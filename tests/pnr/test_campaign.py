"""Tests of score/pnr/campaign/ (a round's place and route in three commands, decided 2026-11-27): what prepare.py
lists as waiting, the chroot form host.py gives the in-tree container commands, what host.py packs and what finish.py
unpacks and counts as a valid run. Offline: no Yosys, no image, no course host (the real runs are measured in
score/pnr/README.md, "A round's runs, in one sequence").

    python3.12 tests/pnr/test_campaign.py
"""
import io
import json
import os
import shutil
import sys
import tarfile
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "score", "pnr", "campaign"))
sys.path.insert(0, os.path.join(SVGOLF, "score", "pnr"))
import finish  # noqa: E402
import host  # noqa: E402
import pnr  # noqa: E402
import prepare  # noqa: E402
import run_job  # noqa: E402

EXJOB_DIR = os.path.join(HERE, "fixtures", "example_job")
EXJOB = "_example_38596d52847c__min_s1"


class PrepareTest(unittest.TestCase):
    def test_nothing_waits_on_the_committed_tables(self):
        """Since 2026-11-27 every design the tasks show is routed or shares a run: nothing waits, nothing lacks a
        request (this changes when a round adds a design, until it is routed)."""
        rows, none = prepare.waiting()
        self.assertEqual((rows, none), ([], []))


class ChrootTest(unittest.TestCase):
    def test_the_same_mounts_environment_and_command(self):
        """The chroot form of run_job.py's `run` command: the pinned memory cap and no swap, nice 19, the CPU set, the
        container command's mounts (read-only ones marked), environment, working directory and command, nothing
        else."""
        pins = pnr.load_pins()
        cmd = run_job.run_command(EXJOB_DIR, EXJOB, pins, cpuset="8-9")
        mounts, env, workdir, argv = host.parse_container_command(cmd)
        self.assertEqual(workdir, pnr.FLOW_DIR)
        self.assertIn(f"make DESIGN_CONFIG=/work/cfg/{EXJOB}.mk", argv[-1])
        full = host.chroot_command(cmd, "/ROOT", "/SKEL", pins, "8-9")
        cap = int(pins["memory_cap_gb"])
        self.assertEqual(full[:15], ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={cap}G", "-p",
                                     "MemorySwapMax=0", "nice", "-n", "19", "taskset", "-c", "8-9", "unshare"])
        i = full.index("chroot-mounts")
        self.assertEqual(full[i + 1:i + 3], ["/ROOT", "/SKEL"])
        j = full.index("--")
        triples = [tuple(full[k:k + 3]) for k in range(i + 3, j, 3)]
        self.assertEqual(triples, [(os.path.abspath(h), d, "ro" if ro else "rw") for h, d, ro in mounts])
        self.assertIn(("/work/designs", "ro"), [(d, m) for _h, d, m in triples])
        self.assertIn(("/work/run", "rw"), [(d, m) for _h, d, m in triples])
        inner = full[j + 1:]
        self.assertEqual(inner[:3], ["/usr/bin/env", "-i", f"PATH={host.IMAGE_PATH}"])
        self.assertEqual(inner[3:3 + len(env)], env)
        self.assertEqual(inner[-len(argv):], argv)
        self.assertEqual(inner[-len(argv) - 1], workdir)


class PackTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="campaign-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)

    def put(self, rel, text="x"):
        p = os.path.join(self.tmp, *rel.split("/"))
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(text)

    def test_pack_takes_what_finish_reads_and_no_database(self):
        res = "job/run/results/asap7/n/min_s1/"
        for rel in ("job/rows/J.json", "job/logs/status.txt", "job/img/J.png", "job/lec/J.yml", "job/cfg/J.mk",
                    "job/sdc/n.sdc", "job/designs/n.v", "job/jobs/J.json", res + "6_final_lec.v", res + "6_final.odb",
                    res + "6_final.def", "job/run/objects/asap7/n/min_s1/6_final_lec_test.yml",
                    "job/run/objects/asap7/n/min_s1/other.tcl", "job/run/logs/asap7/n/min_s1/2_1_floorplan.log",
                    "job/run/reports/asap7/n/min_s1/6_finish.rpt", "logs/runner.log", "job/tmp/J/x"):
            self.put(rel)
        with open(os.devnull, "w") as quiet:
            old, sys.stdout = sys.stdout, quiet
            try:
                host.cmd_pack(type("A", (), {"round": self.tmp})())
            finally:
                sys.stdout = old
        with tarfile.open(os.path.join(self.tmp, "back.tar")) as tar:
            names = set(tar.getnames())
        self.assertIn(res + "6_final_lec.v", names)
        self.assertIn("job/run/objects/asap7/n/min_s1/6_final_lec_test.yml", names)
        self.assertIn("job/run/logs/asap7/n/min_s1/2_1_floorplan.log", names)
        self.assertIn("logs/runner.log", names)
        for gone in (res + "6_final.odb", res + "6_final.def", "job/run/objects/asap7/n/min_s1/other.tcl", "job/tmp/J/x"):
            self.assertNotIn(gone, names)
        dst = finish.unpack(self.tmp)
        self.assertTrue(os.path.isfile(os.path.join(dst, "rows", "J.json")))

    def test_unpack_refuses_what_is_not_a_file_of_the_round(self):
        for name, kind in (("../x", tarfile.REGTYPE), ("/etc/x", tarfile.REGTYPE), ("other/x", tarfile.REGTYPE),
                           ("job/link", tarfile.SYMTYPE)):
            with self.subTest(name):
                with tarfile.open(os.path.join(self.tmp, "back.tar"), "w") as tar:
                    info = tarfile.TarInfo(name)
                    info.type = kind
                    if kind == tarfile.SYMTYPE:
                        info.linkname = "/etc/passwd"
                    tar.addfile(info, io.BytesIO(b""))
                with self.assertRaises(ValueError):
                    finish.unpack(self.tmp)


class ValidityTest(unittest.TestCase):
    def test_the_rule_on_a_row(self):
        with open(os.path.join(EXJOB_DIR, "rows", EXJOB + ".json"), encoding="utf-8") as fh:
            row = json.load(fh)
        self.assertEqual(finish.row_validity(row), (True, None))
        for name, change in (("exit", {"rc": 2}), ("DRC", {"drc": 3}), ("the flow's check", {"lec": ["6_final:DIFFERENT"]}),
                             ("no flow check", {"lec": []}),
                             ("the reference check", {"lec_reference": dict(row["lec_reference"], verdict="DIFFERENT")}),
                             ("status", {"status": "failed"})):
            with self.subTest(name):
                valid, why = finish.row_validity(dict(row, **change))
                self.assertFalse(valid)
                self.assertTrue(why)


if __name__ == "__main__":
    unittest.main(verbosity=2)
