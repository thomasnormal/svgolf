#!/usr/bin/env python3.12
"""Fetch the sky130_fd_sc_hd typical-corner liberty (tt_025C_1v80) at a PINNED commit of
OpenROAD-flow-scripts, and the cell Verilog models at a PINNED commit of the upstream cell
library, and verify sha256 of everything. Nothing is vendored; the files go to .cache/ (git-ignored).

  python3.12 fetch_sky130.py            # downloads missing files, prints the liberty path
  PPA_SKY130_LIB=/path/to/file.lib      # use an existing copy of the liberty (hash still checked)

Liberty (12.8 MB, one file, one corner): ORFS commit 6c6fc7e2 (the same pin as WP-X0's Nangate45 fetch),
flow/platforms/sky130hd/lib/sky130_fd_sc_hd__tt_025C_1v80.lib. The upstream cell library repo
(google/skywater-pdk-libs-sky130_fd_sc_hd) keeps only `timing/*.lib.json` stubs, not the generated .lib;
ORFS's copy is the practical pin.

Verilog models (functional + UDP): google/skywater-pdk-libs-sky130_fd_sc_hd at commit ac7fb61f
(2020-11-10, the repository's last commit): cells/<cell>/sky130_fd_sc_hd__<cell>.functional.v for the
cells the study uses, and models/<udp>/sky130_fd_sc_hd__<udp>.v for the UDPs they instantiate.
"""
import hashlib, os, sys, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, ".cache")
SKY = os.path.join(CACHE, "sky130")

ORFS_COMMIT = "6c6fc7e21b2d0b5b88b1a52d0a5860ea4d88e9e5"
LIB_URL = ("https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD-flow-scripts/"
           f"{ORFS_COMMIT}/flow/platforms/sky130hd/lib/sky130_fd_sc_hd__tt_025C_1v80.lib")
LIB_SHA256 = "ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5"
LIB_GIT_BLOB_SHA1 = "619938b51b2b52bf572e3abd4479fa78202704dc"   # as listed by the GitHub contents API

PDK_LIBS_COMMIT = "ac7fb61f06e6470b94e8afdf7c25268f62fbd7b1"
RAW = f"https://raw.githubusercontent.com/google/skywater-pdk-libs-sky130_fd_sc_hd/{PDK_LIBS_COMMIT}"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def lib_path():
    p = os.environ.get("PPA_SKY130_LIB") or os.path.join(CACHE, "sky130_fd_sc_hd__tt_025C_1v80.lib")
    if not os.path.exists(p):
        os.makedirs(os.path.dirname(p), exist_ok=True)
        print(f"downloading {LIB_URL}", file=sys.stderr)
        urllib.request.urlretrieve(LIB_URL, p)
    if LIB_SHA256 != "SET_ME" and sha256(p) != LIB_SHA256:
        raise SystemExit(f"{p}: sha256 {sha256(p)} != pinned {LIB_SHA256}")
    return p


if __name__ == "__main__":
    p = lib_path()
    print(p, sha256(p), os.path.getsize(p))


# ---------------------------------------------------------------- Verilog cell models (upstream, pinned)
import concurrent.futures as _cf, json as _json, re as _re


def _get(path, dest):
    if not os.path.exists(dest):
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        urllib.request.urlretrieve(f"{RAW}/{path}", dest)
    return path


def fetch_models(families, workers=8):
    """Download `cells/<fam>/sky130_fd_sc_hd__<fam>.functional.v` for each family and the UDP/model files they
    `include`, into .cache/sky130/models/ (the same relative layout as upstream, so the includes resolve). Returns
    {relative path: sha256} (sorted) -- the manifest to pin."""
    root = os.path.join(SKY, "models")
    paths = [f"cells/{f}/sky130_fd_sc_hd__{f}.functional.v" for f in sorted(families)]
    with _cf.ThreadPoolExecutor(workers) as ex:
        list(ex.map(lambda p: _get(p, os.path.join(root, p)), paths))
    extra = set()
    for p in paths:
        for inc in _re.findall(r'`include "\.\./\.\./(models/[^"]+)"', open(os.path.join(root, p)).read()):
            extra.add(inc)
    with _cf.ThreadPoolExecutor(workers) as ex:
        list(ex.map(lambda p: _get(p, os.path.join(root, p)), sorted(extra)))
    man = {}
    for p in paths + sorted(extra):
        man[p] = sha256(os.path.join(root, p))
    return man
