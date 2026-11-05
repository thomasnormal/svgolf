# Tools: what is installed, what is missing, how to get it

Inventory taken 10/30 on the development machine (Apple M2 Pro, 12 cores, 16 GB RAM, macOS, 94 GB free of
926 GB). Nothing was installed or built for this study; the only download was one 6.7 MB liberty file
(`spike/fetch_lib.py`, sha256-pinned). Sizes below come from release metadata (GitHub / Docker Hub / Anaconda
APIs, fetched 10/30). Anything marked *estimate* is mine and was not measured.

## 1. Installed (verified by running it)

| tool | version | used for |
|---|---|---|
| Yosys | 0.53 (Homebrew; `53c22ab7c0`) | the pinned flow; `abc -liberty/-D/-constr`, `stat -liberty`, `ltp`, `synth_ice40`, `synth_ecp5`, `synth_xilinx`, `read_liberty`, `dfflibmap` are all present |
| ABC (`yosys-abc`) | 1.01 (built 2025-05-06) | `&nf` liberty mapping, `buffer/upsize/dnsize`, `stime -p` (ABC's own STA) |
| Verilator | 5.042 | postsynth netlist simulation (existing checker) |
| Icarus Verilog | 12.0 | event-driven 4-state simulation (not used by the checker any more) |
| ngspice | 47 | SPICE (no transistor models on the machine; not used) |
| sv2v, z3, boolector, gtkwave, vcdvcd | present | not needed |
| Python | 3.12.8; pyslang 11.0.0, numpy 1.26.4, scipy 1.15.2, networkx 3.2.1, pandas, cocotb 2.0.1 | the scorer, the spike (the spike uses the standard library only; pyslang for the source gate) |
| conda 24.11, Homebrew 7.0, cmake 4.4.5, bison 3.8.2, flex 2.6.4, eigen 5.0.1, tcl-tk 9.1 (+ tcl-tk@8), boost 1.92 | present | would be the dependencies of an OpenSTA build |
| Docker CLI 24.0.6 | present, **daemon not running** (Docker Desktop context `desktop-linux`) | would host the ORFS image |

Two measured facts about the installed Yosys that matter for the plan:

* **`sta` is useless on the scored netlist.** Yosys `sta` needs timing arcs on the cells (specify blocks); the
  `$_AND_`... cells have none: `Warning: Module '\$_AND_' has no timing arcs! ... No timing paths found.` (run on
  the Sklansky netlist). `ltp` is a unit-delay topological depth, nothing more. So "a pinned static timing
  pass" cannot be Yosys `sta` unless cells with arcs are supplied; the usable pieces are ABC's `stime`
  (printed in the Yosys log of an `abc -liberty -constr` run) and a separate STA.
* **`abc -liberty` works end to end** (mapped netlist of Nangate45 cells, `stat -liberty` area in um^2). `-D` is
  honoured only together with `-constr` (which switches on `buffer; upsize; dnsize; stime -p`); without `-constr`
  ABC runs `&nf` (delay-oriented mapping with area recovery) and the `-D` value changes nothing
  (measured: identical netlists for D = 0, 300, 2000).

## 2. Missing, and how each could be obtained

macOS arm64 is the machine in front of us; Linux x86-64 is what a CI host and most contestants have.

| tool | needed by | macOS arm64 | Linux | download / disk | build / run time |
|---|---|---|---|---|---|
| **OpenSTA** (GPL-3.0, dual-licensed with a commercial licence) | flow B, flow D | no Homebrew formula, no conda-forge/litex-hub package. **Build from source** (CMake; needs Eigen, **CUDD**, Tcl 8.6, SWIG 4.1, Bison, Flex; the README says Xcode's Tcl/Flex/Bison cannot be used, tested on macOS 14.5). Homebrew has all of them except CUDD (build it separately). Docker image from the repo's Dockerfiles (Ubuntu) | same build; Guix has a package; Docker | source repo ~134 MB with history (GitHub API), binary a few tens of MB (*estimate*) | build 3 to 10 minutes on 12 cores (*estimate*); one STA run on a 2000-gate netlist well under a second (*estimate*). Reads Liberty, SDC, SPEF, VCD, SAIF |
| **OpenROAD** (BSD-3) | flow D (floorplan, place, CTS, route, RCX) | **no binary for macOS**; GitHub has no release (last tag 2020); the prebuilt `.deb` (Precision Innovations "VaultLink") is Ubuntu 22.04/24.04 only; conda `litex-hub::openroad` exists for `osx-64` only (20.8 MB, Intel build, a `2.0_9990_...` version string, runs under Rosetta; the channel is community-maintained). Source build now goes through Bazel (`bazelisk`, `./etc/DependencyInstaller.sh -no-gui`); the docs state no time, size or Apple Silicon support. Nix route via LibreLane (below) | `.deb`; Docker `openroad/orfs` | Docker Hub: `openroad/orfs:latest` is **linux/amd64 only**, 1.56 GB compressed (the arm64 tag is from 2024-12); source build several GB of Bazel cache (*estimate*) | source build 30 to 90 minutes on this machine (*estimate*); a full ORFS run on a 2000-gate Nangate45 block is a minute or two on native x86 (*estimate*, from the size of ORFS' own `gcd` example), 2 to 5 times that under amd64 emulation (*estimate*) |
| **ORFS / OpenLane / LibreLane** | flow D | LibreLane: Nix (macOS and Linux, x86-64 and aarch64; first `nix-shell` about 10 minutes from the FOSSi binary cache, per its docs) or Docker. ORFS itself: clone the repo (its `flow/platforms/` hold the PDKs) and point it at an OpenROAD + Yosys + KLayout (`brew install --cask klayout` 0.30.12 exists). pip install of LibreLane is "bring your own tools" | same, plus the `.deb` | Nix store: several GB (*estimate*); Docker 1.6 GB compressed | the Nix route is the only one with aarch64 binaries for the whole stack; **Nix is not installed here** |
| **nextpnr-ice40** | flow C | Homebrew bottle `nextpnr-ice40` 0.11.1 (arm64) + `icestorm` 1.1 (deps boost, eigen, libftdi, libusb). **No `nextpnr-ecp5` formula** (`prjtrellis` 1.4 exists; no ECP5 PnR). conda `litex-hub::nextpnr-ice40` is `osx-64`, 58.7 MB, old (`0.0.0_2979`) | distro packages; OSS CAD Suite | brew: boost + eigen + python are the big dependencies (tens of MB each) | PnR of a 700-LUT4 design: seconds (*estimate*); chipdb generation if built from source is the slow step (*estimate*: minutes) |
| **OSS CAD Suite** (YosysHQ, dated nightly archives) | A, C (one archive for everything open-source except OpenSTA/OpenROAD) | `oss-cad-suite-darwin-arm64-<yyyymmdd>.tgz`, **525 MB** (20261030 build); contents per the project page: Yosys, ABC, nextpnr (generic, ice40, ecp5, machxo2, nexus, gowin), IceStorm/Trellis/Oxide/Apicula, Verilator, Icarus, GHDL (darwin-arm64 and linux-x64), sby/eqy, Z3 and other solvers, GTKWave, cocotb. **No OpenSTA, no OpenROAD** | `linux-x64` 748 MB, `linux-arm64` 686 MB | unpacked size not measured | no build; unpack and put `bin/` first on `PATH` |
| **Icarus**, **Verilator** | already installed | present | present | | |
| **A liberty file** | A, B, D | fetched by `spike/fetch_lib.py`: 6.7 MB, pinned by commit and sha256 | same | | |

Python wheels: none of OpenSTA, OpenROAD or nextpnr is available as a pip wheel in a form this project could
pin (LibreLane's own pip package needs the tools provided separately). `pyosys` is Yosys' Python binding, not
needed here.

## 3. What this means for contestants and CI

* **Flow A needs nothing new**: Yosys and ABC are already required; the liberty file is one 6.7 MB fetch at a
  pinned hash (or a generated 136 kB subset, `spike/mklib8.py`); the STA and the simulator are pure Python
  (the spike's `engine.py`, 400 lines, standard library only).
* **Flow B (OpenSTA)** is a Linux/CI cross-check, not something to require from contestants: no binary exists
  for macOS, the build has a non-brew dependency (CUDD), and the Python STA was measured to agree with ABC's
  own STA to 1.3% on average (`spike/README.md`).
* **Flow C (nextpnr)** is reachable on macOS through Homebrew (iCE40 only) or the 525 MB OSS CAD Suite archive
  (iCE40 and ECP5, pinned by date). One archive also pins Yosys, ABC, Verilator and Icarus, which the present
  checker already reads from `PATH`: pinning them by archive date would replace today's "Yosys 0.53 from
  Homebrew" with a hashable artifact. (The pinned flow records the Yosys version; a different Yosys is a new
  flow and re-issues records, by the existing policy.)
* **Flow D (ORFS)** on this machine means Docker with amd64 emulation (daemon not running; Docker Desktop
  must be started and given enough of the 16 GB), or Nix. It is a maintainers' CI job on a Linux host.
