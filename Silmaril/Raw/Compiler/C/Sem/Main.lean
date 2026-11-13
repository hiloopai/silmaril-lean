module

public import Silmaril.Compiler.C.Sem.C7.Defs
public import Silmaril.Compiler.C.Sem.ValidatorC6.Defs
public import Silmaril.Compiler.C.Sem.ValidatorC7.Defs
public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.C.Sem.RenameDefs.Defs
public import Silmaril.Cerberus.Ail.Codec.Defs
@[expose] public section

/-!
# `csem`: run the C semantics on typed Ail

```
csem check FILE.tail.sexp           -- the top rung whose fragment holds the program (exit 0), or 3
csem run [--fuel N] FILE.tail.sexp  -- run it under that rung, as a process
csem c0 [--fuel N] FILE.tail.sexp   -- run it under C0, as a process
csem c1 [--fuel N] FILE.tail.sexp   -- run it under C1, as a process
csem c2 [--fuel N] FILE.tail.sexp   -- run it under C2, as a process
csem c3 [--fuel N] FILE.tail.sexp   -- run it under C3, as a process
csem c4 [--fuel N] FILE.tail.sexp   -- run it under C4, as a process
csem c5 [--fuel N] FILE.tail.sexp   -- run it under C5, as a process
csem c6 [--fuel N] FILE.tail.sexp   -- run it under C6, as a process
csem c7 [--fuel N] FILE.tail.sexp   -- run it under C7, as a process
csem tv FILE.tail.sexp              -- `tv=1` if `checkC0` accepts it, `tv1=1` if `checkC1` does,
                                    -- `core=1` if `elabC0` elaborates it
csem why FILE.tail.sexp             -- why `checkC0` rejects it (diagnostics)
csem why-rt FILE.tail.sexp          -- alias of `why` (runtime-linked ccomp)
csem why1 FILE.tail.sexp            -- why `checkC1` rejects it (diagnostics)
csem tv2 FILE.tail.sexp             -- `tv2=1` if `checkC2` accepts it
csem why2 FILE.tail.sexp            -- why `checkC2` rejects it (diagnostics)
csem tv3 FILE.tail.sexp             -- `tv3=1` if `checkC3` accepts it
csem why3 FILE.tail.sexp            -- why `checkC3` rejects it (diagnostics)
csem tv4 FILE.tail.sexp             -- `tv4=1` if `checkC4` accepts it
csem why4 FILE.tail.sexp            -- why `checkC4` rejects it (diagnostics)
csem tv5 FILE.tail.sexp             -- `tv5=1` if `checkC5` accepts it
csem why5 FILE.tail.sexp            -- why `checkC5` rejects it (diagnostics)
csem tv6 FILE.tail.sexp             -- `tv6=1` if `checkC6` accepts it
csem why6 FILE.tail.sexp            -- why `checkC6` rejects it (diagnostics)
csem tv7 FILE.tail.sexp             -- `tv7=1` if `checkC7` accepts it
csem why7 FILE.tail.sexp            -- why `checkC7` rejects it (diagnostics)
csem rename-stats FILE.tail.sexp    -- over ccomp's Lir (`ccompLir`): `rename_ok` functions the
                                    -- renamer checker accepts, `rename_total` functions,
                                    -- `entry_ok` functions whose entry label names a block
```

`check` prints the first accepting rung (C1 → C2 → C3 → C4 → C5 → C6 → C7 → C0), and `run`
dispatches to it. The campaign's `c_agree` counts `csem run`.

`FILE.tail.sexp` is a typed-Ail document (`cerb-oracle --level tail`, or ccomp's Ail cache).
`csem c0` (and `c1`, `c2`, `c3`, `c4`, `c5`, `c6`, `c7`, `run`) writes the program's standard output and exits as the process would: with the exit
status, or `128 + n` after signal `n` (`134` after `abort()`). Other results: `125` undefined
behaviour (the reason on stderr), `124` out of fuel, `3` outside the fragment, `2` a bad
document.
-/

namespace Silmaril.Compile.C.Sem.Main

open Silmaril.Cerberus.Ail.Codec

def load (path : String) : IO (Except String Silmaril.Cerberus.Ail.TypedProgram) := do
  match readTailDocument (← IO.FS.readFile path) with
  | .error e => return .error s!"not a typed-Ail document: {e}"
  | .ok (.reject _ _ stage _ msg) => return .error s!"rejected by Cerberus ({stage}): {msg}"
  | .ok (.document _ _ p) => return .ok p

/-- Write a run's output and return its exit code (see above). -/
def report (rung : String) : C0.Result → IO UInt32
  | .done o => do
    let out ← IO.getStdout
    out.write (ByteArray.mk o.stdout.toArray)
    out.flush
    match o.exit with
    | .status n => return n.toUInt32
    | .signal n => IO.eprintln s!"csem: signal {n}"; return (128 + n).toUInt32
    | .diverges => return 124
  | .undefined why => do IO.eprintln s!"csem: undefined behaviour: {why}"; return 125
  | .outOfFuel => do IO.eprintln "csem: out of fuel"; return 124
  | .unsupported why => do IO.eprintln s!"csem: outside {rung}: {why}"; return 3

/-- The top rung whose fragment holds the program, or why none does. -/
def rung (p : Silmaril.Cerberus.Ail.TypedProgram) : Except String String :=
  match C1.check p with
  | .ok () => .ok "C1"
  | .error _ => match C2.check p with
    | .ok () => .ok "C2"
    | .error _ => match C3.check p with
      | .ok () => .ok "C3"
      | .error _ => match C4.check p with
        | .ok () => .ok "C4"
        | .error _ => match C5.check p with
          | .ok () => .ok "C5"
          | .error _ => match C6.check p with
            | .ok () => .ok "C6"
            | .error _ => match C7.check p with
              | .ok () => .ok "C7"
              | .error why => match C0.check p with
                | .ok () => .ok "C0"
                | .error _ => .error why

def main (args : List String) : IO UInt32 := do
  let (fuel, args) := match args with
    | cmd :: "--fuel" :: n :: rest => (n.toNat?.getD 100000000, cmd :: rest)
    | _ => (100000000, args)
  match args with
  | ["check", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      match rung p with
      | .ok r => IO.println r; return 0
      | .error why => IO.println s!"outside C7: {why}"; return 3
  | ["tv", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv := if checkC0 p then 1 else 0
      let tv1 := if checkC1 p then 1 else 0
      let core := if (elabC0 p).isSome then 1 else 0
      IO.println s!"tv={tv} tv1={tv1} core={core}"; return 0
  | ["tv2", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv2 := if checkC2 p then 1 else 0
      IO.println s!"tv2={tv2}"; return 0
  | ["why2", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC2Why tvLirFuel tvC2Fuel p).getD "accepted"); return 0
  | ["tv3", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv3 := if checkC3 p then 1 else 0
      IO.println s!"tv3={tv3}"; return 0
  | ["why3", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC3Why tvLirFuel tvC3Fuel p).getD "accepted"); return 0
  | ["tv4", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv4 := if checkC4 p then 1 else 0
      IO.println s!"tv4={tv4}"; return 0
  | ["why4", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC4Why tvLirFuel tvC4Fuel p).getD "accepted"); return 0
  | ["tv5", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv5 := if checkC5 p then 1 else 0
      IO.println s!"tv5={tv5}"; return 0
  | ["why5", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC5Why tvLirFuel tvC5Fuel p).getD "accepted"); return 0
  | ["tv6", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv6 := if checkC6 p then 1 else 0
      IO.println s!"tv6={tv6}"; return 0
  | ["why6", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC6Why tvLirFuel tvC6Fuel p).getD "accepted"); return 0
  | ["tv7", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let tv7 := if checkC7 p then 1 else 0
      IO.println s!"tv7={tv7}"; return 0
  | ["why7", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC7Why tvLirFuel tvC7Fuel p).getD "accepted"); return 0
  | ["rename-stats", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      let (ok, total) := renumberCheckedStats p
      let entryOk := match ccompLir p with
        | some q => (q.funcs.filter fun (fn : Silmaril.Machine.Lir.Func Nat) => fn.entry < fn.blocks.length).length
        | none => 0
      IO.println s!"rename_ok={ok} rename_total={total} entry_ok={entryOk}"; return 0
  | ["why", path] | ["why-rt", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC0Why tvLirFuel tvC0Fuel p).getD "accepted"); return 0
  | ["why1", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      IO.println ((checkC1Why tvLirFuel tvC1Fuel p).getD "accepted"); return 0
  | ["c0", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C0.check p then
        IO.eprintln s!"csem: outside C0: {why}"; return 3
      report "C0" (C0.run fuel p)
  | ["c1", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C1.check p then
        IO.eprintln s!"csem: outside C1: {why}"; return 3
      report "C1" (C1.run fuel p)
  | ["c2", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C2.check p then
        IO.eprintln s!"csem: outside C2: {why}"; return 3
      report "C2" (C2.run fuel p)
  | ["c3", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C3.check p then
        IO.eprintln s!"csem: outside C3: {why}"; return 3
      report "C3" (C3.run fuel p)
  | ["c4", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C4.check p then
        IO.eprintln s!"csem: outside C4: {why}"; return 3
      report "C4" (C4.run fuel p)
  | ["c5", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C5.check p then
        IO.eprintln s!"csem: outside C5: {why}"; return 3
      report "C5" (C5.run fuel p)
  | ["c6", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C6.check p then
        IO.eprintln s!"csem: outside C6: {why}"; return 3
      report "C6" (C6.run fuel p)
  | ["c7", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      if let .error why := C7.check p then
        IO.eprintln s!"csem: outside C7: {why}"; return 3
      report "C7" (C7.run fuel p)
  | ["run", path] =>
    match ← load path with
    | .error e => IO.eprintln s!"csem: {path}: {e}"; return 2
    | .ok p =>
      match rung p with
      | .ok "C1" => report "C1" (C1.run fuel p)
      | .ok "C2" => report "C2" (C2.run fuel p)
      | .ok "C3" => report "C3" (C3.run fuel p)
      | .ok "C4" => report "C4" (C4.run fuel p)
      | .ok "C5" => report "C5" (C5.run fuel p)
      | .ok "C6" => report "C6" (C6.run fuel p)
      | .ok "C7" => report "C7" (C7.run fuel p)
      | .ok _ => report "C0" (C0.run fuel p)
      | .error why => IO.eprintln s!"csem: outside C7: {why}"; return 3
  | _ => IO.eprintln "usage: csem check FILE | csem run|c0|c1|c2|c3|c4|c5|c6|c7 [--fuel N] FILE | csem tv|tv2|tv3|tv4|tv5|tv6|tv7|why|why-rt|why1|why2|why3|why4|why5|why6|why7|rename-stats FILE"; return 2

end Silmaril.Compile.C.Sem.Main
