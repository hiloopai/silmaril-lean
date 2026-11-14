import Lean.Data.Json
import Silmaril.Wasm.Component.Conformance.Run.Defs
import Silmaril.Wasm.Component.Conformance.Extra.Defs
import Silmaril.Wasm.Component.Conformance.Explore.Defs
import Silmaril.Wasm.Component.Conformance.DecodeGC.Defs

/-!
# `component-wast`: component `.wast` scripts on the reference machine

Reads the JSON form of a `.wast` script (`wasm-tools json-from-wast`, the `wast2json` format:
one object per command, binaries in files next to the JSON) and runs it on the copied
component-model reference machine through `Silmaril.Wasm.Component.Conformance`: decode
(`decodeGC`: `decodeP3`, the binary track's verified `BinaryP3` grammar with silmaril-lean's
core decoder, and where it fails `BinaryGC`, with WebAssembly 3.0 core types and the 🛸 GC
options; every binary `decodeP3` reads is compared with the `BinaryGC` path, `GC-DISAGREE`;
An earlier step retired the pass-1 decoder after proving that it agrees with `decodeP3` on every
binary, `Conformance.DecodeAgree.decode_iff`), validate (`checkCore3?` at
`Conformance.features`, then the rules of `Conformance.Extra` the copied validator lacks),
instantiate with the root arguments of wasmtime's `.wast` host
(`Conformance.Host`: its `host`, `wasmtime` and root functions, and the named instances
registered so far) and invoke over `core3 neverFail`.

```text
component-wast SCRIPT.json [--fuel N] [--oracle first|eager|all] [--budget N]
```

One line per command, `line<TAB>command<TAB>verdict<TAB>detail`, then
`SUMMARY<TAB>pass=…<TAB>weak=…<TAB>valid=…<TAB>fail=…<TAB>unsupported=…<TAB>skip=…`. Verdicts:

* `PASS`: the reference machine did what the script says;
* `FAIL`: it did something else (a bug in the semantics, in the runner, or in the test);
* `UNSUP <class>`: the command needs something outside the runner or the model: `decode`
  (the decoder rejects a binary the script calls valid), `core-module` (a top-level core module), `model-fault` (the
  machine reports an `internal` fault: an unmodelled feature), `value` (a value the runner
  cannot read), `no-instance` (an earlier command it depends on did not produce an
  instance), `after-trap` (an `assert_return` on an instance whose store an earlier trap
  locked down: REF admits no entry after a trap, so this only follows an earlier `FAIL`),
  `after-stuck` (the instance's previous call did not finish); an `assert_trap` on a
  locked-down store passes when it expects "cannot enter component instance" (wasmtime's
  poisoned instance) and is `after-trap` otherwise;
* calls run with the deterministic first-alternative oracle (`--oracle eager`: the eager
  oracle `Conformance.eagerOracle`, `nondet` profile, which never blocks on a wait whose
  condition already holds, as wasmtime); when that run is out of fuel the
  call is re-run from the same configuration with the seeded oracles `lcg 1` and `lcg 2`
  (`nondet` profile) and the first run that ends is used (the verdict says so): the
  machine is nondeterministic, and the first-alternative choices can starve a ready thread;
* `--oracle all`: every call runs under every choice of the scheduling and branching choice
  points (`Explore.exploreCall`, scripted oracles in the `nondet` profile, at most `--budget`
  schedules per call, default 64); the first schedule (all first alternatives) gives the
  configuration the script continues from, and a command passes only when every schedule
  passes; a command whose verdict changes with the schedule is counted in `dependent` and
  reported with the script of the first deviating schedule. Instantiation still runs with the
  first-alternative oracle;
* an `assert_trap` passes on any trap; when the copied model's `TrapReason.wasmtimeMessage`
  of the trap reason does not occur in the expected message (`reasonAgrees`), the verdict is
  marked `[reason-differs]` and counted in `reason-differs`;
* a `deadlock` of the machine passes an `assert_trap` whose text mentions a deadlock
  ("deadlock detected", "cannot make further progress"): wasmtime reports deadlocks as
  traps, REF as the `deadlock` outcome;
* `WEAK decoder`: an `assert_invalid` binary the decoder already rejects, so the validator
  is not exercised (correct when the decoder checks the property, vacuous when it lacks the
  construct);
* `VALID`: no longer produced (a component with root imports, never instantiated);
* `SKIP`: text-format `assert_malformed` (the runner reads binaries only).

The JSON is parsed with Lean core's `Lean.Json` (unverified tooling); everything after the
bytes is the verified decoder and the copied reference semantics. The exit status is 0 when
the script ran, whatever the verdicts.
-/

open Lean (Json)
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Conformance.Explore (exploreCall)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

namespace ComponentWast

abbrev WT := WIT.ValType Empty RtId

/-! ## Values -/

def intKind? : WIT.Primitive → Option IntKind
  | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32 | .u64 => some .u64
  | .s8 => some .s8 | .s16 => some .s16 | .s32 => some .s32 | .s64 => some .s64
  | _ => none

def str? (j : Json) : Except String String := j.getStr?

def int? (j : Json) : Except String Int := do
  match j with
  | .str s => match s.toInt? with
    | some n => pure n
    | none => throw s!"not an integer: {s}"
  | .num n => match n.toString.toInt? with
    | some i => pure i
    | none => throw s!"not an integer: {n}"
  | _ => throw "not an integer"

def strVal (s : String) : Val := .string ⟨⟨s, .utf8, s.utf8ByteSize⟩, .i32⟩

def lookupIdx (names : List String) (n : String) : Except String Nat :=
  match names.idxOf? n with
  | some i => pure i
  | none => throw s!"unknown case or label {n}"

/-- Read a JSON value at a WIT type. -/
partial def toVal (t : WT) (j : Json) : Except String Val := do
  let v := j.getObjValD "value"
  match t with
  | .prim .bool => .bool <$> v.getBool?
  | .prim .char =>
    let s ← str? v
    match s.toList with
    | [c] => pure (.char c)
    | _ => throw s!"not a char: {s}"
  | .prim .string => strVal <$> str? v
  | .prim .f32 => do
    let n ← int? v
    if n < 0 then throw "negative f32 bits"
    pure (.f32 (BitVec.ofNat 32 n.toNat))
  | .prim .f64 => do
    let n ← int? v
    if n < 0 then throw "negative f64 bits"
    pure (.f64 (BitVec.ofNat 64 n.toNat))
  | .prim p =>
    match intKind? p with
    | some k => .int k <$> int? v
    | none => throw s!"unsupported value type {reprStr p}"
  | .list u => do
    let xs ← v.getArr?
    .list <$> xs.toList.mapM (toVal u)
  | .fixedList u _ => do
    let xs ← v.getArr?
    .list <$> xs.toList.mapM (toVal u)
  | .tuple ts => do
    let xs ← v.getArr?
    if xs.size ≠ ts.length then throw "tuple arity"
    .record <$> (ts.zip xs.toList).mapM fun (u, x) => toVal u x
  | .record fs => do
    let xs ← v.getArr?
    let named ← xs.toList.mapM fun x => do
      let a ← x.getArr?
      if h : a.size = 2 then pure (← str? a[0], a[1]) else throw "record field"
    .record <$> fs.mapM fun (n, u) => match named.lookup n with
      | some x => toVal u x
      | none => throw s!"missing field {n}"
  | .variant cs => do
    let c ← str? (v.getObjValD "case")
    let i ← lookupIdx (cs.map (·.1)) c
    match cs[i]? with
    | some (_, some u) => (Val.variant i ∘ some) <$> toVal u (v.getObjValD "payload")
    | _ => pure (.variant i none)
  | .enum ls => do
    let i ← lookupIdx ls (← str? v)
    pure (.variant i none)
  | .option u =>
    match v with
    | .null => pure (.variant 0 none)
    | x => (Val.variant 1 ∘ some) <$> toVal u x
  | .result ok err => do
    let (i, x, u) ← match v.getObjVal? "Ok", v.getObjVal? "Err" with
      | .ok x, _ => pure (0, x, ok)
      | _, .ok x => pure (1, x, err)
      | _, _ => throw "result without Ok or Err"
    match u with
    | some u => (Val.variant i ∘ some) <$> toVal u x
    | none => pure (.variant i none)
  | .flags ls => do
    let xs ← v.getArr?
    let set ← xs.toList.mapM str?
    for s in set do
      if !ls.contains s then throw s!"unknown flag {s}"
    pure (.flags (ls.map set.contains))
  | _ => throw "unsupported value type"

/-- Compare a result value with an expected JSON value at a WIT type (strings by content,
ignoring the encoding and source pointer width). -/
partial def valMatches (t : WT) (v : Val) (j : Json) : Except String Bool := do
  match t, v with
  | .prim .string, .string s => pure (s.v.str == (← str? (j.getObjValD "value")))
  | .list u, .list vs | .fixedList u _, .list vs => do
    let xs ← (j.getObjValD "value").getArr?
    if xs.size ≠ vs.length then return false
    (vs.zip xs.toList).allM fun (a, b) => valMatches u a b
  | .tuple ts, .record vs => do
    let xs ← (j.getObjValD "value").getArr?
    if xs.size ≠ vs.length ∨ ts.length ≠ vs.length then return false
    ((ts.zip vs).zip xs.toList).allM fun ((u, a), b) => valMatches u a b
  | .record fs, .record vs => do
    let xs ← (j.getObjValD "value").getArr?
    let named ← xs.toList.mapM fun x => do
      let a ← x.getArr?
      if h : a.size = 2 then pure (← str? a[0], a[1]) else throw "record field"
    if fs.length ≠ vs.length ∨ named.length ≠ fs.length then return false
    (fs.zip vs).allM fun ((n, u), a) => match named.lookup n with
      | some b => valMatches u a b
      | none => pure false
  | .variant cs, .variant i p => do
    let x := j.getObjValD "value"
    let c ← str? (x.getObjValD "case")
    let some (n, u) := cs[i]? | return false
    if n ≠ c then return false
    match u, p with
    | some u, some a => valMatches u a (x.getObjValD "payload")
    | none, none => pure true
    | _, _ => pure false
  | .option u, .variant i p =>
    match j.getObjValD "value", i, p with
    | .null, 0, none => pure true
    | .null, _, _ => pure false
    | x, 1, some a => valMatches u a x
    | _, _, _ => pure false
  | .result ok err, .variant i p => do
    let x := j.getObjValD "value"
    let (b, u) ← match i with
      | 0 => pure (x.getObjValD "Ok", ok)
      | 1 => pure (x.getObjValD "Err", err)
      | _ => return false
    match u, p with
    | some u, some a => valMatches u a b
    | none, none => pure true
    | _, _ => pure false
  | _, _ =>
    match toVal t j with
    | .ok w => pure (Val.beq v w)
    | .error e => throw e

/-! ## The script interpreter -/

structure Inst where
  cfg : Cfg
  exports : List (String × FuncId)
  calls : Nat := 0

structure St where
  fuel : Nat
  /-- The oracle of the first run of each call (`--oracle first|eager`). -/
  eager : Bool := false
  /-- Named component definitions (`(component definition $x …)`) and their types. -/
  defs : List (String × RefComponent × Silmaril.Wasm.Component.Reference.ComponentType) := []
  /-- Named root instances registered in the host namespace (wasmtime's linker). -/
  registered : List (String × HostItem) := []
  /-- Binaries `decodeP3` reads on which the `BinaryGC` path differs (`gcAgrees`). -/
  gcDisagree : Nat := 0
  /-- Component binaries decoded. -/
  decoded : Nat := 0
  /-- Named instances, and the most recent one under `""`. -/
  insts : List (String × Option Inst) := []
  /-- The most recent instance (`none`: the last module command produced none). -/
  current : Option Inst := none
  currentName : Option String := none
  pass : Nat := 0
  fail : Nat := 0
  unsup : Nat := 0
  skip : Nat := 0
  /-- Invalid binaries the decoder rejects before the validator sees them. -/
  weak : Nat := 0
  /-- Components that validate but import something, so are not instantiated. -/
  valid : Nat := 0
  /-- `assert_trap`s that trapped for a reason whose keywords the expected message lacks. -/
  reasonDiffers : Nat := 0
  /-- A remark on the last invoke (the oracle used), appended to the next verdict. -/
  note : String := ""
  /-- Counts of the `UNSUP` classes. -/
  classes : List (String × Nat) := []
  /-- wasmtime's `resource1` destructor counters (`drops`, `last_drop`): state of its linker,
  shared by every store of the script, so carried from store to store. -/
  drops : Nat × Nat := (0, 0)
  /-- `--oracle all`: every call is run under every oracle choice (`Explore.exploreCall`), at
  most `budget` schedules per call. -/
  explore : Bool := false
  budget : Nat := 64
  /-- The other schedules of the last call (`--oracle all`). -/
  alts : List Explore.Run := []
  /-- Calls explored, schedules run, calls whose enumeration hit the budget, and commands
  whose verdict depends on the schedule. -/
  explored : Nat := 0
  schedules : Nat := 0
  partialCalls : Nat := 0
  dependent : Nat := 0

abbrev M := StateT St IO

def bump (cls : String) (xs : List (String × Nat)) : List (String × Nat) :=
  match xs.lookup cls with
  | some n => (cls, n + 1) :: xs.filter (·.1 != cls)
  | none => xs ++ [(cls, 1)]

def clean (s : String) : String :=
  let s := s.replace "\n" " " |>.replace "\t" " "
    |>.replace "Silmaril.Wasm.Component.Value.Val." "" |>.replace "Silmaril.Wasm.Component.Value." ""
    |>.replace "Silmaril.Wasm.Component." ""
  if s.length > 400 then (s.take 400).toString ++ "…" else s

def report (line : Nat) (cmd verdict detail : String) : M Unit := do
  let note := (← get).note
  modify fun s => { s with note := "" }
  IO.println s!"{line}\t{cmd}\t{verdict}\t{clean (detail ++ note)}"
  (← IO.getStdout).flush
  let (word, cls) := match verdict.splitOn " " with
    | [w, c] => (w, c)
    | _ => (verdict, "")
  modify fun s =>
    if word == "PASS" then { s with pass := s.pass + 1 }
    else if word == "FAIL" then { s with fail := s.fail + 1 }
    else if word == "SKIP" then { s with skip := s.skip + 1 }
    else if word == "WEAK" then { s with weak := s.weak + 1 }
    else if word == "VALID" then { s with valid := s.valid + 1 }
    else { s with unsup := s.unsup + 1, classes := bump cls s.classes }

def isCoreModule (bs : ByteArray) : Bool :=
  bs.size ≥ 8 && bs[4]! == 1 && bs[5]! == 0 && bs[6]! == 0 && bs[7]! == 0

/-- How reading a binary went. -/
inductive Load where
  | ok (c : RefComponent) (ct : Silmaril.Wasm.Component.Reference.ComponentType)
  | core
  | decode (msg : String)
  | invalid (msg : String)

def load (dir : System.FilePath) (file : String) : M Load := do
  let bs ← IO.FS.readBinFile (dir / file)
  if isCoreModule bs then return .core
  modify fun s => { s with decoded := s.decoded + 1 }
  if !gcAgrees bs then
    modify fun s => { s with gcDisagree := s.gcDisagree + 1 }
    IO.println s!"GC-DISAGREE\t{file}\tBinaryGC and decodeP3 differ"
  match decodeGC bs with
  | .error e => return .decode e
  | .ok c =>
    match Extra.validateFull c with
    | .error e => return .invalid e
    | .ok ct => return .ok c ct

def importNames (ct : Silmaril.Wasm.Component.Reference.ComponentType) : List String := ct.imports.map (·.1)

def trapStr : Option TrapReason → String
  | some r => reprStr r
  | none => "trap"

def contains (s t : String) : Bool := (s.splitOn t).length > 1

/-- Does the trap reason agree with the expected message? The copied model's own
`TrapReason.wasmtimeMessage` (wasmtime `a7b4f29`'s message, or a descriptive string) occurs in
it; a core trap agrees with wasmtime's core-trap messages. A heuristic: wasmtime 50's
messages are not guaranteed to be `a7b4f29`'s. -/
def reasonAgrees (r : Option TrapReason) (text : String) : Bool :=
  match r with
  | none => false
  | some r =>
    let t := text.toLower
    contains t r.wasmtimeMessage.toLower ||
      match r with
      | .coreTrap => ["unreachable", "exception", "out of bounds", "integer", "divide",
          "unaligned", "indirect call", "null", "wasm trap"].any (contains t)
      | _ => false

/-- Instantiate and record the instance (under `name` when given, also registering its core
modules and resources in the host namespace, as wasmtime's `WastContext::module`). -/
def instantiateCmd (line : Nat) (cmd : String) (c : RefComponent)
    (ct : Silmaril.Wasm.Component.Reference.ComponentType) (name : Option String) : M Unit := do
  let fuel := (← get).fuel
  let res := instantiate fuel (← get).registered c ct (← get).drops
  let inst? : Option Inst := match res with
    | .instance m es _ => some { cfg := m, exports := es }
    | _ => none
  match res with
  | .instance m _ _ => modify fun s => { s with drops := (m.host.drops, m.host.lastDrop) }
  | _ => pure ()
  match res, name with
  | .instance _ _ items, some n =>
    modify fun s => { s with registered :=
      (n, .inst (registerItems n items)) :: s.registered.filter (·.1 != n) }
  | _, _ => pure ()
  let put (xs : List (String × Option Inst)) : List (String × Option Inst) :=
    match name with
    | some n => (n, inst?) :: xs.filter (·.1 != n)
    | none => xs
  modify fun s => { s with current := inst?, currentName := name, insts := put s.insts }
  match res with
  | .instance _ es _ => report line cmd "PASS" s!"exports {es.map (·.1)}"
  | .trap r => report line cmd "FAIL" s!"instantiation trapped: {trapStr r}"
  | .stuck why =>
    if why.startsWith "internal fault" then report line cmd "UNSUP model-fault" why
    else report line cmd "FAIL" s!"instantiation stuck: {why}"

def noInstance (cmd : String) : M Unit := do
  modify fun s => { s with current := none, currentName := none }
  let _ := cmd

def moduleCmd (dir : System.FilePath) (line : Nat) (cmd : String) (file : String)
    (name : Option String) (define : Bool) : M Unit := do
  let l ← load dir file
  match l with
  | .core =>
    noInstance cmd
    report line cmd "UNSUP core-module" "top-level core module"
  | .decode e =>
    noInstance cmd
    report line cmd "UNSUP decode" e
  | .invalid e =>
    noInstance cmd
    report line cmd "FAIL" s!"validator rejects a valid component: {e}"
  | .ok c ct =>
    if define then
      modify fun s => { s with defs := (name.getD "", c, ct) :: s.defs }
      report line cmd "PASS" s!"defined (root imports {importNames ct})"
    else instantiateCmd line cmd c ct name

/-- Run an `invoke` action; `none` when it could not be run (reported). -/
def invokeAction (line : Nat) (cmd : String) (a : Json) :
    M (Option (CallResult × Option (WIT.FuncType Empty RtId))) := do
  let st ← get
  let modName := (a.getObjValAs? String "module").toOption
  let inst? := match modName with
    | some n => (st.insts.lookup n).join
    | none => st.current
  let some inst := inst? | do
    report line cmd "UNSUP no-instance" "no instance to invoke"
    return none
  let field ← match a.getObjValAs? String "field" with
    | .ok f => pure f
    | .error e => do report line cmd "FAIL" s!"bad action: {e}"; return none
  let some f := inst.exports.lookup field | do
    report line cmd "FAIL" s!"no export {field}"
    return none
  let some ft := funcType? inst.cfg f | do
    report line cmd "FAIL" s!"no function value for {field}"
    return none
  let argsJ := (a.getObjValD "args").getArr?.toOption.getD #[]
  if argsJ.size ≠ ft.params.length then
    report line cmd "FAIL" "argument count"
    return none
  let args ← match (ft.params.zip argsJ.toList).mapM fun (p, j) => toVal p.2 j with
    | .ok vs => pure vs
    | .error e => do report line cmd "UNSUP value" e; return none
  if inst.cfg.store.lockdown then
    return some (.trap (some .lockedDown), none)
  if !inst.cfg.hostInControl then
    report line cmd "UNSUP after-stuck" "the instance's last call did not finish"
    return none
  let cfg₀ : Cfg := { inst.cfg with host := { inst.cfg.host with
    drops := st.drops.1, lastDrop := st.drops.2 } }
  let inst := { inst with cfg := cfg₀ }
  let exploredRuns : List Explore.Run × Bool :=
    if st.explore then exploreCall st.fuel inst.cfg inst.calls f args st.budget else ([], true)
  let (r, cfg', note) : CallResult × Cfg × String :=
    if st.explore then
      match exploredRuns with
      | (main :: rest, complete) =>
        (main.result, main.cfg, s!" [oracles: {rest.length + 1} schedules" ++
          (if complete then ", all" else s!", budget {st.budget} exhausted") ++ "]")
      | ([], _) => (.stuck "no schedule", inst.cfg, "")
    else
    match invoke st.fuel inst.cfg inst.calls f args
        (if st.eager then eagerOracle else oracle) with
    | (.stuck "out of fuel", c) =>
      match [1, 2].findSome? fun seed =>
          match invoke st.fuel inst.cfg inst.calls f args (lcgOracle seed) with
          | (.stuck "out of fuel", _) => none
          | (r, c) => some (r, c, seed) with
      | some (r, c, seed) =>
        (r, c, s!" [oracle lcg {seed}: the first-alternative oracle ran out of fuel]")
      | none => (.stuck "out of fuel", c, " [also out of fuel with oracle lcg 1, 2]")
    | (r, c) => (r, c, "")
  modify fun s => { s with note := note, drops := (cfg'.host.drops, cfg'.host.lastDrop) }
  if st.explore then
    let (runs, complete) := exploredRuns
    modify fun s => { s with alts := runs.drop 1, explored := s.explored + 1 }
    modify fun s => { s with schedules := s.schedules + runs.length }
    modify fun s => { s with partialCalls := s.partialCalls + (if complete then 0 else 1) }
  let inst' := { inst with cfg := cfg', calls := inst.calls + 1 }
  modify fun s => { s with
    current := if modName.isNone || s.currentName == modName then some inst' else s.current,
    insts := s.insts.map fun (n, i) =>
      if some n == modName || (modName.isNone && some n == s.currentName) then (n, some inst')
      else (n, i) }
  return some (r, some ft)

def describe : CallResult → String
  | .returned vs => s!"returned {reprStr vs}"
  | .cancelled => "cancelled"
  | .trap r => s!"trapped: {trapStr r}"
  | .deadlock => "deadlock"
  | .stuck why => s!"stuck: {why}"

/-- The verdict of an `assert_return`, `action` or `assert_trap` command on call result `r`
(`ft`: the function's type): the verdict word (with the `UNSUP` class) and the detail. -/
def callVerdict (ty text : String) (c : Json) (ft : Option (WIT.FuncType Empty RtId))
    (r : CallResult) : String × String :=
  let stuck (r : CallResult) (sfx : String) : String × String :=
    match r with
    | .stuck why =>
      if why.startsWith "internal fault" then ("UNSUP model-fault", why ++ sfx)
      else ("FAIL", describe r ++ sfx)
    | _ => ("FAIL", describe r ++ sfx)
  if ty == "assert_trap" then
    match r with
    | .trap (some .lockedDown) =>
      if contains text.toLower "cannot enter" then
        ("PASS", s!"the store is locked down by an earlier trap (expected \"{text}\")")
      else ("UNSUP after-trap", s!"the store is locked down by an earlier trap (expected \"{text}\")")
    | .trap reason =>
      if reasonAgrees reason text then ("PASS", s!"{describe r} (expected \"{text}\")")
      else ("PASS", s!"{describe r} (expected \"{text}\") [reason-differs]")
    | .deadlock =>
      if contains text "deadlock" || contains text "cannot make further progress" then
        ("PASS", s!"deadlock (expected \"{text}\")")
      else ("FAIL", s!"deadlock, expected trap \"{text}\"")
    | _ =>
      match r with
      | .stuck why =>
        if why.startsWith "internal fault" then ("UNSUP model-fault", s!"{why} (expected \"{text}\")")
        else ("FAIL", s!"{describe r}, expected trap \"{text}\"")
      | _ => ("FAIL", s!"{describe r}, expected trap \"{text}\"")
  else
    match r with
    | .trap (some .lockedDown) => ("UNSUP after-trap", "the store is locked down by an earlier trap")
    | .returned vs =>
      if ty == "action" then ("PASS", describe r) else
      let exp := (c.getObjValD "expected").getArr?.toOption.getD #[]
      let resTy := (ft.bind (·.result)).toList
      if exp.size ≠ vs.length ∨ resTy.length ≠ vs.length then
        ("FAIL", s!"{describe r}, expected {exp.size} values")
      else
        match ((resTy.zip vs).zip exp.toList).allM fun ((t, v), j) => valMatches t v j with
        | .ok true => ("PASS", describe r)
        | .ok false => ("FAIL", s!"{describe r}, expected {(Json.arr exp).compress}")
        | .error e => ("UNSUP value", e)
    | _ => stuck r ""

def command (dir : System.FilePath) (c : Json) : M Unit := do
  let ty := (c.getObjValAs? String "type").toOption.getD "?"
  let line := (c.getObjValAs? Nat "line").toOption.getD 0
  let file := (c.getObjValAs? String "filename").toOption.getD ""
  let name := (c.getObjValAs? String "name").toOption
  let text := (c.getObjValAs? String "text").toOption.getD ""
  match ty with
  | "module" => moduleCmd dir line ty file name false
  | "module_definition" => moduleCmd dir line ty file name true
  | "module_instance" => do
    let inst := (c.getObjValAs? String "instance").toOption
    let modn := (c.getObjValAs? String "module").toOption.getD ""
    match (← get).defs.lookup modn with
    | some (comp, ct) => instantiateCmd line ty comp ct inst
    | none =>
      noInstance ty
      report line ty "UNSUP no-instance" s!"no definition {modn}"
  | "assert_return" | "action" | "assert_trap" => do
    let some (r, ft) ← invokeAction line ty (c.getObjValD "action") | return
    let (v, d) := callVerdict ty text c ft r
    let alts := (← get).alts
    modify fun s => { s with alts := [] }
    -- `--oracle all`: the verdict must not depend on the schedule
    let word (v : String) : String := (v.splitOn " ").headD v
    match alts.find? fun a => word (callVerdict ty text c ft a.result).1 != word v with
    | some a =>
      modify fun s => { s with dependent := s.dependent + 1 }
      let (v', d') := callVerdict ty text c ft a.result
      if word v == "PASS" then
        report line ty "FAIL" s!"{d}; but under oracle script {a.script}: {v'} {d'}"
      else report line ty v s!"{d}; under oracle script {a.script}: {v'} {d'}"
    | none =>
      if contains d "[reason-differs]" then
        modify fun s => { s with reasonDiffers := s.reasonDiffers + 1 }
      report line ty v d
  | "assert_invalid" | "assert_malformed" => do
    if (c.getObjValAs? String "module_type").toOption == some "text" then
      report line ty "SKIP" "text module"
      return
    match ← load dir file with
    | .core => report line ty "UNSUP core-module" "top-level core module"
    | .decode e =>
      if ty == "assert_malformed" then report line ty "PASS" s!"decoder: {e}"
      else report line ty "WEAK decoder" s!"rejected by the decoder, not the validator: {e} (expected \"{text}\")"
    | .invalid e => report line ty "PASS" s!"validator: {e} (expected \"{text}\")"
    | .ok _ _ => report line ty "FAIL" s!"accepted, expected \"{text}\""
  | "assert_unlinkable" | "assert_uninstantiable" => do
    match ← load dir file with
    | .core => report line ty "UNSUP core-module" "top-level core module"
    | .decode e => report line ty "UNSUP decode" e
    | .invalid e =>
      report line ty (if ty == "assert_unlinkable" then "PASS" else "FAIL")
        s!"validator: {e} (expected \"{text}\")"
    | .ok comp ct =>
      match instantiate (← get).fuel (← get).registered comp ct (← get).drops with
      | .instance _ _ _ => report line ty "FAIL" s!"instantiated, expected \"{text}\""
      | .trap r => report line ty "PASS" s!"instantiation trapped: {trapStr r} (expected \"{text}\")"
      | .stuck why =>
        if why.startsWith "internal fault" then report line ty "UNSUP model-fault" why
        else report line ty "FAIL" s!"stuck: {why}, expected \"{text}\""
  | other => report line other "UNSUP command" other

end ComponentWast

open ComponentWast in
def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option (Nat × String × Nat)
    | [] => some (20000000, "first", 64)
    | "--fuel" :: n :: rest => (opts rest).map fun (_, o, b) => (n.toNat!, o, b)
    | "--oracle" :: o :: rest => (opts rest).map fun (f, _, b) => (f, o, b)
    | "--budget" :: n :: rest => (opts rest).map fun (f, o, _) => (f, o, n.toNat!)
    | _ => none
  let (path, fuel, orc, budget) : String × Nat × String × Nat := match args with
    | p :: rest => match opts rest with
      | some (f, o, b) => (p, f, o, b)
      | none => ("", 0, "", 0)
    | [] => ("", 0, "", 0)
  if path == "" || !(orc == "first" || orc == "eager" || orc == "all") then
    IO.eprintln "usage: component-wast SCRIPT.json [--fuel N] [--oracle first|eager|all] [--budget N]"
    return 2
  let fp : System.FilePath := path
  let dir := fp.parent.getD "."
  let j ← match Json.parse (← IO.FS.readFile fp) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"component-wast: {e}"; return 2
  let cmds := (j.getObjValD "commands").getArr?.toOption.getD #[]
  let ((), st) ← (cmds.forM fun c => command dir c).run
    { fuel, eager := orc == "eager", explore := orc == "all", budget }
  IO.println s!"SUMMARY\tpass={st.pass}\tweak={st.weak}\tvalid={st.valid}\tfail={st.fail}\tunsupported={st.unsup}\tskip={st.skip}\treason-differs={st.reasonDiffers}\tgc-disagree={st.gcDisagree}\tdecoded={st.decoded}\tclasses={st.classes}\texplored={st.explored}\tschedules={st.schedules}\tpartial={st.partialCalls}\tdependent={st.dependent}"
  return 0
