module

public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: memory SIMD (`Step` 22–25)

Round 6 kept the memory SIMD instructions out of every theorem. `Round4.Bounded` rejects them
(`Round6.MemSimd.noMemSimd_of_bounded`), and `instrToV` encodes them by the provisional
`schemaInstrV`, which is not a typed `instr` (`Round6.MemSimd.not_typedV_instrToV_vecStore`).
Round 6's track memsimd defined the real encoding `Round6.MemSimd.instrToVM`, checked against the
IL type `instr` (`typedV_vecMemV`), but did not use it.

This header adds what the stores need.

* `vbytesCall`, `withVBytes B`: `$vbytes_(V128, c)` is a `hint(builtin)` with no clauses, and
  `Prims.builtins` does not answer it. So `Step/vstore-val` (rule 23) can never fire in
  `simEnv (BI …)`, although Core's `vecStoreVal` steps. `withVBytes B` answers it with the
  16-byte little-endian encoding of `c` and defers to `B` elsewhere.
* `VBytes env`: what the store rules need of the environment, `$vbytes_` on the image of a
  `V128`.

The per-rule simulation (`Silmaril/Proofs/Wasm/SpecTec/Sim/Round7/MemSimd/VStore.lean` and its
siblings) is stated at the level of encoded states and instruction lists, with the memory SIMD
instruction encoded by `instrToVM`.

**The configuration-level encoding (pass 3).** `instrToVM` re-encodes only an instruction at the
top; a block body still goes through `instrToV`. `instrToVD` re-encodes at every depth (block,
loop, if and `try_table` bodies), and `adminToVD`, `funcInstVD`, `storeVD`, `stateVD`, `configVD`
are round 3's encoders with `instrToVD` in place of `instrToV`. Off memory SIMD code they are the
old encoders (`configVD_eq_of_noMemSimd`), so on round 6's domain nothing changes.

**The extended domain.** `instrBndM` is `Round4.instrBnd` without the clause rejecting the four
memory SIMD instructions; `BoundedM` is `Round4.Bounded` with it, and `BoundedSelM` is
`Round5.Target.BoundedSel` with `BoundedM` for `Round4.Bounded`.

**The target `Round7.Task.wholeStepValidRM`** (frozen, **open**): `Round6.Task.wholeStepValidR`
at the backend reading, with `configVD` for `configV` and `BoundedSelM` for `BoundedSel`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue moduleInstToValue tagInstToValue memInstToValue
  tableInstToValue dataInstToValue elemInstToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

namespace MemSimd

/-- `$vbytes_(V128, c)`: the 16-byte little-endian encoding of `c`. -/
def vbytesCall : List ArgV → Option Value
  | [.val (.case "V128" (.tuple [])), .val (.case "%" (.tuple [.num (.natN n)]))] =>
      some (.list (FwdMem.leBytesV 16 n))
  | _ => none

/-- **`B` with `$vbytes_` answered by `vbytesCall`.** -/
def withVBytes (B : Builtins) : Builtins :=
  ⟨fun x ws => if x = "vbytes_" then vbytesCall ws else B.call x ws⟩

/-- **What the vector store rules need of the environment**: `$vbytes_(V128, c)` is Core's
16-byte little-endian encoding. -/
def VBytes (env : Env) : Prop :=
  ∀ c : BitVec 128, Silmaril.SpecTec.Equiv.ExecNumeric.Applies env "vbytes_"
    [.val (caseNilV "V128"), .val (pctV c.toNat)] (.list (FwdMem.leBytesV 16 c.toNat))


/-! ## The configuration-level encoding with `instrToVM` -/

mutual
/-- **`instrToV` with the memory SIMD instructions encoded by `instrToVM` at every depth.** -/
def instrToVD : Instr → Value
  | .block bt body => .case "BLOCK" (.tuple [Encode.toValue bt, .list (instrsToVD body)])
  | .loop bt body => .case "LOOP" (.tuple [Encode.toValue bt, .list (instrsToVD body)])
  | .if_ bt b₁ b₂ =>
      .case "IF%%ELSE%" (.tuple [Encode.toValue bt, .list (instrsToVD b₁), .list (instrsToVD b₂)])
  | .tryTable bt cs body =>
      .case "TRY_TABLE" (.tuple [Encode.toValue bt,
        .case "%" (.tuple [.list (cs.map Encode.toValue)]),
        .list (instrsToVD body)])
  | i => Round6.MemSimd.instrToVM i

/-- `instrToVD` on a sequence. -/
def instrsToVD : List Instr → List Value
  | [] => []
  | i :: is => instrToVD i :: instrsToVD is
end

mutual
/-- `adminToV` with `instrToVD`. -/
def adminToVD : Admin → Value
  | .plain i => instrToVD i
  | .ref r => refToValue r
  | .callRefType d => .case "CALL_REF" (CT.defType d)
  | .returnCallRefType d => .case "RETURN_CALL_REF" (CT.defType d)
  | .label n cont body =>
      .case "LABEL_%{%}%"
        (.tuple [.num (.natN n), .list (instrsToVD cont), .list (adminsToVD body)])
  | .handler n cs body =>
      .case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
        .list (adminsToVD body)])
  | .frame n f body =>
      .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV f, .list (adminsToVD body)])
  | .trap => caseNilV "TRAP"

/-- `adminToVD` on a sequence. -/
def adminsToVD : List Admin → List Value
  | [] => []
  | a :: rest => adminToVD a :: adminsToVD rest
end

/-- `funcInstV` with `instrToVD`. -/
def funcInstVD (hn : H → String) (f : FuncInst H) : Value :=
  .struct [("TYPE", CT.defType f.type), ("MODULE", moduleInstToValue CT f.module),
    ("CODE", match f.code with
      | .wasm fn => .case "FUNC" (.tuple [pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToVD fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h)))]

/-- `storeV` with `funcInstVD`. -/
def storeVD (hn : H → String) (s : Store H) : Value :=
  .struct
    [("TAGS", .list (s.tags.map (tagInstToValue CT))),
     ("GLOBALS", .list (s.globals.map globalInstV)),
     ("MEMS", .list (s.mems.map memInstToValue)),
     ("TABLES", .list (s.tables.map (tableInstToValue CT))),
     ("FUNCS", .list (s.funcs.map (funcInstVD hn))),
     ("DATAS", .list (s.datas.map dataInstToValue)),
     ("ELEMS", .list (s.elems.map (elemInstToValue CT))),
     ("STRUCTS", .list (s.structs.map structInstV)),
     ("ARRAYS", .list (s.arrays.map arrayInstV)),
     ("EXNS", .list (s.exns.map exnInstV))]

/-- `stateV` with `storeVD`. -/
def stateVD (hn : H → String) (s : Store H) (f : Frame) : Value :=
  .case "%;%" (.tuple [storeVD hn s, frameV f])

/-- **The configuration-level encoding with the memory SIMD instructions encoded against
`instr`**: `configV` with `instrToVD` everywhere, in the code and in the store's function
bodies. -/
def configVD (hn : H → String) (c : Config H) : Value :=
  .case "%;%" (.tuple [stateVD hn c.store c.frame, .list (adminsToVD c.code)])

/-! ## The extended domain -/

mutual
/-- `Round4.instrBnd` admitting the four memory SIMD instructions. -/
def instrBndM : Instr → Bool
  | .block _ body => instrsBndM body
  | .loop _ body => instrsBndM body
  | .if_ _ b₁ b₂ => instrsBndM b₁ && instrsBndM b₂
  | .tryTable _ cs body => decide (cs.length < Round4.bnd32) && instrsBndM body
  | _ => true

/-- `instrBndM` on a sequence. -/
def instrsBndM : List Instr → Bool
  | [] => true
  | i :: is => instrBndM i && instrsBndM is
end

/-- `Round4.FuncBnd` with `instrsBndM`. -/
def FuncBndM (fi : FuncInst H) : Prop :=
  Round4.tyBnd fi.type = true ∧ Round4.ModuleBnd fi.module ∧
    ∀ fn, fi.code = .wasm fn → instrsBndM fn.body = true

/-- `Round4.StoreBnd` with `FuncBndM`. -/
structure StoreBndM (s : Store H) : Prop where
  /-- Tag types. -/
  tags : ∀ ti ∈ s.tags, Round4.tyBnd ti.type = true
  /-- Global types. -/
  globals : ∀ gi ∈ s.globals, Round4.tyBnd gi.type.type = true
  /-- Table element types. -/
  tables : ∀ ti ∈ s.tables, Round4.tyBnd ti.type.element = true
  /-- Function instances. -/
  funcs : ∀ fi ∈ s.funcs, FuncBndM fi
  /-- Element segment types. -/
  elems : ∀ ei ∈ s.elems, Round4.tyBnd ei.type = true
  /-- Structure instance types. -/
  structs : ∀ si ∈ s.structs, Round4.tyBnd si.type = true
  /-- Array instance types. -/
  arrays : ∀ ai ∈ s.arrays, Round4.tyBnd ai.type = true

mutual
/-- `Round4.AdminBnd` with `instrBndM`. -/
def AdminBndM : Admin → Prop
  | .plain i => instrBndM i = true
  | .ref _ => True
  | .callRefType d => Round4.tyBnd d = true
  | .returnCallRefType d => Round4.tyBnd d = true
  | .label _ cont body => instrsBndM cont = true ∧ AdminsBndM body
  | .handler _ _ body => AdminsBndM body
  | .frame _ f body => Round4.ModuleBnd f.module ∧ AdminsBndM body
  | .trap => True

/-- `AdminBndM` on a sequence. -/
def AdminsBndM : List Admin → Prop
  | [] => True
  | a :: l => AdminBndM a ∧ AdminsBndM l
end

/-- **`Round4.Bounded` admitting memory SIMD code.** -/
structure BoundedM (c : Config H) : Prop where
  /-- Table, segment, array and memory sizes. -/
  store : Integrate.StoreOk c.store
  /-- Types, modules and code held by the store. -/
  storeBnd : StoreBndM c.store
  /-- The frame's module. -/
  frame : Round4.ModuleBnd c.frame.module
  /-- The active code. -/
  code : AdminsBndM c.code

/-- **`Round5.Target.BoundedSel` admitting memory SIMD code.** -/
def BoundedSelM (c : Config H) : Prop :=
  (BoundedM c ∧ Round5.Pos.NoExports c) ∧ Round5.Target.NoMissel c

/-! ## The restated target -/

/-- **The round-7 target with memory SIMD** (frozen, open). It is `Round6.Task.wholeStepValidR`
at the backend reading, with SpecTec configurations encoded by `configVD` (memory SIMD
instructions against the IL type `instr`) and the domain `BoundedSelM` (memory SIMD code
admitted). -/
def Task.wholeStepValidRM : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelM c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧
              Round6.Int.backend.step B (configVD hn c) (configVD hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelM c → Round6.Int.backend.step B (configVD hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step (Profile.spec nd r) host c c')

/-- **`Round7.Task.wholeStepValidRM` on its memory-SIMD-free part** (pass 4): both halves with
`NoMemSimd` added for the source and for every Core successor. On that part `configVD` is
`configV` and `BoundedSelM` is round 6's `BoundedSel`, so it follows from round 6
(`Round7.MemSimd.wholeStepValidRMNoMS_backend`). It is a restriction of the frozen target, not
the target. -/
def WholeStepValidRMNoMS : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host →
      ∀ (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
          Round6.MemSimd.NoMemSimd c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ →
            BoundedSelM c₁ ∧ Round6.MemSimd.NoMemSimd c₁) →
          Step (Profile.spec nd r) host c c' →
          ∃ c'', Step (Profile.spec nd r) host c c'' ∧
            ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
            ∃ d', Bwd.ConfigEq c'' d' ∧
              Round6.Int.backend.step B (configVD hn c) (configVD hn d')) ∧
        (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
          BoundedSelM c → Round6.MemSimd.NoMemSimd c →
          (∀ c₁, Step (Profile.spec nd r) host c c₁ → Round6.MemSimd.NoMemSimd c₁) →
          Round6.Int.backend.step B (configVD hn c) w →
          ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step (Profile.spec nd r) host c c')

/-! ## Round 6's generic backward dispatch at `configVD` (pass 5)

Round 6's backward recursion (`Round6.Target.backward_upToVC`) is stated at `configV`. The
definitions below are its interface at `configVD`: the typing facts it needs of encoded
configurations, the conclusion up to `ConfigEq`, and the per-rule obligations. The recursion
itself is `Round7.MemSimd.backward_upToD`; the memory SIMD `Step_read` rules discharge their
obligations in `Round7.MemSimd.readMSD`. -/

/-- `c`'s `configVD` image is a value of SpecTec's type `config`. -/
def TypedD (env : Env) (hn : H → String) (c : Config H) : Prop :=
  HasTyp env VarEnv.empty (.varT "config" []) (configVD hn c)

/-- **What the generic backward recursion needs of the typing of `configVD` images**: the fields
of `Sim.TypingFacts` that it uses, at `configVD`. -/
structure TypingFactsD (env : Env) (hn : H → String) : Prop where
  /-- A typed configuration has a typed state and typed code. -/
  config : ∀ c : Config H, TypedD env hn c ↔
    TypedV env stateT (stateVD hn c.store c.frame) ∧ TypedV env instrsT (.list (adminsToVD c.code))
  /-- A state is typed when its store and frame are. -/
  state : ∀ (s : Store H) (f : Frame), TypedV env stateT (stateVD hn s f) ↔
    TypedV env storeT (storeVD hn s) ∧ TypedV env frameT (frameV f)
  /-- `instr*` is typed elementwise. -/
  append : ∀ a b : List Value, TypedV env instrsT (.list (a ++ b)) ↔
    TypedV env instrsT (.list a) ∧ TypedV env instrsT (.list b)
  /-- The body of a typed label. -/
  label : ∀ (n : Nat) (cont : List Instr) (body : List Admin),
    TypedV env instrsT (.list [adminToVD (.label n cont body)]) →
      TypedV env instrsT (.list (adminsToVD body))
  /-- The body of a typed handler. -/
  handler : ∀ (n : Nat) (cs : List Catch) (body : List Admin),
    TypedV env instrsT (.list [adminToVD (.handler n cs body)]) →
      TypedV env instrsT (.list (adminsToVD body))
  /-- The frame and body of a typed frame. -/
  frame : ∀ (n : Nat) (f : Frame) (body : List Admin),
    TypedV env instrsT (.list [adminToVD (.frame n f body)]) →
      TypedV env frameT (frameV f) ∧ TypedV env instrsT (.list (adminsToVD body))

/-- `Bwd.BwdUpTo` at `configVD`: `w` is the image of a configuration equivalent to a Core
successor of `c`. -/
def BwdUpToD (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H)
    (w : Value) : Prop :=
  ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

/-- **The per-rule backward obligations at `configVD`**, under a predicate `V`:
`Round4Read.BackwardUpToV` with `configVD`, `adminsToVD` and `TypedD`. -/
structure BackwardUpToD (V : Config H → Prop) (env : Env) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    V ⟨s, f, is⟩ → TypedD env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule. -/
  read : ∀ (i : Nat) (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule. -/
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step" i (.tuple [configVD hn c, w]) → BwdUpToD hn P host c w

/-- The memory SIMD `Step_read` rules: the trapping loads 42, 44, 46, 48, 50 and the loads in
bounds 43, 45, 47, 49, 51. -/
def msReadRules : List Nat := [42, 43, 44, 45, 46, 47, 48, 49, 50, 51]

/-- **`BackwardUpToD` without the memory SIMD `Step_read` rules**: what remains of the per-rule
obligations once `readMSD` discharges rules 42–51. -/
structure BackwardUpToDRest (V : Config H → Prop) (env : Env) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    V ⟨s, f, is⟩ → TypedD env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule, off the memory SIMD rules. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule. -/
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step" i (.tuple [configVD hn c, w]) → BwdUpToD hn P host c w

/-- The memory SIMD store rules of `Step`: 22–25 (pass 6). -/
def stepMSRules : List Nat := [22, 23, 24, 25]

/-- **`BackwardUpToDRest` without the memory SIMD store rules** (pass 6): what remains of the
per-rule obligations once `readMSD` discharges `Step_read` 42–51 and `stepMSD` discharges `Step`
22–25. -/
structure BackwardUpToDRestS (V : Config H → Prop) (env : Env) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    V ⟨s, f, is⟩ → TypedD env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule, off the memory SIMD rules. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), V c → TypedD env hn c →
    Fires env "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule, off the memory SIMD rules. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → ∀ (c : Config H) (w : Value), V c →
    TypedD env hn c → Fires env "Step" i (.tuple [configVD hn c, w]) → BwdUpToD hn P host c w

/-! ## A state encoding with any function list (pass 6)

`stateV` and `stateVD` differ only in the `FUNCS` field of the store. The memory SIMD rules never
read that field, so their per-rule leaves are stated at `stateVF F s f`, the store encoding with
an arbitrary `FUNCS` value `F`; `stateV hn s f` and `stateVD hn s f` are its instances
(`stateV_eq_stateVF`, `stateVD_eq_stateVF`). -/

/-- `storeV` with the `FUNCS` field given by `F`. -/
def storeVF (F : Value) (s : Store H) : Value :=
  .struct
    [("TAGS", .list (s.tags.map (tagInstToValue CT))),
     ("GLOBALS", .list (s.globals.map globalInstV)),
     ("MEMS", .list (s.mems.map memInstToValue)),
     ("TABLES", .list (s.tables.map (tableInstToValue CT))),
     ("FUNCS", F),
     ("DATAS", .list (s.datas.map dataInstToValue)),
     ("ELEMS", .list (s.elems.map (elemInstToValue CT))),
     ("STRUCTS", .list (s.structs.map structInstV)),
     ("ARRAYS", .list (s.arrays.map arrayInstV)),
     ("EXNS", .list (s.exns.map exnInstV))]

/-- `stateV` with the store's `FUNCS` field given by `F`. -/
def stateVF (F : Value) (s : Store H) (f : Frame) : Value :=
  .case "%;%" (.tuple [storeVF F s, frameV f])

end MemSimd

end Silmaril.Wasm.SpecTec.Sim.Round7
