module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Store

/-!
# Round 5: `InstrTyping` outside the open classes

`typedV_instrToV_of`: every source instruction outside `InstrOpen` (numeric operators, scalar
loads and stores, SIMD other than `v128.const`) is a typed `instr`, given its nested bodies
typed and its `try_table` catches bounded. Validity is not needed for these: indices are `u32`s
by representation, and source value, heap and reference types are typed outright.

`instrTyping_of_open : OpenTyping B → InstrTyping B`: by well-founded recursion on the
instruction, validity of a block-like instruction makes its bodies valid (`instrOk_bodies`), so
**`InstrTyping` reduces to the open classes**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {B : Builtins}

/-- The index sorts, all aliases of `idx`. -/
def idxNames : List IL.Id := ["typeidx", "funcidx", "globalidx", "tableidx", "memidx", "tagidx",
  "elemidx", "dataidx", "labelidx", "localidx", "fieldidx"]

set_option maxRecDepth 100000 in
theorem findTyp_xidx (x : IL.Id) (hx : x ∈ idxNames) :
    (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := by
  simp only [idxNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- An index of any sort. -/
theorem typedV_xidx (x : IL.Id) (hx : x ∈ idxNames) {k : IndexKind} (i : Idx k) :
    TypedV (simEnv B) (.varT x []) (Encode.toValue i) :=
  Typing.typedV_alias (findTyp_xidx x hx) (Typing.typedV_idx i)

/-- `_IDX x`, a `typeuse`. -/
theorem typedV_typeuseIdx (x : TypeIdx) :
    TypedV (simEnv B) (.varT "typeuse" []) (.case "_IDX" (Encode.toValue x)) :=
  Typing.typedV_closedCase Typing.findTyp_typeuse rfl
    (typedV_xidx "typeidx" (by simp [idxNames]) x _ ⟨rfl, rfl, rfl⟩)

/-- Every source reference type is a `reftype`. -/
theorem typedV_reftypeSrc (rt : RefType) :
    TypedV (simEnv B) (.varT "reftype" []) (Encode.toValue rt) :=
  Typing.typedV_closedCase findTyp_reftype rfl (hasTyp_tupT_iff.2 ⟨_, rfl,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, Typing.hasTyp_nullOpt rt.nullable,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, Typing.typedV_heaptype rt.heap _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-- `sx?`. -/
theorem typedV_sxOpt (s : Option Signedness) :
    TypedV (simEnv B) (.iterT (.varT "sx" []) .opt) (.opt (s.map sxV)) := by
  rcases s with _ | s
  · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  · exact fun ρ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, ConfigOk.typedV_sx s ρ hρ⟩)

/-- A one-payload `instr` case. -/
theorem typedV_instr1 {op : MixopS} {t : Typ} {w : Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271
      0 0) op = some (t, []))
    (hq : IntNumeric.quantFreeAt (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op = true)
    (h : TypedV (simEnv B) t w) : TypedV (simEnv B) (.varT "instr" []) (.case op w) :=
  FwdMem.typedV_instrCase hf hq (h _ ⟨rfl, rfl, rfl⟩)

/-- An index-only `instr` case. -/
theorem typedV_instrIdx {op : MixopS} {x : IL.Id} {k : IndexKind} (i : Idx k)
    (hf : IntNumeric.findCase (IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271
      0 0) op = some (.varT x [], []))
    (hq : IntNumeric.quantFreeAt (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op = true)
    (hx : x ∈ idxNames := by simp [idxNames]) :
    TypedV (simEnv B) (.varT "instr" []) (.case op (Encode.toValue i)) :=
  typedV_instr1 hf hq (typedV_xidx x hx i)

/-- A two-index `instr` case. -/
theorem typedV_instrIdx2 {op : MixopS} {a b x y : IL.Id} {k k' : IndexKind} (i : Idx k)
    (j : Idx k')
    (hf : IntNumeric.findCase (IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271
      0 0) op = some (.tupT [.mk a (.varT x []), .mk b (.varT y [])], []))
    (hq : IntNumeric.quantFreeAt (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op = true)
    (hx : x ∈ idxNames := by simp [idxNames]) (hy : y ∈ idxNames := by simp [idxNames]) :
    TypedV (simEnv B) (.varT "instr" [])
      (.case op (.tuple [Encode.toValue i, Encode.toValue j])) :=
  FwdMem.typedV_instrCase hf hq (hasTyp_tup2 (typedV_xidx x hx i) (typedV_xidx y hy j))

/-- A nullary `instr` case. -/
theorem typedV_instr0 {op : MixopS}
    (hf : IntNumeric.findCase (IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271
      0 0) op = some (.tupT [], []))
    (hq : IntNumeric.quantFreeAt (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op = true) :
    TypedV (simEnv B) (.varT "instr" []) (.case op (.tuple [])) :=
  FwdMem.typedV_instrCase hf hq hasTyp_tupT_nil

/-- A list of labels is a `labelidx*`. -/
theorem typedV_labels (ls : List LabelIdx) :
    TypedV (simEnv B) (.iterT (.varT "labelidx" []) .list) (.list (ls.map Encode.toValue)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_xidx "labelidx" (by simp [idxNames]) l

/-- `(valtype*)?`. -/
theorem typedV_selectAnnot (ts : List ValType) :
    TypedV (simEnv B) (.iterT (.iterT (.varT "valtype" []) .list) .opt)
      (.opt (some (.list (ts.map Encode.toValue)))) := fun ρ hρ =>
  hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, (typedV_list_iff.2 fun u hu => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
    exact Typing.typedV_valtype t) ρ hρ⟩)

/-- `list(catch)`, below `2^32` catches. -/
theorem typedV_catches (cs : List Catch) (h : cs.length < 2 ^ 32) :
    TypedV (simEnv B) (.varT "list" [.typA (.varT "catch" [])])
      (.case "%" (.tuple [.list (cs.map Encode.toValue)])) :=
  typedV_listT (by decide) (by simpa using h) fun u hu => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
    exact Round4.typedV_catch c

set_option maxRecDepth 100000 in
/-- **Every instruction outside `InstrOpen` is a typed `instr`**, given its bodies typed and its
catches bounded (`instrBnd`). -/
theorem typedV_instrToV_of (i : Instr) (hopen : InstrOpen i = false)
    (hb : Round4.instrBnd i = true)
    (hbodies : ∀ b ∈ i.bodies, TypedV (simEnv B) instrsT (.list (instrsToV b))) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  cases i
  all_goals try first
    | (simp [InstrOpen] at hopen; done)
    | exact typedV_instr0 rfl rfl
    | exact typedV_instrIdx _ rfl rfl
    | exact typedV_instrIdx2 _ _ rfl rfl
  case select ts =>
    rcases ts with _ | ts
    · exact typedV_instr1 rfl rfl fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact typedV_instr1 rfl rfl (typedV_selectAnnot ts)
  case block bt body =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup2 (Typing.typedV_blocktype bt)
      (hbodies body (by simp [Instr.bodies])))
  case loop bt body =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup2 (Typing.typedV_blocktype bt)
      (hbodies body (by simp [Instr.bodies])))
  case if_ bt b₁ b₂ =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup3 (Typing.typedV_blocktype bt)
      (hbodies b₁ (by simp [Instr.bodies])) (hbodies b₂ (by simp [Instr.bodies])))
  case brTable ls l =>
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_tup2 (typedV_labels ls) (typedV_xidx "labelidx" (by simp [idxNames]) l))
  case brOnCast l s t =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup3
      (typedV_xidx "labelidx" (by simp [idxNames]) l) (typedV_reftypeSrc s) (typedV_reftypeSrc t))
  case brOnCastFail l s t =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup3
      (typedV_xidx "labelidx" (by simp [idxNames]) l) (typedV_reftypeSrc s) (typedV_reftypeSrc t))
  case callRef x => exact typedV_instr1 rfl rfl (typedV_typeuseIdx x)
  case returnCallRef x => exact typedV_instr1 rfl rfl (typedV_typeuseIdx x)
  case callIndirect x y =>
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_tup2 (typedV_xidx "tableidx" (by simp [idxNames]) x) (typedV_typeuseIdx y))
  case returnCallIndirect x y =>
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_tup2 (typedV_xidx "tableidx" (by simp [idxNames]) x) (typedV_typeuseIdx y))
  case tryTable bt cs body =>
    have hb' : cs.length < Round4.bnd32 ∧ Round4.instrsBnd body = true := by
      simpa [Round4.instrBnd] using hb
    have hcs : cs.length < 2 ^ 32 := hb'.1
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup3 (Typing.typedV_blocktype bt)
      (typedV_catches cs hcs) (hbodies body (by simp [Instr.bodies])))
  case refNull ht => exact typedV_instr1 rfl rfl (Typing.typedV_heaptype ht)
  case refTest rt => exact typedV_instr1 rfl rfl (typedV_reftypeSrc rt)
  case refCast rt => exact typedV_instr1 rfl rfl (typedV_reftypeSrc rt)
  case i31Get s => exact typedV_instr1 rfl rfl (ConfigOk.typedV_sx s)
  case structGet s x f =>
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tup3 (typedV_sxOpt s)
      (typedV_xidx "typeidx" (by simp [idxNames]) x) (typedV_xidx "fieldidx" (by simp [idxNames]) f))
  case arrayGet s x =>
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_tup2 (typedV_sxOpt s) (typedV_xidx "typeidx" (by simp [idxNames]) x))
  case arrayNewFixed x n =>
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_tup2 (typedV_xidx "typeidx" (by simp [idxNames]) x) (Typing.typedV_u32 n.isLt))
  case intConst t b => exact Typing.typedV_instr_val (.num ⟨.int t, b⟩)
  case floatConst t b => exact Typing.typedV_instr_val (.num ⟨.float t, b⟩)
  case vecConst b => exact Typing.typedV_instr_val (.vec b)

/-- **The bodies of a valid instruction are valid.** -/
theorem instrOk_bodies {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) :
    ∀ b ∈ i.bodies, ∃ C' it', InstrsOk C' b it' := by
  cases h with
  | parametric hp => cases hp <;> simp [Instr.bodies]
  | numeric hp => cases hp <;> simp [Instr.bodies]
  | vector hp => cases hp <;> simp [Instr.bodies]
  | «variable» hp => cases hp <;> simp [Instr.bodies]
  | memory hp => cases hp <;> simp [Instr.bodies]
  | table hp => cases hp <;> simp [Instr.bodies]
  | reference hp => cases hp <;> simp [Instr.bodies]
  | block _ hb => exact fun _ hm => (List.mem_singleton.1 hm) ▸ ⟨_, _, hb⟩
  | loop _ hb => exact fun _ hm => (List.mem_singleton.1 hm) ▸ ⟨_, _, hb⟩
  | if_ _ h₁ h₂ =>
    exact fun _ hm => (List.mem_pair.1 hm).elim (fun h => h ▸ ⟨_, _, h₁⟩)
      (fun h => h ▸ ⟨_, _, h₂⟩)
  | tryTable _ hb _ => exact fun _ hm => (List.mem_singleton.1 hm) ▸ ⟨_, _, hb⟩
  | _ => simp [Instr.bodies]

/-- The bodies of a bounded instruction are bounded. -/
theorem instrBnd_bodies {i : Instr} (h : Round4.instrBnd i = true) :
    ∀ b ∈ i.bodies, Round4.instrsBnd b = true := by
  cases i <;> simp_all [Round4.instrBnd, Instr.bodies]

/-- An instruction of a body is smaller than the instruction. -/
theorem sizeOf_lt_of_body {i j : Instr} {b : List Instr} (hb : b ∈ i.bodies) (hj : j ∈ b) :
    sizeOf j < sizeOf i := by
  have hjb : sizeOf j < sizeOf b := List.sizeOf_lt_of_mem hj
  cases i <;> simp only [Instr.bodies, List.mem_singleton, List.mem_pair, List.not_mem_nil] at hb
  all_goals first
    | (subst hb; simp only [Instr.block.sizeOf_spec, Instr.loop.sizeOf_spec,
        Instr.tryTable.sizeOf_spec]; omega)
    | (rcases hb with rfl | rfl <;> simp only [Instr.if_.sizeOf_spec] <;> omega)

/-- **`InstrTyping` from the open classes**, by well-founded recursion on the instruction. -/
theorem instrTyping_aux (hO : OpenTyping B) :
    ∀ (i : Instr) (C : Context) (it : InstrType), InstrOk C i it → Round4.instrBnd i = true →
      TypedV (simEnv B) (.varT "instr" []) (instrToV i)
  | i, C, it, hok, hb =>
    if hop : InstrOpen i = true then hO C i it hok hb hop
    else typedV_instrToV_of i (by simpa using hop) hb fun b hbm => by
      obtain ⟨C', it', hbo⟩ := instrOk_bodies hok b hbm
      rw [Exn.instrsToV_eq_map]
      exact typedV_list_iff.2 fun u hu => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hu
        obtain ⟨C'', it'', hjo⟩ := instrsOk_mem hbo j hj
        have := sizeOf_lt_of_body hbm hj
        exact instrTyping_aux hO j C'' it'' hjo (instrsBnd_mem (instrBnd_bodies hb b hbm) j hj)
termination_by i => sizeOf i

/-- **`InstrTyping` reduces to the open classes.** -/
theorem instrTyping_of_open (hO : OpenTyping B) : InstrTyping B :=
  fun C i it hok hb => instrTyping_aux hO i C it hok hb

/-- **`PosTypingNE` from `OpenTyping`.** -/
theorem posTypingNE_of_open {H : Type} (hO : OpenTyping B) (hn : H → String) :
    PosTypingNE B hn :=
  posTypingNE_of_instr (instrTyping_of_open hO) hn

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
