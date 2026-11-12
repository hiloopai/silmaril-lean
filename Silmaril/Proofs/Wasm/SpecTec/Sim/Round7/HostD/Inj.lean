module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostD.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Thms

/-!
# Round 7, memory SIMD: `storeVD` is injective on typed store images

Round 5 proved that `storeV hn` is injective on stores whose image is a typed `store`
(`Round5.FwdRef2.storeV_inj_typed`). The same holds of `storeVD hn`, which encodes memory SIMD
instructions by `Round6.MemSimd.instrToVM` at every depth:

* `instrToVD_head`: every `case` image of `instrToVD` carries the instruction's head;
* `vecMemV_inj`: the IL image of a memory SIMD instruction determines it;
* `instrToVD_inj`: `instrToVD` is injective at images satisfying a good predicate
  (`Round5.FwdRef2.GoodV`). Off blocks and memory SIMD instructions it is `instrToV`, and round 5's
  `instrToV_inj` applies; the block cases recurse;
* `storeVD_inj_typed`: so `storeVD hn` is injective on stores with typed images, for an injective
  `hn` (the function bodies are the only components that need the typing).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL (MixopS)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Round5.FwdRef2 (GoodV InstrG goodV_typed toValue_eq_iff memargV_eq_iff szV_eq_iff
  laneIdxV_inj)
open Round6.MemSimd (memSimd instrToVM vecMemV vecLoadOpV)
open Round7.MemSimd (instrToVD instrsToVD funcInstVD storeVD)
open Round7.MSPres (memSimd_of_head head_memSimd block_of_head loop_of_head if_of_head
  tryTable_of_head)

variable {H : Type}

/-! ## Heads -/

/-- Off the four block forms, a `case` image of `instrToVD` carries the instruction's head. -/
theorem instrToVD_head_other (i : Instr) (h₁ : ∀ bt b, i = .block bt b → False)
    (h₂ : ∀ bt b, i = .loop bt b → False) (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False)
    (h₄ : ∀ bt cs b, i = .tryTable bt cs b → False) (op : MixopS) (w : Value)
    (h : instrToVD i = .case op w) : op = Typing.instrHead i := by
  have h' : instrToVM i = .case op w := (instrToVD.eq_5 i h₁ h₂ h₃ h₄).symm.trans h
  cases hm : memSimd i with
  | true => exact Round7.MemSimd.instrToVM_case_memSimd hm h'
  | false => exact Typing.instrToV_case ((Round6.MemSimd.instrToVM_of_not hm).symm.trans h')

/-- **Every `case` image of `instrToVD` carries the instruction's head.** -/
theorem instrToVD_head (j : Instr) {op : MixopS} {w : Value} (h : instrToVD j = .case op w) :
    op = Typing.instrHead j :=
  (instrToVD.mutual_induct (fun j => ∀ op w, instrToVD j = .case op w →
      op = Typing.instrHead j) (fun _ => True)
    (fun _ _ _ _ _ h => (Value.case.inj h).1.symm)
    (fun _ _ _ _ _ h => (Value.case.inj h).1.symm)
    (fun _ _ _ _ _ _ _ h => (Value.case.inj h).1.symm)
    (fun _ _ _ _ _ _ h => (Value.case.inj h).1.symm)
    instrToVD_head_other trivial (fun _ _ _ _ => trivial)).1 j op w h

/-! ## Memory SIMD images -/

/-- An `instrToVM` image that is a `case` carries the instruction's head. -/
theorem instrToVM_head {i : Instr} {op : MixopS} {w : Value} (h : instrToVM i = .case op w) :
    op = Typing.instrHead i := by
  cases hm : memSimd i with
  | true => exact Round7.MemSimd.instrToVM_case_memSimd hm h
  | false =>
    rw [Round6.MemSimd.instrToVM_of_not hm] at h
    exact Typing.instrToV_case h


theorem vecLoad_of_head {i : Instr} (h : Typing.instrHead i = "VLOAD") :
    ∃ op m a, i = .vecLoad op m a := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, _, rfl⟩ | simp at h

theorem vecLoadLane_of_head {i : Instr} (h : Typing.instrHead i = "VLOAD_LANE") :
    ∃ p m a l, i = .vecLoadLane p m a l := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, _, _, rfl⟩ | simp at h

theorem vecStore_of_head {i : Instr} (h : Typing.instrHead i = "VSTORE") :
    ∃ m a, i = .vecStore m a := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, rfl⟩ | simp at h

theorem vecStoreLane_of_head {i : Instr} (h : Typing.instrHead i = "VSTORE_LANE") :
    ∃ p m a l, i = .vecStoreLane p m a l := by
  cases i <;> simp only [Typing.instrHead] at h <;> first | exact ⟨_, _, _, _, rfl⟩ | simp at h

theorem vecLoadOpV_inj {a b : VecLoadOp} (h : vecLoadOpV a = vecLoadOpV b) : a = b := by
  cases a <;> cases b <;> simp_all [vecLoadOpV, Round5.FwdRef2.vecSxV_inj.eq_iff, szV_eq_iff]

theorem vecLoad_inj {o o' : VecLoadOp} {m m' : MemIdx} {a a' : MemArg}
    (h : instrToVM (.vecLoad o m a) = instrToVM (.vecLoad o' m' a')) :
    Instr.vecLoad o m a = .vecLoad o' m' a' := by
  have h' : vecLoadOpV o = vecLoadOpV o' ∧ m = m' ∧ a = a' := by
    simpa only [instrToVM, vecMemV, Option.getD_some, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, Value.opt.injEq, toValue_eq_iff, memargV_eq_iff, true_and,
      and_true] using h
  rw [vecLoadOpV_inj h'.1, h'.2.1, h'.2.2]

theorem vecLoadLane_inj {p p' : PackSize} {m m' : MemIdx} {a a' : MemArg} {l l' : LaneIdx}
    (h : instrToVM (.vecLoadLane p m a l) = instrToVM (.vecLoadLane p' m' a' l')) :
    Instr.vecLoadLane p m a l = .vecLoadLane p' m' a' l' := by
  have h' : p = p' ∧ m = m' ∧ a = a' ∧ Vec.laneIdxV l = Vec.laneIdxV l' := by
    simpa only [instrToVM, vecMemV, Option.getD_some, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, szV_eq_iff, toValue_eq_iff, memargV_eq_iff, true_and, and_true] using h
  rw [h'.1, h'.2.1, h'.2.2.1, laneIdxV_inj h'.2.2.2]

theorem vecStore_inj {m m' : MemIdx} {a a' : MemArg}
    (h : instrToVM (.vecStore m a) = instrToVM (.vecStore m' a')) :
    Instr.vecStore m a = .vecStore m' a' := by
  have h' : m = m' ∧ a = a' := by
    simpa only [instrToVM, vecMemV, Option.getD_some, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, toValue_eq_iff, memargV_eq_iff, true_and, and_true] using h
  rw [h'.1, h'.2]

theorem vecStoreLane_inj {p p' : PackSize} {m m' : MemIdx} {a a' : MemArg} {l l' : LaneIdx}
    (h : instrToVM (.vecStoreLane p m a l) = instrToVM (.vecStoreLane p' m' a' l')) :
    Instr.vecStoreLane p m a l = .vecStoreLane p' m' a' l' := by
  have h' : p = p' ∧ m = m' ∧ a = a' ∧ Vec.laneIdxV l = Vec.laneIdxV l' := by
    simpa only [instrToVM, vecMemV, Option.getD_some, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, szV_eq_iff, toValue_eq_iff, memargV_eq_iff, true_and, and_true] using h
  rw [h'.1, h'.2.1, h'.2.2.1, laneIdxV_inj h'.2.2.2]

/-- Two memory SIMD instructions with equal `instrToVM` images have equal heads. -/
theorem head_eq_of_instrToVM {i j : Instr} (hi : memSimd i = true)
    (h : instrToVM i = instrToVM j) : Typing.instrHead j = Typing.instrHead i := by
  obtain ⟨op, w, hc⟩ : ∃ op w, instrToVM i = .case op w := by
    cases i <;> simp only [memSimd, Bool.false_eq_true] at hi <;> exact ⟨_, _, rfl⟩
  have hop : op = Typing.instrHead i := Round7.MemSimd.instrToVM_case_memSimd hi hc
  have hop' : op = Typing.instrHead j := instrToVM_head (h ▸ hc)
  rw [← hop, ← hop']

/-- **A memory SIMD instruction is determined by its `instrToVM` image.** -/
theorem instrToVM_inj_memSimd {i j : Instr} (hi : memSimd i = true)
    (h : instrToVM i = instrToVM j) : i = j := by
  have hh : Typing.instrHead j = Typing.instrHead i := head_eq_of_instrToVM hi h
  rcases head_memSimd hi with hd | hd | hd | hd
  · obtain ⟨o, m, a, rfl⟩ := vecLoad_of_head hd
    obtain ⟨o', m', a', rfl⟩ := vecLoad_of_head (hh.trans hd)
    exact vecLoad_inj h
  · obtain ⟨p, m, a, l, rfl⟩ := vecLoadLane_of_head hd
    obtain ⟨p', m', a', l', rfl⟩ := vecLoadLane_of_head (hh.trans hd)
    exact vecLoadLane_inj h
  · obtain ⟨m, a, rfl⟩ := vecStore_of_head hd
    obtain ⟨m', a', rfl⟩ := vecStore_of_head (hh.trans hd)
    exact vecStore_inj h
  · obtain ⟨p, m, a, l, rfl⟩ := vecStoreLane_of_head hd
    obtain ⟨p', m', a', l', rfl⟩ := vecStoreLane_of_head (hh.trans hd)
    exact vecStoreLane_inj h

/-! ## `instrToVD` -/

/-- The four block forms, or none of them. -/
theorem instr_blockCases (j : Instr) :
    (∃ bt b, j = .block bt b) ∨ (∃ bt b, j = .loop bt b) ∨ (∃ bt b₁ b₂, j = .if_ bt b₁ b₂) ∨
      (∃ bt cs b, j = .tryTable bt cs b) ∨
      ((∀ bt b, j = .block bt b → False) ∧ (∀ bt b, j = .loop bt b → False) ∧
        (∀ bt b₁ b₂, j = .if_ bt b₁ b₂ → False) ∧ (∀ bt cs b, j = .tryTable bt cs b → False)) := by
  cases j <;> simp

/-- An instruction that is not a block form has no `instrToVM` image with a block head. -/
theorem instrToVM_ne_block {i : Instr} (h₁ : ∀ bt b, i = .block bt b → False)
    (h₂ : ∀ bt b, i = .loop bt b → False) (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False)
    (h₄ : ∀ bt cs b, i = .tryTable bt cs b → False) {j : Instr}
    (hj : (∃ bt b, j = .block bt b) ∨ (∃ bt b, j = .loop bt b) ∨ (∃ bt b₁ b₂, j = .if_ bt b₁ b₂) ∨
      (∃ bt cs b, j = .tryTable bt cs b)) :
    instrToVM i ≠ instrToVD j := by
  intro h
  rcases hj with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ | ⟨bt, cs, b, rfl⟩
  · obtain ⟨bt', b', rfl⟩ := block_of_head (instrToVM_head h).symm
    exact h₁ _ _ rfl
  · obtain ⟨bt', b', rfl⟩ := loop_of_head (instrToVM_head h).symm
    exact h₂ _ _ rfl
  · obtain ⟨bt', c₁, c₂, rfl⟩ := if_of_head (instrToVM_head h).symm
    exact h₃ _ _ _ rfl
  · obtain ⟨bt', cs', b', rfl⟩ := tryTable_of_head (instrToVM_head h).symm
    exact h₄ _ _ _ rfl

/-- The motive of `instrToVD_inj_and` at an instruction. -/
abbrev InjI (G : Value → Prop) (i : Instr) : Prop :=
  ∀ j, G (instrToVD i) → instrToVD i = instrToVD j → i = j

/-- The motive of `instrToVD_inj_and` at a sequence. -/
abbrev InjL (G : Value → Prop) (b : List Instr) : Prop :=
  ∀ b', (∀ v ∈ instrsToVD b, G v) → instrsToVD b = instrsToVD b' → b = b'

theorem inj_block {G : Value → Prop} (hG : GoodV G) (bt : BlockType) (body : List Instr)
    (ih : InjL G body) : InjI G (.block bt body) := by
  intro j hg h
  obtain ⟨bt', b', rfl⟩ := block_of_head (instrToVD_head j h.symm).symm
  have h' : bt = bt' ∧ instrsToVD body = instrsToVD b' := by
    simpa only [instrToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, toValue_eq_iff, true_and, and_true] using h
  rw [h'.1, ih b' (hG.block _ _ hg) h'.2]

theorem inj_loop {G : Value → Prop} (hG : GoodV G) (bt : BlockType) (body : List Instr)
    (ih : InjL G body) : InjI G (.loop bt body) := by
  intro j hg h
  obtain ⟨bt', b', rfl⟩ := loop_of_head (instrToVD_head j h.symm).symm
  have h' : bt = bt' ∧ instrsToVD body = instrsToVD b' := by
    simpa only [instrToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, toValue_eq_iff, true_and, and_true] using h
  rw [h'.1, ih b' (hG.loop _ _ hg) h'.2]

theorem inj_if {G : Value → Prop} (hG : GoodV G) (bt : BlockType) (b₁ b₂ : List Instr)
    (ih₁ : InjL G b₁) (ih₂ : InjL G b₂) : InjI G (.if_ bt b₁ b₂) := by
  intro j hg h
  obtain ⟨bt', c₁, c₂, rfl⟩ := if_of_head (instrToVD_head j h.symm).symm
  have h' : bt = bt' ∧ instrsToVD b₁ = instrsToVD c₁ ∧ instrsToVD b₂ = instrsToVD c₂ := by
    simpa only [instrToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, toValue_eq_iff, true_and, and_true] using h
  rw [h'.1, ih₁ c₁ (hG.ifThen _ _ _ hg) h'.2.1, ih₂ c₂ (hG.ifElse _ _ _ hg) h'.2.2]

theorem inj_tryTable {G : Value → Prop} (hG : GoodV G) (bt : BlockType) (cs : List Catch)
    (body : List Instr) (ih : InjL G body) : InjI G (.tryTable bt cs body) := by
  intro j hg h
  obtain ⟨bt', cs', b', rfl⟩ := tryTable_of_head (instrToVD_head j h.symm).symm
  have h' : bt = bt' ∧ cs = cs' ∧ instrsToVD body = instrsToVD b' := by
    simpa only [instrToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, toValue_eq_iff, Round5.FwdRef2.map_toValue_eq_iff, true_and,
      and_true] using h
  rw [h'.1, h'.2.1, ih b' (hG.tryTable _ _ _ hg) h'.2.2]

/-- Two instructions that are not block forms, with equal `instrToVM` images and a good image,
are equal. -/
theorem inj_vm {G : Value → Prop} (hG : GoodV G) {i j : Instr} (hg : G (instrToVM i))
    (h : instrToVM i = instrToVM j) : i = j := by
  cases hm : memSimd i with
  | true => exact instrToVM_inj_memSimd hm h
  | false =>
    cases hm' : memSimd j with
    | true => exact (instrToVM_inj_memSimd hm' h.symm).symm
    | false =>
      have hv : instrToV i = instrToV j := by
        rw [← Round6.MemSimd.instrToVM_of_not hm, ← Round6.MemSimd.instrToVM_of_not hm', h]
      have hg' : G (instrToV i) := Round6.MemSimd.instrToVM_of_not hm ▸ hg
      exact Round5.FwdRef2.instrToV_inj hG hg' hv

theorem inj_other {G : Value → Prop} (hG : GoodV G) (i : Instr)
    (h₁ : ∀ bt b, i = .block bt b → False) (h₂ : ∀ bt b, i = .loop bt b → False)
    (h₃ : ∀ bt b₁ b₂, i = .if_ bt b₁ b₂ → False) (h₄ : ∀ bt cs b, i = .tryTable bt cs b → False) :
    InjI G i := by
  intro j hg h
  have e : instrToVD i = instrToVM i := instrToVD.eq_5 i h₁ h₂ h₃ h₄
  rcases instr_blockCases j with hj | hj | hj | hj | ⟨k₁, k₂, k₃, k₄⟩
  · exact absurd (e ▸ h) (instrToVM_ne_block h₁ h₂ h₃ h₄ (.inl hj))
  · exact absurd (e ▸ h) (instrToVM_ne_block h₁ h₂ h₃ h₄ (.inr (.inl hj)))
  · exact absurd (e ▸ h) (instrToVM_ne_block h₁ h₂ h₃ h₄ (.inr (.inr (.inl hj))))
  · exact absurd (e ▸ h) (instrToVM_ne_block h₁ h₂ h₃ h₄ (.inr (.inr (.inr hj))))
  · have e' : instrToVD j = instrToVM j := instrToVD.eq_5 j k₁ k₂ k₃ k₄
    exact inj_vm hG (e ▸ hg) (e.symm.trans (h.trans e'))

theorem inj_nil {G : Value → Prop} : InjL G [] := by
  intro b' _ h
  cases b' with
  | nil => rfl
  | cons _ _ => simp [instrsToVD] at h

theorem inj_cons {G : Value → Prop} (i : Instr) (is : List Instr) (ih₁ : InjI G i)
    (ih₂ : InjL G is) : InjL G (i :: is) := by
  intro b' hg h
  cases b' with
  | nil => simp [instrsToVD] at h
  | cons k b'' =>
    have h' : instrToVD i = instrToVD k ∧ instrsToVD is = instrsToVD b'' := by
      simpa only [instrsToVD, List.cons.injEq] using h
    have hg₁ : G (instrToVD i) := hg _ (by simp [instrsToVD])
    have hg₂ : ∀ v ∈ instrsToVD is, G v := fun v hv => hg v (by simp [instrsToVD, hv])
    rw [ih₁ k hg₁ h'.1, ih₂ b'' hg₂ h'.2]

/-- **`instrToVD` and `instrsToVD` are injective at good images.** -/
theorem instrToVD_inj_and {G : Value → Prop} (hG : GoodV G) :
    (∀ i : Instr, InjI G i) ∧ (∀ b : List Instr, InjL G b) :=
  instrToVD.mutual_induct (InjI G) (InjL G) (inj_block hG) (inj_loop hG) (inj_if hG)
    (inj_tryTable hG) (inj_other hG) inj_nil inj_cons

/-- **`instrsToVD` is injective at typed images.** -/
theorem instrsToVD_inj_typed {B : Builtins} {b b' : List Instr}
    (hb : ∀ v ∈ instrsToVD b, InstrG B v) (h : instrsToVD b = instrsToVD b') : b = b' :=
  (instrToVD_inj_and (goodV_typed B)).2 b b' hb h

/-! ## Function instances and stores -/

/-- The `CODE` field of `funcInstVD`. -/
def funcInstCodeVD (hn : H → String) : FuncCode H → Value
  | .wasm fn => .case "FUNC" (.tuple [pctV fn.type.toNat,
      .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
      .list (instrsToVD fn.body)])
  | .host h => .case "_HOSTFUNC" (.text (hn h))

theorem funcInstVD_eq' (hn : H → String) (ty : _) (m : ModuleInst) (c : FuncCode H) :
    funcInstVD hn ⟨ty, m, c⟩ = .struct [("TYPE", CT.defType ty),
      ("MODULE", moduleInstToValue CT m), ("CODE", funcInstCodeVD hn c)] := by
  cases c <;> rfl

/-- The body of a function instance with a typed `funcInstVD` image is typed. -/
theorem body_typedD {B : Builtins} {hn : H → String} {ty m fn}
    (hf : HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstVD hn ⟨ty, m, .wasm fn⟩)) :
    ∀ v ∈ instrsToVD fn.body, InstrG B v := by
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_funcinst hf
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  obtain ⟨cs, htd, hfc⟩ := Round5.FwdRef2.findTyp_funccode (B := B)
  have hc := IntNumeric.hasTyp_of_hasTypCase (Typing.hasTypCase_of_closedVariant htd hF.2.2.1) hfc
  exact Round5.FwdRef2.instrs_elems ⟨rfl, rfl, rfl⟩
    (Round5.FwdRef2.hasTyp_expr_inv ⟨rfl, rfl, rfl⟩ (Round5.FwdRef2.tup3_inv hc).2)

/-- Function code is determined by its `funcInstCodeVD` image, given a typed body. -/
theorem codeVD_inj {B : Builtins} {hn : H → String} (hinj : Function.Injective hn)
    {c c' : FuncCode H} (hb : ∀ fn, c = .wasm fn → ∀ v ∈ instrsToVD fn.body, InstrG B v)
    (h : funcInstCodeVD hn c = funcInstCodeVD hn c') : c = c' := by
  cases c with
  | wasm fn =>
      show FuncCode.wasm fn = c'
      cases c' with
      | wasm fn' =>
          show FuncCode.wasm fn = .wasm fn'
          obtain ⟨t, ls, body⟩ := fn
          obtain ⟨t', ls', body'⟩ := fn'
          have h' : t.toNat = t'.toNat ∧ ls.map (fun t => Value.case "LOCAL" (Encode.toValue t)) =
              ls'.map (fun t => Value.case "LOCAL" (Encode.toValue t)) ∧
              instrsToVD body = instrsToVD body' := by
            simpa only [funcInstCodeVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
              Value.list.injEq, Round5.FwdRef2.pctV_eq_iff, true_and, and_true] using h
          have hl : ls = ls' := List.map_injective_iff.2 (fun a b hab => by simpa using hab) h'.2.1
          have hbd : body = body' := instrsToVD_inj_typed (hb _ rfl) h'.2.2
          rw [Silmaril.Wasm.Idx.toNat_injective h'.1, hl, hbd]
      | host _ => simp [funcInstCodeVD] at h
  | host x =>
      cases c' with
      | wasm _ => simp [funcInstCodeVD] at h
      | host x' =>
          have hx : hn x = hn x' := by simpa [funcInstCodeVD] using h
          rw [hinj hx]

/-- `funcInstVD` is injective at a typed image. -/
theorem funcInstVD_inj_typed {B : Builtins} {hn : H → String} (hinj : Function.Injective hn)
    {f f' : FuncInst H}
    (hf : HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstVD hn f))
    (h : funcInstVD hn f = funcInstVD hn f') : f = f' := by
  obtain ⟨ty, m, code⟩ := f
  obtain ⟨ty', m', code'⟩ := f'
  have h' : CT.defType ty = CT.defType ty' ∧ moduleInstToValue CT m = moduleInstToValue CT m' ∧
      funcInstCodeVD hn code = funcInstCodeVD hn code' := by
    rw [funcInstVD_eq', funcInstVD_eq'] at h
    simpa only [Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] using h
  have hb : ∀ fn, code = .wasm fn → ∀ v ∈ instrsToVD fn.body, InstrG B v := by
    rintro fn rfl
    exact body_typedD hf
  rw [CT.defType_inj h'.1, moduleInstToValue_inj CT h'.2.1, codeVD_inj hinj hb h'.2.2]

/-- The function instances of a store with a typed `storeVD` image are typed. -/
theorem funcs_typedD {B : Builtins} {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeVD hn s)) :
    ∀ f ∈ s.funcs, HasTyp (simEnv B) VarEnv.empty (.varT "funcinst" []) (funcInstVD hn f) := by
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty ConfigOk.findTyp_store'
    (hs _ ConfigOk.valsOnly_empty)
  have hfu : HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "funcinst" []) .list)
      (.list (s.funcs.map (funcInstVD hn))) := by
    simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
    exact hF.2.2.2.2.1
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 hfu
  intro f hf
  exact hasTypList_iff.1 hall _ (by rw [← Value.list.inj hl]; exact List.mem_map_of_mem hf)

/-- **`storeVD` is injective on stores with typed images**, for an injective host naming. -/
theorem storeVD_inj_typed {B : Builtins} {hn : H → String} (hinj : Function.Injective hn)
    {s s' : Store H} (hs : TypedV (simEnv B) storeT (storeVD hn s))
    (h : storeVD hn s = storeVD hn s') : s = s' := by
  have hft := funcs_typedD hs
  obtain ⟨tg, gl, me, ta, fu, da, el, st, ar, ex⟩ := s
  obtain ⟨tg', gl', me', ta', fu', da', el', st', ar', ex'⟩ := s'
  have h' : tg.map (tagInstToValue CT) = tg'.map (tagInstToValue CT) ∧
      gl.map globalInstV = gl'.map globalInstV ∧ me.map memInstToValue = me'.map memInstToValue ∧
      ta.map (tableInstToValue CT) = ta'.map (tableInstToValue CT) ∧
      fu.map (funcInstVD hn) = fu'.map (funcInstVD hn) ∧
      da.map dataInstToValue = da'.map dataInstToValue ∧
      el.map (elemInstToValue CT) = el'.map (elemInstToValue CT) ∧
      st.map structInstV = st'.map structInstV ∧ ar.map arrayInstV = ar'.map arrayInstV ∧
      ex.map exnInstV = ex'.map exnInstV := by
    simpa only [storeVD, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq, Value.list.injEq,
      true_and, and_true] using h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h'
  have hfu : fu = fu' := Round5.FwdRef2.map_inj_on
    (fun f hf f' hff => funcInstVD_inj_typed hinj (hft f hf) hff) h₅
  rw [List.map_injective_iff.2 (tagInstToValue_inj CT) h₁,
    List.map_injective_iff.2 Round5.FwdRef2.globalInstV_inj h₂,
    List.map_injective_iff.2 memInstToValue_inj h₃,
    List.map_injective_iff.2 (tableInstToValue_inj CT) h₄, hfu,
    List.map_injective_iff.2 dataInstToValue_inj h₆,
    List.map_injective_iff.2 (elemInstToValue_inj CT) h₇,
    List.map_injective_iff.2 Round5.FwdRef2.structInstV_inj h₈,
    List.map_injective_iff.2 Round5.FwdRef2.arrayInstV_inj h₉,
    List.map_injective_iff.2 Round5.FwdRef2.exnInstV_inj h₁₀]

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD
