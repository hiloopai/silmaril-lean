module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# Round 5, pass 2, track read: `ConfigOk` and `Bounded` give `ReadValidS`

* `segOk_of_instrOk`, `codeSeg_of_ok`: a valid aggregate instruction's segment index resolves
  (its typing rule looks the segment up in the context, which `StateOk` resolves), at every depth
  of valid code, by the recursion of `Round4Int.adminsIdx_of_ok`.
* `readValidS_of_bounded`: a valid, bounded configuration satisfies `ReadValidS`.
* `readValidS_ctxClosed`: `ReadValidS` survives the context decompositions of the backward
  recursion.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Read (CtxClosed)
open Round4Int (CtxRes)

variable {H : Type} {s : Store H}

/-- A storage type whose unpacked type is numeric or vector has a positive `$zsize`. -/
theorem storageSize_pos_of_numOrVec : ∀ {z : CStorageType}, z.unpack.IsNumOrVec →
    0 < storageSize z
  | .val (.num (.int t)), _ => by cases t <;> decide
  | .val (.num (.float t)), _ => by cases t <;> decide
  | .val (.vec _), _ => by simp [storageSize]
  | .pack p, _ => by cases p <;> decide

/-- **A valid instruction's aggregate indices resolve**, in a context whose indices resolve and
whose types are the frame module's. -/
theorem segOk_of_instrOk {f : Frame} {C : Context} {i : Instr} {it : InstrType}
    (R : CtxRes s f C) (hT : C.types = f.module.types) (h : InstrOk C i it) :
    Instr.SegOk s f i := by
  cases i <;> try trivial
  case arrayNewDefault x =>
    obtain ⟨d, m, z, hd, he, hdef⟩ : ∃ d m z, C.type? x = some d ∧
        Expand d (.array (.field m z)) ∧ Defaultable z.unpack := by
      cases h <;> rename_i h <;> cases h
      exact ⟨_, _, _, by assumption, by assumption, by assumption⟩
    refine ⟨d, m, z, ?_, he, (defaultVal?_isSome_iff _).2 hdef⟩
    simpa [Context.type?, Frame.type?, hT] using hd
  case arrayNewData x y =>
    obtain ⟨d, m, z, hd, he, hnv, hy⟩ : ∃ d m z, C.type? x = some d ∧
        Expand d (.array (.field m z)) ∧ z.unpack.IsNumOrVec ∧ C.datas[y.toNat]? = some () := by
      cases h <;> rename_i h <;> cases h
      exact ⟨_, _, _, by assumption, by assumption, by assumption, by assumption⟩
    exact ⟨R.data hy, d, m, z, by simpa [Context.type?, Frame.type?, hT] using hd, he,
      storageSize_pos_of_numOrVec hnv⟩
  case arrayInitData x y =>
    obtain ⟨d, z, hd, he, hnv, hy⟩ : ∃ d z, C.type? x = some d ∧
        Expand d (.array (.field .var z)) ∧ z.unpack.IsNumOrVec ∧ C.datas[y.toNat]? = some () := by
      cases h <;> rename_i h <;> cases h
      exact ⟨_, _, by assumption, by assumption, by assumption, by assumption⟩
    exact ⟨R.data hy, d, .var, z, by simpa [Context.type?, Frame.type?, hT] using hd, he,
      storageSize_pos_of_numOrVec hnv⟩
  all_goals (cases h <;> rename_i h <;> cases h)
  all_goals exact R.elem (by assumption)

/-- `codeSeg` along an append. -/
theorem codeSeg_append {f : Frame} :
    ∀ {l₁ l₂ : List Admin}, codeSeg s f (l₁ ++ l₂) ↔ codeSeg s f l₁ ∧ codeSeg s f l₂
  | [], _ => by simp [codeSeg]
  | _ :: _, _ => by simp [codeSeg, codeSeg_append, and_assoc]

mutual
/-- **Every aggregate segment index of a valid administrative instruction resolves**, at every
depth. -/
theorem adminSeg_of_ok (hS : StoreOk s) :
    ∀ {f : Frame} {C : Context} {a : Admin} {it : InstrType}, CtxRes s f C →
      C.types = f.module.types → AdminOk s C a it → adminSeg s f a
  | _, _, _, _, R, hT, .plain h => segOk_of_instrOk R hT h
  | _, _, _, _, _, _, .callRefType _ _ => trivial
  | _, _, _, _, _, _, .returnCallRefType _ _ _ _ _ => trivial
  | _, _, _, _, _, _, .ref _ => trivial
  | _, C, _, _, R, hT, .label (t' := t') _ _ hb =>
    codeSeg_of_ok hS (R.of_frameView (C' := C.withLabel t') rfl) hT hb
  | _, _, _, _, _, _, .frame (C' := C') (ts := ts) hf _ hb _ =>
    codeSeg_of_ok hS ((Round4Int.ctxRes_of_stateOk ⟨hS, hf⟩).of_frameView
      (C' := { C' with return_ := some ts }) rfl) (StateOk.types (C := C') ⟨hS, hf⟩) hb
  | _, _, _, _, R, hT, .handler _ hb => codeSeg_of_ok hS R hT hb
  | _, _, _, _, _, _, .trap _ => trivial
  | _, _, _, _, _, _, .throwRefInits _ => trivial

/-- **Every aggregate segment index of valid code resolves**, at every depth. -/
theorem codeSeg_of_ok (hS : StoreOk s) :
    ∀ {f : Frame} {C : Context} {l : List Admin} {it : InstrType}, CtxRes s f C →
      C.types = f.module.types → AdminsOk s C l it → codeSeg s f l
  | _, _, _, _, _, _, .nil => trivial
  | _, _, _, _, R, hT, .single h => ⟨adminSeg_of_ok hS R hT h, trivial⟩
  | _, _, _, _, R, hT, .seq h₁ _ h₂ =>
    codeSeg_append.2 ⟨codeSeg_of_ok hS R hT h₁,
      codeSeg_of_ok hS (R.of_frameView (Context.initLocals_frameView _ _))
        ((congrArg (·.types) (Context.initLocals_frameView _ _)).trans hT) h₂⟩
  | _, _, _, _, R, hT, .cons ha _ hs =>
    ⟨adminSeg_of_ok hS R hT ha,
      codeSeg_of_ok hS (R.of_frameView (Context.initLocals_frameView _ _))
        ((congrArg (·.types) (Context.initLocals_frameView _ _)).trans hT) hs⟩
  | _, _, _, _, R, hT, .sub h _ _ => codeSeg_of_ok hS R hT h
  | _, _, _, _, R, hT, .frame h _ => codeSeg_of_ok hS R hT h
end

/-- **A valid, bounded configuration satisfies `ReadValidS`.** -/
theorem readValidS_of_bounded {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : Round4.Bounded c) : ReadValidS c := by
  have hr := Bwd.readValidR_of_bounded hc hb
  obtain ⟨C, hst, hcode⟩ := hc
  exact ⟨hr, codeSeg_of_ok hst.1 (Round4Int.ctxRes_of_stateOk hst) (StateOk.types hst) hcode, hb.code, hb.frame⟩

/-- **`ReadValidS` survives the context decompositions** of the backward recursion. -/
theorem readValidS_ctxClosed : CtxClosed (ReadValidS (H := H)) where
  mid s f a b c h := ⟨Bwd.readValidR_ctxClosed.mid s f a b c h.r,
    (codeSeg_append.1 (codeSeg_append.1 h.seg).1).2,
    (Round4.adminsBnd_append.1 (Round4.adminsBnd_append.1 h.bnd).1).2, h.frame⟩
  label s f n cont body h :=
    ⟨Bwd.readValidR_ctxClosed.label s f n cont body h.r, h.seg.1, h.bnd.1.2, h.frame⟩
  handler s f n cs body h :=
    ⟨Bwd.readValidR_ctxClosed.handler s f n cs body h.r, h.seg.1, h.bnd.1, h.frame⟩
  frame s f fi n body h :=
    ⟨Bwd.readValidR_ctxClosed.frame s f fi n body h.r, h.seg.1, h.bnd.1.2, h.bnd.1.1⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Read
