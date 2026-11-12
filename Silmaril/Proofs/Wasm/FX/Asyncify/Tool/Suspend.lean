module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.ResumeChain

/-!
# A suspension: the source asks the host; the target unwinds, the host answers, the target rewinds
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

theorem LocR.recOf {P : Prog} {fn : FnSrc} {sl tl : List W} (h : LocR P fn sl tl) (k : Nat)
    (hF : fn.nloc + 1 ≤ P.frameWords) : LocR P fn sl (Silmaril.Wasm.FX.Asyncify.Tool.recOf P.frameWords k tl) := by
  obtain ⟨hl, ex, rfl, hex⟩ := h
  refine ⟨hl, ex.take (P.frameWords - 1 - fn.nloc) ++ [BitVec.ofNat 32 k], ?_, ?_⟩
  · simp only [Silmaril.Wasm.FX.Asyncify.Tool.recOf, List.take_append, hl, List.append_assoc]
    rw [List.take_of_length_le (by omega)]
  · simp; omega

theorem WaitR.restore {P : Prog} {above k : Nat} {fs ft : Frame} (h : WaitR P above k fs ft) :
    WaitR P above k fs { ft with locals := recOf P.frameWords k ft.locals } := by
  cases h with
  | mk hfn hloc hst hf =>
    exact .mk hfn (hloc.recOf _ (Prog.fnOk_nloc hfn)) hst hf
where
  Prog.fnOk_nloc {P : Prog} {fid : Nat} {fn : FnSrc} (h : P.fnAt fid = some fn) :
      fn.nloc + 1 ≤ P.frameWords := Prog.nloc_lt (Prog.fnAt_mem h)

theorem Chain.restore {P : Prog} {above e : Nat} {ks : List Nat} {sw tw : List Frame}
    (h : Chain P above e ks sw tw) : Chain P above e ks sw (restore P.frameWords ks tw) := by
  induction h with
  | nil e => exact .nil e
  | cons hw _ ih => exact .cons hw.restore ih

theorem Chain.len {P : Prog} (hP : P.WF) {above e : Nat} {ks : List Nat} {sw tw : List Frame}
    (h : Chain P above e ks sw tw) :
    sw.length = tw.length ∧ ∀ w ∈ tw, w.locals.length = P.frameWords := by
  induction h with
  | nil e => simp
  | cons hw _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro w hw'
    simp only [List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · cases hw with
      | mk hfn hloc _ _ => exact hloc.len (Prog.fnOk hP hfn).nloc
    · exact ih.2 w hw'

theorem step_call_imp {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {f : FuncIdx}
    {K : List Instr} (hf : c.frames = fr :: rest) (hcode : fr.code = .call f :: K)
    (himp : f.value.val < E.imps.length) (hn : E.imps[f.value.val].1 ≤ fr.ops.length) :
    step E c = .ask f.value.val (fr.ops.take E.imps[f.value.val].1).reverse
      ⟨{ fr with ops := fr.ops.drop E.imps[f.value.val].1, code := K } :: rest, c.globals, c.mem⟩ := by
  simp [step, hf, hcode, exec, ctlOf, himp, hn, Cfg.setTop]

end Silmaril.Wasm.FX.Asyncify.Tool
