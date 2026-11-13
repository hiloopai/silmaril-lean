module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Aggregate

/-!
# Exception renaming: the forward simulation of Core 3.0 steps

`step_rn`: every host-free Core step `c ~> c'` is matched, from the renamed configuration
`rnCfg n c t` over an `ExnRen n c.store t` target store, by one step to `rnCfg n c' t'` with
`ExnRen n c'.store t'`. The leaf families are `Leaf`/`Aggregate`; this module does the
structural and control rules and the four contexts:

* `throw` allocates at `s.exns.length` in the source and at `t.exns.length = rnIdx n
  s.exns.length` in the target (`exns_length_rn`), and the new instances correspond
  (`addExn_rn`);
* `throw_ref` reads the exception at `a` in the source and at `rnIdx n a` in the target
  (`exns_rn`), so the handler clauses that match are the same (`catchMatches_rn_back`);
* calls keep their function addresses; the frame of a call holds the renamed arguments
  (`rnFrame_forCall`); host calls do not exist (`noHost`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {n : Nat}

/-- The renamed configuration over the store `t`. -/
def rnCfg (n : Nat) (c : Config H) (t : Store H) : Config H :=
  ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩

theorem rnAdmins_eq_nil {l : List Admin} : rnAdmins n l = [] ↔ l = [] := by
  cases l <;> simp

theorem rnAdmins_ne_nil {l : List Admin} : rnAdmins n l ≠ [] ↔ l ≠ [] :=
  not_congr rnAdmins_eq_nil

theorem rnAdmin_of_isCallRef {c : Admin} (hc : c.IsCallRef) : rnAdmin n c = c := by
  cases c with
  | plain i => rfl
  | callRefType d => rfl
  | _ => exact hc.elim

theorem rnAdmin_of_isReturnCallRef {c : Admin} (hc : c.IsReturnCallRef) : rnAdmin n c = c := by
  cases c with
  | plain i => rfl
  | returnCallRefType d => rfl
  | _ => exact hc.elim

theorem rnAdmin_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    rnAdmin n (c.retToCallIn m) = c.retToCallIn m := by
  cases c with
  | plain i =>
    cases i <;> try rfl
    simp only [Admin.retToCallIn]
    split <;> rfl
  | returnCallRefType d => rfl
  | _ => exact hc.elim

theorem rnVal_ne_null {v : Val} (hv : v ≠ .ref .null) : rnVal n v ≠ .ref .null := by
  cases v with
  | ref r =>
    rw [rnVal_ref, Ne, Val.ref.injEq, rnRef_eq_null]
    exact fun h => hv (by rw [h])
  | num _ => exact fun h => by cases h
  | vec _ => exact fun h => by cases h

@[simp] theorem rnAdmins_throwing (a : Nat) : rnAdmins n (throwing a) = throwing (rnIdx n a) :=
  rfl

theorem catchMatches_rn_back {s t : Store H} (h : ExnRen n s t) {f : Frame} {a : Nat}
    {c : Catch} (hm : CatchMatches t (rnFrame n f) (rnIdx n a) c) : CatchMatches s f a c := by
  cases c with
  | catch_ x l =>
    obtain ⟨e, ta, he, ht, hta⟩ := hm
    rw [exns_rn h, Option.map_eq_some_iff] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨e', ta, he', ht, hta⟩
  | catchRef x l =>
    obtain ⟨e, ta, he, ht, hta⟩ := hm
    rw [exns_rn h, Option.map_eq_some_iff] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨e', ta, he', ht, hta⟩
  | catchAll l => trivial
  | catchAllRef l => trivial

theorem ctxtInstrs_rn {s s' t t' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin}
    (ht : Step P noHost (rnCfg n ⟨s, f, is⟩ t) (rnCfg n ⟨s', f', is'⟩ t'))
    (hne : vs ≠ [] ∨ rest ≠ []) :
    Step P noHost (rnCfg n ⟨s, f, vals vs ++ is ++ rest⟩ t)
      (rnCfg n ⟨s', f', vals vs ++ is' ++ rest⟩ t') := by
  have hne' : vs.map (rnVal n) ≠ [] ∨ rnAdmins n rest ≠ [] := by
    simpa [rnAdmins_ne_nil] using hne
  have hs := Step.ctxtInstrs (vs := vs.map (rnVal n)) (rest := rnAdmins n rest) ht hne'
  simpa only [rnCfg, rnAdmins_append', rnAdmins_vals'] using hs

/-- **The forward simulation, one step.** -/
theorem step_rn {c c' : Config H} (hs : Step P noHost c c') :
    ∀ {t : Store H}, ExnRen n c.store t →
      ∃ t', Step P noHost (rnCfg n c t) (rnCfg n c' t') ∧ ExnRen n c'.store t' := by
  induction hs with
  | parametric hp =>
    intro t h
    exact ⟨t, .parametric (Silmaril.Proofs.Wasm.Models.FXRename.parametric_rn n hp), h⟩
  | numeric hp =>
    intro t h
    exact ⟨t, .numeric (Silmaril.Proofs.Wasm.Models.FXRename.numeric_rn n hp), h⟩
  | vector hp =>
    intro t h
    exact ⟨t, .vector (Silmaril.Proofs.Wasm.Models.FXRename.vector_rn n hp), h⟩
  | @«variable» c c' hv =>
    intro t h
    obtain ⟨s, f, code⟩ := c; obtain ⟨s', f', out⟩ := c'
    obtain ⟨t', ht, h'⟩ := variable_rn h hv
    exact ⟨t', .variable ht, h'⟩
  | @table c c' hv =>
    intro t h
    obtain ⟨s, f, code⟩ := c; obtain ⟨s', f', out⟩ := c'
    obtain ⟨t', ht, h'⟩ := table_rn' h hv
    exact ⟨t', .table ht, h'⟩
  | @memory c c' hv =>
    intro t h
    obtain ⟨s, f, code⟩ := c; obtain ⟨s', f', out⟩ := c'
    obtain ⟨t', ht, h'⟩ := memory_rn h hv
    exact ⟨t', .memory ht, h'⟩
  | @reference c c' hv =>
    intro t h
    obtain ⟨s, f, code⟩ := c; obtain ⟨s', f', out⟩ := c'
    obtain ⟨t', ht, h'⟩ := reference_rn h hv
    exact ⟨t', .reference ht, h'⟩
  | @aggregate c c' hv =>
    intro t h
    obtain ⟨s, f, code⟩ := c; obtain ⟨s', f', out⟩ := c'
    obtain ⟨t', ht, h'⟩ := aggregate_rn h hv
    exact ⟨t', .aggregate ht, h'⟩
  | ctxtInstrs _ hne ih =>
    intro t h
    obtain ⟨t', ht, h'⟩ := ih h
    exact ⟨t', ctxtInstrs_rn ht hne, h'⟩
  | ctxtLabel _ ih =>
    intro t h
    obtain ⟨t', ht, h'⟩ := ih h
    exact ⟨t', .ctxtLabel ht, h'⟩
  | ctxtHandler _ ih =>
    intro t h
    obtain ⟨t', ht, h'⟩ := ih h
    exact ⟨t', .ctxtHandler ht, h'⟩
  | ctxtFrame _ ih =>
    intro t h
    obtain ⟨t', ht, h'⟩ := ih h
    exact ⟨t', .ctxtFrame ht, h'⟩
  | block hbt hm =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .block hbt (by simpa using hm)
  | loop hbt hm =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .loop hbt (by simpa using hm)
  | ifTrue hc => intro t h; exact ⟨t, .ifTrue hc, h⟩
  | ifFalse => intro t h; exact ⟨t, .ifFalse, h⟩
  | labelVals => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .labelVals
  | brLabelZero hl hn =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brLabelZero hl (by simpa using hn)
  | brLabelSucc hl =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .brLabelSucc hl
  | brHandler => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .brHandler
  | brIfTrue hc => intro t h; exact ⟨t, .brIfTrue hc, h⟩
  | brIfFalse => intro t h; exact ⟨t, .brIfFalse, h⟩
  | brTableLt hi => intro t h; exact ⟨t, .brTableLt hi, h⟩
  | brTableGe hi => intro t h; exact ⟨t, .brTableGe hi, h⟩
  | brOnNullNull => intro t h; exact ⟨t, .brOnNullNull, h⟩
  | brOnNullAddr hv =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnNullAddr (rnVal_ne_null hv)
  | brOnNonNullNull => intro t h; exact ⟨t, .brOnNonNullNull, h⟩
  | brOnNonNullAddr hv =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnNonNullAddr (rnVal_ne_null hv)
  | brOnCastSucceed hr =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnCastSucceed (refOk_rn h hr)
  | brOnCastFail hr =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnCastFail (fun hr' => hr (refOk_rn_back h hr'))
  | brOnCastFailSucceed hr =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnCastFailSucceed (refOk_rn h hr)
  | brOnCastFailFail hr =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .brOnCastFailFail (fun hr' => hr (refOk_rn_back h hr'))
  | call hx hf =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .call hx (funcs_rn h hf)
  | callRefNull hc =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isCallRef hc]
    exact .callRefNull hc
  | callRefFunc hc hf he hn hcode =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isCallRef hc, rnFrame_forCall]
    exact .callRefFunc hc (funcs_rn h hf) he (by simpa using hn) hcode
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall hx hf =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .returnCall hx (funcs_rn h hf)
  | returnCallRefLabel hc =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isReturnCallRef hc]
    exact .returnCallRefLabel hc
  | returnCallRefHandler hc =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isReturnCallRef hc]
    exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isReturnCallRef hc]
    exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    rw [rnAdmin_of_isReturnCallRef hc, rnAdmin_retToCallIn hc]
    exact .returnCallRefFrameAddr hc (funcs_rn h hf) he (by simpa using hn)
  | callIndirect => intro t h; exact ⟨t, .callIndirect, h⟩
  | returnCallIndirect => intro t h; exact ⟨t, .returnCallIndirect, h⟩
  | frameVals hn =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .frameVals (by simpa using hn)
  | returnFrame hn =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .returnFrame (by simpa using hn)
  | returnLabel => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .returnLabel
  | returnHandler =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .returnHandler
  | @throw s f x vs ta ti ts ht he hn =>
    intro t h
    refine ⟨_, ?_, addExn_rn h ⟨ta, vs⟩⟩
    simp only [rnCfg]; rn_simp
    rw [← exns_length_rn h]
    exact .throw (tag_rn h ht) he (by simpa using hn)
  | throwRefNull => intro t h; exact ⟨t, .throwRefNull, h⟩
  | throwRefInstrs hne =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .throwRefInstrs (by simpa [rnAdmins_ne_nil] using hne)
  | throwRefLabel => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .throwRefLabel
  | throwRefFrame => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .throwRefFrame
  | throwRefHandlerEmpty =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .throwRefHandlerEmpty
  | @throwRefHandlerCatch s f k x l cs a e he ht =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .throwRefHandlerCatch (e := rnExn n e) (by rw [exns_rn h, he]; rfl) ht
  | @throwRefHandlerCatchRef s f k x l cs a e he ht =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .throwRefHandlerCatchRef (e := rnExn n e) (by rw [exns_rn h, he]; rfl) ht
  | throwRefHandlerCatchAll =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext hm =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .throwRefHandlerNext (fun hm' => hm (catchMatches_rn_back h hm'))
  | tryTable hbt hm =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .tryTable hbt (by simpa using hm)
  | handlerVals => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .handlerVals
  | trapInstrs hne =>
    intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp
    exact .trapInstrs (by simpa [rnAdmins_ne_nil] using hne)
  | trapLabel => intro t h; exact ⟨t, .trapLabel, h⟩
  | trapHandler => intro t h; exact ⟨t, .trapHandler, h⟩
  | trapFrame => intro t h; refine ⟨t, ?_, h⟩; simp only [rnCfg]; rn_simp; exact .trapFrame

end Silmaril.Proofs.Wasm.Models.FXRenameSim
