module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.BackAggregate

/-!
# Exception renaming, backward: every host-free Core 3.0 step

`step_rn_back`: every step of the renamed configuration `rnCfg n c t` (over an `ExnRen n c.store
t` store) is the renamed image of a step of `c`. With `step_rn` this makes the renaming a
lock-step bisimulation.

The induction (`step_rn_back_of`) is over the target step, for every source configuration
`⟨s, f, L⟩` whose renaming is the step's source. Each arm reads the code back with `rn_inv` and
applies the same rule to the source. The arms that need more than one line are lemmas: the
leaf families (`BackLeaf`, `BackTable`, `BackAggregate`), the plain families (`parametric_step_rn_back` and the others),
the four contexts (`backStep_ctxtInstrs` and the others) and the handler rules that read an
exception back (`throwRefHandlerCatch_rn_back`).

Refined from the earlier `Silmaril.Raw.Wasm.Models.FXRenameSim.BackStep`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {n : Nat}

/-- The conclusion of the backward simulation. -/
def BackStep (P : Profile) (n : Nat) (c d : Config H) : Prop :=
  ∃ (c' : Config H) (t' : Store H), Step P noHost c c' ∧ d = rnCfg n c' t' ∧ ExnRen n c'.store t'

theorem backStep_intro {s s' t' : Store H} {f f' : Frame} {L L' : List Admin} {d : Config H}
    (hs : Step P noHost ⟨s, f, L⟩ ⟨s', f', L'⟩) (hd : d = ⟨t', rnFrame n f', rnAdmins n L'⟩)
    (h' : ExnRen n s' t') : BackStep P n ⟨s, f, L⟩ d :=
  ⟨⟨s', f', L'⟩, t', hs, hd, h'⟩

theorem backStep_of_backOf {R : Config H → Config H → Prop} {s : Store H} {f : Frame}
    {L : List Admin} {d : Config H} (hR : ∀ {c c'}, R c c' → Step P noHost c c')
    (h : BackOf R n s f L d) : BackStep P n ⟨s, f, L⟩ d := by
  obtain ⟨s', f', L', t', hs, hd, h'⟩ := h
  exact backStep_intro (hR hs) hd h'

theorem isCallRef_rn_back {a : Admin} (h : (rnAdmin n a).IsCallRef) :
    a.IsCallRef ∧ rnAdmin n a = a := by
  cases a with
  | plain i => exact ⟨h, rfl⟩
  | callRefType d => exact ⟨h, rfl⟩
  | _ => exact h.elim

theorem isReturnCallRef_rn_back {a : Admin} (h : (rnAdmin n a).IsReturnCallRef) :
    a.IsReturnCallRef ∧ rnAdmin n a = a := by
  cases a with
  | plain i => exact ⟨h, rfl⟩
  | returnCallRefType d => exact ⟨h, rfl⟩
  | _ => exact h.elim

theorem rnVal_ne_null_back {v : Val} (hv : rnVal n v ≠ .ref .null) : v ≠ .ref .null :=
  fun h => hv (by rw [h]; rfl)

theorem catchMatches_rn {s t : Store H} (h : ExnRen n s t) {f : Frame} {a : Nat} {c : Catch}
    (hm : CatchMatches s f a c) : CatchMatches t (rnFrame n f) (rnIdx n a) c := by
  cases c with
  | catch_ x l =>
    obtain ⟨e, ta, he, ht, hta⟩ := hm
    exact ⟨rnExn n e, ta, by rw [exns_rn h, he]; rfl, ht, hta⟩
  | catchRef x l =>
    obtain ⟨e, ta, he, ht, hta⟩ := hm
    exact ⟨rnExn n e, ta, by rw [exns_rn h, he]; rfl, ht, hta⟩
  | catchAll l => trivial
  | catchAllRef l => trivial

theorem rnAdmins_plain_back : ∀ {L : List Admin},
    Silmaril.Proofs.Wasm.Models.FXRename.PlainCode (rnAdmins n L) → rnAdmins n L = L
  | [], _ => rfl
  | .plain i :: L, h => by
    rw [rnAdmins_cons, rnAdmin_plain, rnAdmins_plain_back (L := L) h]
  | .trap :: L, h => by
    rw [rnAdmins_cons, rnAdmin_trap, rnAdmins_plain_back (L := L) h]
  | .label .. :: _, h => h.elim
  | .handler .. :: _, h => h.elim
  | .frame .. :: _, h => h.elim
  | .ref _ :: _, h => h.elim
  | .callRefType _ :: _, h => h.elim
  | .returnCallRefType _ :: _, h => h.elim

theorem parametric_rn_back {L is' : List Admin} (hp : ParametricStep (rnAdmins n L) is') :
    ∃ L', ParametricStep L L' ∧ is' = rnAdmins n L' := by
  generalize hc : rnAdmins n L = c at hp
  cases hp with
  | unreachable => rn_inv hc; exact ⟨_, .unreachable, by rn_fin⟩
  | nop => rn_inv hc; exact ⟨_, .nop, by rn_fin⟩
  | drop v => rn_inv hc; exact ⟨_, .drop _, by rn_fin⟩
  | selectTrue hc' => rn_inv hc; exact ⟨_, .selectTrue hc', by rn_fin⟩
  | selectFalse v₁ v₂ ts => rn_inv hc; exact ⟨_, .selectFalse _ _ ts, by rn_fin⟩

theorem rnCfg_inj {t' t₀ : Store H} {f' : Frame} {is' : List Admin} {c : Config H}
    (hd : (⟨t', f', is'⟩ : Config H) = rnCfg n c t₀) :
    t' = t₀ ∧ f' = rnFrame n c.frame ∧ is' = rnAdmins n c.code :=
  Config.mk.inj hd

theorem rnExn_tag (e : ExnInst) : (rnExn n e).tag = e.tag := rfl

/-! ## Contexts -/

theorem backStep_ctxtInstrs {s : Store H} {f : Frame} {L : List Admin} {vs : List Val}
    {rest : List Admin} {t' : Store H} {f' : Frame} {is' : List Admin} (hb : BackStep P n ⟨s, f, L⟩ ⟨t', f', is'⟩)
    (hne : vs.map (rnVal n) ≠ [] ∨ rnAdmins n rest ≠ []) :
    BackStep P n ⟨s, f, vals vs ++ L ++ rest⟩
      ⟨t', f', vals (vs.map (rnVal n)) ++ is' ++ rnAdmins n rest⟩ := by
  obtain ⟨⟨s', f₀, L'⟩, t₀, hs, hd, h'⟩ := hb
  have hne' : vs ≠ [] ∨ rest ≠ [] := by simpa [rnAdmins_ne_nil] using hne
  have hd' : (⟨t', f', vals (vs.map (rnVal n)) ++ is' ++ rnAdmins n rest⟩ : Config H) =
      ⟨t₀, rnFrame n f₀, rnAdmins n (vals vs ++ L' ++ rest)⟩ := by
    obtain ⟨h₁, h₂, h₃⟩ := rnCfg_inj hd
    rw [h₁, h₂, h₃]; rn_simp
  exact backStep_intro (.ctxtInstrs hs hne') hd' h'

theorem backStep_ctxtLabel {s : Store H} {f : Frame} {L : List Admin} {k : Nat}
    {cont : List Instr} {t' : Store H} {f' : Frame} {is' : List Admin} (hb : BackStep P n ⟨s, f, L⟩ ⟨t', f', is'⟩) :
    BackStep P n ⟨s, f, [.label k cont L]⟩ ⟨t', f', [.label k cont is']⟩ := by
  obtain ⟨⟨s', f₀, L'⟩, t₀, hs, hd, h'⟩ := hb
  have hd' : (⟨t', f', [.label k cont is']⟩ : Config H) =
      ⟨t₀, rnFrame n f₀, rnAdmins n [.label k cont L']⟩ := by
    obtain ⟨h₁, h₂, h₃⟩ := rnCfg_inj hd
    rw [h₁, h₂, h₃]; rn_simp
  exact backStep_intro (.ctxtLabel hs) hd' h'

theorem backStep_ctxtHandler {s : Store H} {f : Frame} {L : List Admin} {k : Nat}
    {cs : List Catch} {t' : Store H} {f' : Frame} {is' : List Admin} (hb : BackStep P n ⟨s, f, L⟩ ⟨t', f', is'⟩) :
    BackStep P n ⟨s, f, [.handler k cs L]⟩ ⟨t', f', [.handler k cs is']⟩ := by
  obtain ⟨⟨s', f₀, L'⟩, t₀, hs, hd, h'⟩ := hb
  have hd' : (⟨t', f', [.handler k cs is']⟩ : Config H) =
      ⟨t₀, rnFrame n f₀, rnAdmins n [.handler k cs L']⟩ := by
    obtain ⟨h₁, h₂, h₃⟩ := rnCfg_inj hd
    rw [h₁, h₂, h₃]; rn_simp
  exact backStep_intro (.ctxtHandler hs) hd' h'

theorem backStep_ctxtFrame {s : Store H} {f fi : Frame} {L : List Admin} {k : Nat}
    {t' : Store H} {fi' : Frame} {is' : List Admin}
    (hb : BackStep P n ⟨s, fi, L⟩ ⟨t', fi', is'⟩) :
    BackStep P n ⟨s, f, [.frame k fi L]⟩ ⟨t', rnFrame n f, [.frame k fi' is']⟩ := by
  obtain ⟨⟨s', f₀, L'⟩, t₀, hs, hd, h'⟩ := hb
  have hd' : (⟨t', rnFrame n f, [.frame k fi' is']⟩ : Config H) =
      ⟨t₀, rnFrame n f, rnAdmins n [.frame k f₀ L']⟩ := by
    obtain ⟨h₁, h₂, h₃⟩ := rnCfg_inj hd
    rw [h₁, h₂, h₃]; rn_simp
  exact backStep_intro (.ctxtFrame hs) hd' h'

section Back

variable {s t : Store H} {f : Frame} {L : List Admin} (h : ExnRen n s t)
include h

/-! ## The plain families -/

theorem parametric_step_rn_back {is' : List Admin} (hp : ParametricStep (rnAdmins n L) is') :
    BackStep P n ⟨s, f, L⟩ ⟨t, rnFrame n f, is'⟩ := by
  obtain ⟨L', hL', hL⟩ := parametric_rn_back hp
  exact backStep_intro (.parametric hL') (by rw [hL]) h

/-- Numeric steps rewrite plain code (no references), which the renaming fixes. -/
theorem numeric_step_rn_back {is' : List Admin} (hp : NumericStep P (rnAdmins n L) is') :
    BackStep P n ⟨s, f, L⟩ ⟨t, rnFrame n f, is'⟩ := by
  have hpl := Silmaril.Proofs.Wasm.Models.FXRename.numeric_plain hp
  have hL : rnAdmins n L = L := rnAdmins_plain_back hpl.1
  have hp₀ : NumericStep P L is' := hL ▸ hp
  exact backStep_intro (.numeric hp₀) (by rw [Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_plain hpl.2]) h

/-- Vector steps rewrite plain code, which the renaming fixes. -/
theorem vector_step_rn_back {is' : List Admin} (hp : VectorStep P (rnAdmins n L) is') :
    BackStep P n ⟨s, f, L⟩ ⟨t, rnFrame n f, is'⟩ := by
  have hpl := Silmaril.Proofs.Wasm.Models.FXRename.vector_plain hp
  have hL : rnAdmins n L = L := rnAdmins_plain_back hpl.1
  have hp₀ : VectorStep P L is' := hL ▸ hp
  exact backStep_intro (.vector hp₀) (by rw [Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_plain hpl.2]) h

/-! ## Handler rules that read an exception -/

theorem throwRefHandlerCatch_rn_back {k : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {a : Nat} {e : ExnInst} (he : t.exns[rnIdx n a]? = some e)
    (ht : (rnFrame n f).module.tags[x.toNat]? = some e.tag) :
    BackStep P n ⟨s, f, [.handler k (.catch_ x l :: cs) (throwing a)]⟩
      ⟨t, rnFrame n f, vals e.fields ++ [.plain (.br l)]⟩ := by
  obtain ⟨e₀, he₀, hee⟩ := exns_rn_back h he
  have ht₀ : f.module.tags[x.toNat]? = some e₀.tag := by
    rw [← rnExn_tag (n := n), hee]; exact ht
  exact backStep_intro (.throwRefHandlerCatch he₀ ht₀) (by rw [← hee]; rn_fin) h

theorem throwRefHandlerCatchRef_rn_back {k : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    {a : Nat} {e : ExnInst} (he : t.exns[rnIdx n a]? = some e)
    (ht : (rnFrame n f).module.tags[x.toNat]? = some e.tag) :
    BackStep P n ⟨s, f, [.handler k (.catchRef x l :: cs) (throwing a)]⟩
      ⟨t, rnFrame n f, vals e.fields ++ [.ref (.exn (rnIdx n a)), .plain (.br l)]⟩ := by
  obtain ⟨e₀, he₀, hee⟩ := exns_rn_back h he
  have ht₀ : f.module.tags[x.toNat]? = some e₀.tag := by
    rw [← rnExn_tag (n := n), hee]; exact ht
  exact backStep_intro (.throwRefHandlerCatchRef he₀ ht₀) (by rw [← hee]; rn_fin) h

end Back

/-- **The backward simulation, one step**, for every source configuration `⟨s, f, L⟩` whose
renaming is the source of the step. -/
theorem step_rn_back_of {e d : Config H} (hs : Step P noHost e d) :
    ∀ {s : Store H} {f : Frame} {L : List Admin} {t : Store H}, ExnRen n s t →
      (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = e → BackStep P n ⟨s, f, L⟩ d := by
  induction hs with
  | parametric hp => intro s f L t h hq; rn_inv hq; exact parametric_step_rn_back h hp
  | numeric hp => intro s f L t h hq; rn_inv hq; exact numeric_step_rn_back h hp
  | vector hp => intro s f L t h hq; rn_inv hq; exact vector_step_rn_back h hp
  | «variable» hv =>
    intro s f L t h hq
    exact backStep_of_backOf (fun h => .variable h) (variable_rn_back_of h hv hq)
  | table hv =>
    intro s f L t h hq
    exact backStep_of_backOf (fun h => .table h) (table_rn_back_of h hv hq)
  | memory hv =>
    intro s f L t h hq
    exact backStep_of_backOf (fun h => .memory h) (memory_rn_back_of h hv hq)
  | reference hv =>
    intro s f L t h hq
    exact backStep_of_backOf (fun h => .reference h) (reference_rn_back_of h hv hq)
  | aggregate hv =>
    intro s f L t h hq
    exact backStep_of_backOf (fun h => .aggregate h) (aggregate_rn_back_of h hv hq)
  | ctxtInstrs _ hne ih =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_ctxtInstrs (ih h rfl) hne
  | ctxtLabel _ ih => intro s f L t h hq; rn_inv hq; exact backStep_ctxtLabel (ih h rfl)
  | ctxtHandler _ ih => intro s f L t h hq; rn_inv hq; exact backStep_ctxtHandler (ih h rfl)
  | ctxtFrame _ ih => intro s f L t h hq; rn_inv hq; exact backStep_ctxtFrame (ih h rfl)
  | block hbt hm =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.block hbt (by simpa using hm)) (by rn_fin) h
  | loop hbt hm =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.loop hbt (by simpa using hm)) (by rn_fin) h
  | ifTrue hc =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.ifTrue hc) (by rn_fin) h
  | ifFalse =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .ifFalse (by rn_fin) h
  | labelVals =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .labelVals (by rn_fin) h
  | brLabelZero hl hn =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brLabelZero hl (by simp)) (by rn_fin) h
  | brLabelSucc hl =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brLabelSucc hl) (by rn_fin) h
  | brHandler =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .brHandler (by rn_fin) h
  | brIfTrue hc =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brIfTrue hc) (by rn_fin) h
  | brIfFalse =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .brIfFalse (by rn_fin) h
  | brTableLt hi =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brTableLt hi) (by rn_fin) h
  | brTableGe hi =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brTableGe hi) (by rn_fin) h
  | brOnNullNull =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .brOnNullNull (by rn_fin) h
  | brOnNullAddr hv =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnNullAddr (rnVal_ne_null_back hv)) (by rn_fin) h
  | brOnNonNullNull =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .brOnNonNullNull (by rn_fin) h
  | brOnNonNullAddr hv =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnNonNullAddr (rnVal_ne_null_back hv)) (by rn_fin) h
  | brOnCastSucceed hr =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnCastSucceed (refOk_rn_back h hr)) (by rn_fin) h
  | brOnCastFail hr =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnCastFail (fun hr' => hr (refOk_rn h hr'))) (by rn_fin) h
  | brOnCastFailSucceed hr =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnCastFailSucceed (refOk_rn_back h hr)) (by rn_fin) h
  | brOnCastFailFail hr =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.brOnCastFailFail (fun hr' => hr (refOk_rn h hr'))) (by rn_fin) h
  | call hx hf =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.call hx (funcs_rn_back h hf)) (by rn_fin) h
  | callRefNull hc =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, hc₁⟩ := isCallRef_rn_back hc
    exact backStep_intro (.callRefNull hc₀) (by rn_fin) h
  | callRefFunc hc hf he hn hcode =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, hc₁⟩ := isCallRef_rn_back hc
    refine backStep_intro (.callRefFunc hc₀ (funcs_rn_back h hf) he (by simpa using hn) hcode) ?_ h
    rn_simp
    rw [rnFrame_forCall]
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall hx hf =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.returnCall hx (funcs_rn_back h hf)) (by rn_fin) h
  | returnCallRefLabel hc =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, hc₁⟩ := isReturnCallRef_rn_back hc
    exact backStep_intro (.returnCallRefLabel hc₀) (by rn_fin) h
  | returnCallRefHandler hc =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, hc₁⟩ := isReturnCallRef_rn_back hc
    exact backStep_intro (.returnCallRefHandler hc₀) (by rn_fin) h
  | returnCallRefFrameNull hc =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, -⟩ := isReturnCallRef_rn_back hc
    exact backStep_intro (.returnCallRefFrameNull hc₀) (by rn_fin) h
  | returnCallRefFrameAddr hc hf he hn =>
    intro s f L t h hq
    rn_inv hq
    obtain ⟨hc₀, hc₁⟩ := isReturnCallRef_rn_back hc
    refine backStep_intro (.returnCallRefFrameAddr hc₀ (funcs_rn_back h hf) he (by simpa using hn)) ?_ h
    rn_simp
    rw [hc₁, rnAdmin_retToCallIn hc₀]
    rfl
  | callIndirect =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .callIndirect (by rn_fin) h
  | returnCallIndirect =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .returnCallIndirect (by rn_fin) h
  | frameVals hn =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.frameVals (by simp)) (by rn_fin) h
  | returnFrame hn =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.returnFrame (by simp)) (by rn_fin) h
  | returnLabel =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .returnLabel (by rn_fin) h
  | returnHandler =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .returnHandler (by rn_fin) h
  | throw ht he hn =>
    intro s f L t h hq
    rn_inv hq
    refine backStep_intro (.throw (tag_rn_back h ht) he (by simpa using hn)) ?_ (addExn_rn h _)
    rw [exns_length_rn h]
    rn_fin
  | throwRefNull =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefNull (by rn_fin) h
  | throwRefInstrs hne =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.throwRefInstrs (by simpa [rnAdmins_ne_nil] using hne)) (by rn_fin) h
  | throwRefLabel =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefLabel (by rn_fin) h
  | throwRefFrame =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefFrame (by rn_fin) h
  | throwRefHandlerEmpty =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefHandlerEmpty (by rn_fin) h
  | throwRefHandlerCatch he ht =>
    intro s f L t h hq
    rn_inv hq
    exact throwRefHandlerCatch_rn_back h he ht
  | throwRefHandlerCatchRef he ht =>
    intro s f L t h hq
    rn_inv hq
    exact throwRefHandlerCatchRef_rn_back h he ht
  | throwRefHandlerCatchAll =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefHandlerCatchAll (by rn_fin) h
  | throwRefHandlerCatchAllRef =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .throwRefHandlerCatchAllRef (by rn_fin) h
  | throwRefHandlerNext hm =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.throwRefHandlerNext (fun hm' => hm (catchMatches_rn h hm'))) (by rn_fin) h
  | tryTable hbt hm =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.tryTable hbt (by simpa using hm)) (by rn_fin) h
  | handlerVals =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .handlerVals (by rn_fin) h
  | trapInstrs hne =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro (.trapInstrs (by simpa [rnAdmins_ne_nil] using hne)) (by rn_fin) h
  | trapLabel =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .trapLabel (by rn_fin) h
  | trapHandler =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .trapHandler (by rn_fin) h
  | trapFrame =>
    intro s f L t h hq
    rn_inv hq
    exact backStep_intro .trapFrame (by rn_fin) h



/-- **The backward simulation, one step.** -/
theorem step_rn_back {e d : Config H} (hs : Step P noHost e d) :
    ∀ {c : Config H} {t : Store H}, ExnRen n c.store t → rnCfg n c t = e → BackStep P n c d := by
  intro c t h hq
  exact step_rn_back_of hs h hq

end Silmaril.Proofs.Wasm.Models.FXRenameSim
