module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeSubjRed
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdS

/-!
# Nesting under `ctxt-instrs`, `LABEL_` and `FRAME_`: one forward theorem

Pass 5 proved the forward 2.0 half on the top-level fragment `TopVStep20`, one value-prefix/suffix
context above it (`Task.wholeStepCtxS20'`), and the lifting lemmas `fwdS_label`/`fwdS_frame` with
explicit typing hypotheses. This module closes the fragment under all three evaluation contexts
of V2's `Step` (`ctxtInstrs`, `ctxtLabel`, `ctxtFrame`), at any depth, and proves one forward
theorem for it.

* **Typing inversions and their converses** for the two block forms of the 2.0 `admininstr`
  (`Original.d295`): `typedV_adminLabel20_iff`, `typedV_adminFrame20_iff`. Both cases are
  premise-free, `LABEL_ n instr* admininstr*` and `FRAME_ n frame admininstr*`. With the
  elementwise typing of `admininstr*` (`typedV_admins_append20_iff`), a typed configuration is
  taken apart at each context and put back after the inner step.
* **`Nest20 R`**: the closure of a step relation `R` under the three contexts, with V2's own side
  condition on `ctxt-instrs`. `Nest20.step` embeds it in V2's `Step` when `R` does.
* **`FwdBase20 B hn W R`**: what a base fragment must provide. Subject reduction for the image,
  and a forward step of the corrected script from a typed image whose store satisfies `W`.
* **`fwd_nest20`**: from `FwdBase20`, every `Nest20 R` step from a typed image whose store
  satisfies `W` is a corrected step between the images, and its successor image is typed. The
  induction carries subject reduction through each context, so no successor hypothesis remains.
* `fwdBase20_topV`: the top-level fragment is a base, at `GrowCalls20` builtins with `W` the
  whole-pages condition. So **`Task.wholeStepNest20`** is stated and proved
  (`wholeStepNest20`): at `growB`, every `Nest20 TopVStep20` step is matched forward.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase recCases)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy valsTy sstepB20S_iff sstepS_ctxtInstrs)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d295)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Typing in a scope that binds values only -/

/-- A closed type name, from a value-only scope to every such scope. -/
theorem typedV_of_valsOnly20 {env : Env} {ρ : VarEnv} (hρ : Sim.ValsOnly ρ) {x : IL.Id}
    {v : Value} (h : HasTyp env ρ (.varT x []) v) : TypedV env (.varT x []) v :=
  fun _ hρ' => Sim.IntNumeric.hasTyp_varT_nil_congr hρ hρ' h

/-- A list over a closed type name, from a value-only scope to every such scope. -/
theorem typedV_list_of_valsOnly20 {env : Env} {ρ : VarEnv} (hρ : Sim.ValsOnly ρ) {x : IL.Id}
    {l : List Value} (h : HasTyp env ρ (.iterT (.varT x []) .list) (.list l)) :
    TypedV env (.iterT (.varT x []) .list) (.list l) := by
  obtain ⟨l', he, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := Value.list.inj he
  exact Sim.typedV_list_iff.2 fun u hu => typedV_of_valsOnly20 hρ (hasTypList_iff.1 hl u hu)

/-! ## The block forms of `admininstr` -/

/-- The payload of a typed `admininstr` case, at the case's declared type. -/
theorem hasTyp_adminCase20 {op : MixopS} {t : Typ} {prems : List Prem} {w : Value}
    (hf : findCase (recCases Original.d295 0 0) op = some (t, prems))
    (h : TypedV (simEnv20 B) (.varT "admininstr" []) (.case op w)) :
    HasTyp (simEnv20 B) VarEnv.empty t w := by
  obtain ⟨op', w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (hasTypDef_of_closed findTyp_admininstr20 (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  exact Sim.IntNumeric.hasTyp_of_hasTypCase hc hf

/-- A typed three-component tuple `n; τ; admininstr*`, taken apart. -/
theorem hasTyp_tup3_inv20 {env : Env} {a b c : IL.Id} {X Y : IL.Id} {τ : Typ} {u v : Value}
    {l : List Value}
    (h : HasTyp env VarEnv.empty (.tupT [.mk a (.varT X []), .mk b τ,
      .mk c (.iterT (.varT Y []) .list)]) (.tuple [u, v, .list l])) :
    TypedV env (.varT X []) u ∧ HasTyp env (VarEnv.empty.bindVal a u) τ v ∧
      TypedV env (.iterT (.varT Y []) .list) (.list l) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y₁, ys₁, h₁, hy₁, ht₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨y₂, ys₂, h₂, hy₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₂
  obtain ⟨y₃, ys₃, h₃, hy₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj h₃
  exact ⟨typedV_of_empty20 hy₁, hy₂, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ hy₃⟩

/-- A three-component tuple from typed components (the binders bind values only). -/
theorem hasTyp_tup3_mk20 {env : Env} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : TypedV env τ₁ u) (h₂ : TypedV env τ₂ v) (h₃ : TypedV env τ₃ w) :
    HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

theorem findCase_label20 : findCase (recCases Original.d295 0 0) "LABEL_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "instr*" instrsT, .mk "admininstr*" adminsTy], []) := rfl

theorem findCase_frame20 : findCase (recCases Original.d295 0 0) "FRAME_%{%}%" =
    some (.tupT [.mk "n" nT, .mk "frame" frameT, .mk "admininstr*" adminsTy], []) := rfl

/-- **A label is a typed `admininstr` exactly when its arity, continuation and body are typed.** -/
theorem typedV_adminLabel20_iff {n : Nat} {cont : List Silmaril.Wasm.V2.Instr} {body : List Admin} :
    TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (.label n cont body)) ↔
      TypedV (simEnv20 B) nT (.num (.natN n)) ∧
        TypedV (simEnv20 B) instrsT (.list (instrsToV cont)) ∧
        TypedV (simEnv20 B) adminsTy (.list (adminsToV body)) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := hasTyp_tup3_inv20 (hasTyp_adminCase20 findCase_label20 h)
    exact ⟨h₁, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact Pure.typedV_closedCase20 findTyp_admininstr20 findCase_label20 (hasTyp_tup3_mk20 h₁ h₂ h₃)

/-- **A frame is a typed `admininstr` exactly when its arity, frame and body are typed.** -/
theorem typedV_adminFrame20_iff {n : Nat} {fr : Frame} {body : List Admin} :
    TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV (.frame n fr body)) ↔
      TypedV (simEnv20 B) nT (.num (.natN n)) ∧ TypedV (simEnv20 B) frameT (frameV fr) ∧
        TypedV (simEnv20 B) adminsTy (.list (adminsToV body)) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := hasTyp_tup3_inv20 (hasTyp_adminCase20 findCase_frame20 h)
    exact ⟨h₁, typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact Pure.typedV_closedCase20 findTyp_admininstr20 findCase_frame20 (hasTyp_tup3_mk20 h₁ h₂ h₃)

/-! ## `admininstr*`, elementwise -/

theorem typedV_admins_single20_iff {a : Admin} :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV [a])) ↔
      TypedV (simEnv20 B) (.varT "admininstr" []) (adminToV a) := by
  simp [Sim.typedV_list_iff, adminsToV]

theorem typedV_admins_append20_iff {l₁ l₂ : List Admin} :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV (l₁ ++ l₂))) ↔
      TypedV (simEnv20 B) adminsTy (.list (adminsToV l₁)) ∧
        TypedV (simEnv20 B) adminsTy (.list (adminsToV l₂)) := by
  simp only [Pure.adminsToV_append, Sim.typedV_list_iff, List.mem_append]
  exact ⟨fun h => ⟨fun u hu => h u (.inl hu), fun u hu => h u (.inr hu)⟩,
    fun ⟨h₁, h₂⟩ u hu => hu.elim (h₁ u) (h₂ u)⟩

/-! ## The nested fragment -/

/-- **The closure of `R` under V2's three evaluation contexts**, `ctxt-instrs` (with V2's side
condition), `ctxt-label` and `ctxt-frame`, at any depth. -/
inductive Nest20 (R : Config H → Config H → Prop) : Config H → Config H → Prop where
  | base {c c' : Config H} (h : R c c') : Nest20 R c c'
  | ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : Nest20 R ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
      Nest20 R ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  | label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Silmaril.Wasm.V2.Instr}
      {is is' : List Admin} (h : Nest20 R ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Nest20 R ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  | frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Nest20 R ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Nest20 R ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩

/-- Every step of the closure is a V2 step when every base step is. -/
theorem Nest20.step {P : Profile} {host : HostSemantics H} {R : Config H → Config H → Prop}
    (hR : ∀ c c', R c c' → Step P host c c') {c c' : Config H} (h : Nest20 R c c') :
    Step P host c c' := by
  induction h with
  | base h => exact hR _ _ h
  | ctx _ hne ih => exact .ctxtInstrs ih hne
  | label _ ih => exact .ctxtLabel ih
  | frame _ ih => exact .ctxtFrame ih

/-- The closure is monotone in its base. -/
theorem Nest20.mono {R R' : Config H → Config H → Prop} (hR : ∀ c c', R c c' → R' c c')
    {c c' : Config H} (h : Nest20 R c c') : Nest20 R' c c' := by
  induction h with
  | base h => exact .base (hR _ _ h)
  | ctx _ hne ih => exact .ctx ih hne
  | label _ ih => exact .label ih
  | frame _ ih => exact .frame ih

/-- **A base fragment for the forward half**: subject reduction for the image, and a forward
step of the corrected script from a typed image whose store satisfies `W`. -/
structure FwdBase20 (B : Builtins) (hn : H → String) (W : Store H → Prop)
    (R : Config H → Config H → Prop) : Prop where
  sr : ∀ c c', Typed20 (simEnv20 B) hn c → R c c' → Typed20 (simEnv20 B) hn c'
  fwd : ∀ c c', Typed20 (simEnv20 B) hn c → W c.store → R c c' →
    SStepB (simEnv20S B) (configV hn c) (configV hn c')

/-- The union of two base fragments is a base fragment. -/
theorem FwdBase20.or {W : Store H → Prop} {R R' : Config H → Config H → Prop}
    (h : FwdBase20 B hn W R) (h' : FwdBase20 B hn W R') :
    FwdBase20 B hn W (fun c c' => R c c' ∨ R' c c') where
  sr c c' hc hr := hr.elim (h.sr c c' hc) (h'.sr c c' hc)
  fwd c c' hc hw hr := hr.elim (h.fwd c c' hc hw) (h'.fwd c c' hc hw)

/-- A base fragment under a stronger store condition. -/
theorem FwdBase20.weaken {W W' : Store H → Prop} {R : Config H → Config H → Prop}
    (h : FwdBase20 B hn W R) (hW : ∀ s, W' s → W s) : FwdBase20 B hn W' R where
  sr := h.sr
  fwd c c' hc hw hr := h.fwd c c' hc (hW _ hw) hr

/-! ## The three contexts, one at a time -/

/-- `ctxt-instrs`: the typing of the outer configuration splits, and the inner step lifts. -/
theorem fwdNest_ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (hc : Typed20 (simEnv20 B) hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : Typed20 (simEnv20 B) hn ⟨s, f, is⟩ → Typed20 (simEnv20 B) hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    Typed20 (simEnv20 B) hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
  obtain ⟨hvi, hrest⟩ := typedV_admins_append20_iff.1 hcode
  obtain ⟨hvals, his⟩ := typedV_admins_append20_iff.1 hvi
  obtain ⟨hc', hst⟩ := ih (typed20_iff.2 ⟨hz, his⟩)
  obtain ⟨hz', his'⟩ := typed20_iff.1 hc'
  refine ⟨typed20_iff.2 ⟨hz', typedV_admins_append20_iff.2
    ⟨typedV_admins_append20_iff.2 ⟨hvals, his'⟩, hrest⟩⟩, ?_⟩
  have hvs : TypedV (simEnv20S B) valsTy (.list (adminsToV (vals vs))) := by
    rw [Pure.adminsToV_vals]
    exact (typAgreeS B).vals _ (typedV_vals20 vs)
  have hs := sstepS_ctxtInstrs (typedV_state20S hz) (typedV_state20S hz') hvs
    (typedV_admins20S his) (typedV_admins20S his') (typedV_admins20S hrest)
    (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20S_iff B).1 hst)
  refine (sstepB20S_iff B).2 ?_
  simpa only [configV, Pure.adminsToV_append] using hs

/-- `ctxt-label`: the label's typing inverts, and the inner step lifts. -/
theorem fwdNest_label {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List Silmaril.Wasm.V2.Instr} {is is' : List Admin}
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, [.label n cont is]⟩)
    (ih : Typed20 (simEnv20 B) hn ⟨s, f, is⟩ → Typed20 (simEnv20 B) hn ⟨s', f', is'⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    Typed20 (simEnv20 B) hn ⟨s', f', [.label n cont is']⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
  obtain ⟨hn', hcont, his⟩ := typedV_adminLabel20_iff.1 (typedV_admins_single20_iff.1 hcode)
  have hin : Typed20 (simEnv20 B) hn ⟨s, f, is⟩ := typed20_iff.2 ⟨hz, his⟩
  obtain ⟨hc', hst⟩ := ih hin
  obtain ⟨hz', his'⟩ := typed20_iff.1 hc'
  exact ⟨typed20_iff.2 ⟨hz', typedV_admins_single20_iff.2
    (typedV_adminLabel20_iff.2 ⟨hn', hcont, his'⟩)⟩, fwdS_label hin hc' hn' hcont hst⟩

/-- `ctxt-frame`: the frame's typing inverts; the inner configuration runs under the inner frame
and the outer frame is kept. -/
theorem fwdNest_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, [.frame n fi is]⟩)
    (ih : Typed20 (simEnv20 B) hn ⟨s, fi, is⟩ → Typed20 (simEnv20 B) hn ⟨s', fi', is'⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    Typed20 (simEnv20 B) hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStepB (simEnv20S B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
  obtain ⟨hs, hf⟩ := typedV_stateV_iff.1 hz
  obtain ⟨hn', hfi, his⟩ := typedV_adminFrame20_iff.1 (typedV_admins_single20_iff.1 hcode)
  obtain ⟨hc', hst⟩ := ih (typed20_iff.2 ⟨typedV_stateV_iff.2 ⟨hs, hfi⟩, his⟩)
  obtain ⟨hz', his'⟩ := typed20_iff.1 hc'
  obtain ⟨hs', hfi'⟩ := typedV_stateV_iff.1 hz'
  exact ⟨typed20_iff.2 ⟨typedV_stateV_iff.2 ⟨hs', hf⟩, typedV_admins_single20_iff.2
    (typedV_adminFrame20_iff.2 ⟨hn', hfi', his'⟩)⟩,
    fwdS_frame hs hs' hf hfi hfi' hn' his his' hst⟩

/-! ## The forward theorem -/

/-- **The forward 2.0 half on a nested fragment**: from a base fragment, every step of its
closure under the three contexts, from a typed image whose store satisfies `W`, is a step of the
corrected script between the images, and the successor image is typed. -/
theorem fwd_nest20 {W : Store H → Prop} {R : Config H → Config H → Prop}
    (F : FwdBase20 B hn W R) {c c' : Config H} (h : Nest20 R c c')
    (hc : Typed20 (simEnv20 B) hn c) (hw : W c.store) :
    Typed20 (simEnv20 B) hn c' ∧ SStepB (simEnv20S B) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact ⟨F.sr _ _ hc h, F.fwd _ _ hc hw h⟩
  | ctx _ hne ih => exact fwdNest_ctx hne hc fun hin => ih hin hw
  | label _ ih => exact fwdNest_label hc fun hin => ih hin hw
  | frame _ ih => exact fwdNest_frame hc fun hin => ih hin hw

/-! ## The top-level fragment as a base -/

/-- **The top-level fragment is a base**, at `GrowCalls20` builtins, under whole pages. -/
theorem fwdBase20_topV {P : Profile} (hG : GrowCalls20 B) :
    FwdBase20 B hn WholePages (TopVStep20 (H := H) P) where
  sr _ _ hc h := typed20_of_topVStep20 hc h
  fwd _ _ hc hw h := by
    obtain ⟨k, hk, hf⟩ := fires_topVStep20 hG hc hw h
    exact sstepB20S_of_fires (stepAgreeS B k hk _ hf)

/-- **The forward 2.0 half on the nested top-level fragment** (stated and proved): at `growB`,
every step of `Nest20 TopVStep20` from a configuration with typed image and whole pages is a step
of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepNest20 : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c → WholePages c.store →
    Nest20 (TopVStep20 (Profile.spec nd r)) c c' →
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c' ∧
      SStepB (simEnv20S (growB (Profile.spec nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeStepNest20` is proved.** -/
theorem wholeStepNest20 : Task.wholeStepNest20 :=
  fun _ _ _ _ _ _ hc hw h => fwd_nest20 (fwdBase20_topV (growCalls20_growB _)) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
