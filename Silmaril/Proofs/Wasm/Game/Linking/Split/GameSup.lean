module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Joint

/-!
# Static linking, separation: composition is simulated by the shared world

Original module documentation:

# The provider interacting with the consumer is the shared object: `⊇` (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

Every overlay play of the consumer's stateful plays run against the provider object
(`interact`, POPL 2022 P13) is a play of the shared object. The proof walks the consumer's play
and the provider's play together (their underlay and overlay projections agree), keeping the
invariant `GInv` between the game states of the three instances; host-free runs of the
consumer and of the provider are simulated by the shared world (`CRel.reach`, `PRel.reach`),
a call of the consumer into the provider is one `call_ref` step of the shared world
(`CRel.call`), and the provider's run from its `$invoke` is replaced by the run through that
canonical first step (`reach_of_step`, from the diamond `Internal.deterministic`).

Silmaril: the canonical first step is now justified for every profile by uniqueness of the first
step of an invocation (`InternalP.pending_unique`: it enters the callee's frame, no numeric
choice is involved), so `⊇` holds for an arbitrary profile.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking

/-! ### Interface helpers -/

theorem ifaceOp?_eq {ts : List FnType} {h : Nat} {args : List Val} {e : (ifaceSig ts).Op}
    (he : ifaceOp? ts h args = some e) : e.1.val = h ∧ e.2.1 = args := by
  unfold ifaceOp? at he
  split at he
  · split at he
    · cases he; exact ⟨rfl, rfl⟩
    · cases he
  · cases he

theorem ofResult?_values {ft : FnType} {vs : List Val} {v : Answer ft}
    (h : Answer.ofResult? ft (.values vs) = some v) :
    List.Forall₂ ScalarType.HasVal ft.results vs := by
  by_cases hv : List.Forall₂ ScalarType.HasVal ft.results vs
  · exact hv
  · simp [Answer.ofResult?, hv] at h

theorem ofResult?_toResult' {ft : FnType} {r : Result} {v : Answer ft}
    (h : Answer.ofResult? ft r = some v) : v.toResult = r := by
  cases r with
  | values vs =>
    by_cases hv : List.Forall₂ ScalarType.HasVal ft.results vs
    · simp only [Answer.ofResult?, hv, dite_true, Option.some.injEq] at h
      subst h; rfl
    · simp [Answer.ofResult?, hv] at h
  | trap => cases h; rfl
  | throw a => cases h; rfl

/-- Scalar results are not renamed. -/
theorem ren_result_of_ofResult? {ft : FnType} {r : Result} {v : Answer ft}
    (h : Answer.ofResult? ft r = some v) (ρ : Ren) : ρ.result r = r := by
  cases r with
  | values vs => simp [Ren.result, forall₂_hasVal_ren (ofResult?_values h) ρ]
  | trap => rfl
  | throw a => rfl

theorem emptySig_op_elim {α : Prop} (e : (ifaceSig []).Op) : α :=
  (ifaceSig_nil_op_isEmpty.false e).elim

/-! ### Plays of a closed instance -/

theorem path_idle_cons {I : ScalarInstance} {P : Profile} {s : Store Nat}
    {m : Move I.E I.F} {p : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.idle s) (m :: p) q) :
    ∃ f, m = .inr (.ask f) ∧ I.Path P (.running f s (I.initThread f)) p q := by
  generalize hq : (ScalarInstance.HState.idle s : I.HState) = q₀ at h
  generalize hl : m :: p = l at h
  cases h with
  | nil => cases hl
  | cons ht hp =>
    cases hl
    cases ht with
    | call s' f => cases hq; exact ⟨f, rfl, hp⟩
    | ucall _ _ _ => cases hq
    | uret _ => cases hq
    | oret _ _ _ => cases hq

theorem path_running_cons {I : ScalarInstance} (hI : I.imports = []) {P : Profile}
    {s : Store Nat} {f : I.F.Op} {t : Thread} {m : Move I.E I.F}
    {p : List (Move I.E I.F)} {q : I.HState}
    (h : I.Path P (.running f s t) (m :: p) q) :
    ∃ s' t' r v, m = .inr (.ans f v) ∧ Reach P (s, t) (s', t') ∧ ResultAt s' t' r ∧
      Answer.ofResult? (I.exports.get f.1) r = some v ∧ I.Path P (.idle s') p q := by
  generalize hq : (ScalarInstance.HState.running f s t : I.HState) = q₀ at h
  generalize hl : m :: p = l at h
  cases h with
  | nil => cases hl
  | cons ht hp =>
    cases hl
    cases ht with
    | call _ _ => cases hq
    | @ucall _ _ _ _ _ _ _ e _ _ _ =>
      exact absurd e.1.2 (by simp [ScalarInstance.E, hI])
    | uret _ => cases hq
    | oret run final answer =>
      cases hq
      exact ⟨_, _, _, _, rfl, run, final, answer, hp⟩

variable {S : Setup}

/-! ### The invariant between game states -/

/-- The invariant between the game states of the shared world, the provider and the consumer,
along their plays. -/
inductive GInv (St : Static S) (P : Profile) :
    S.sharedI.HState → S.providerI.HState → S.consumerI.HState → Prop where
  | idle {σ π κ : Store Nat} (h : Idle St σ π κ) : GInv St P (.idle σ) (.idle π) (.idle κ)
  | run {f : S.consumerI.F.Op} {σ₀ σ π κ : Store Nat} {ts₀ ts tc : Thread}
      (hr : Reach P (σ₀, ts₀) (σ, ts)) (h : CRel St σ ts π κ tc) :
      GInv St P (.running f σ₀ ts₀) (.idle π) (.running f κ tc)
  | wait {f : S.consumerI.F.Op} {σ₀ σ π κ : Store Nat} {ts₀ ts tc : Thread}
      {e : S.consumerI.E.Op} (hr : Reach P (σ₀, ts₀) (σ, ts)) (h : CRel St σ ts π κ tc)
      (hco : CalloutAt κ tc e.1 e.2.1) :
      GInv St P (.running f σ₀ ts₀) (.running e π (S.providerI.initThread e)) (.waiting f κ tc e)

/-- The provider's play answering the consumer's import question `e`: it starts with the export
question `e` and continues from the provider's invocation of `e`. -/
private theorem provider_after_ask {P : Profile} {π : Store Nat}
    {qp' : S.providerI.HState} {pp : List (Move S.providerI.E S.providerI.F)}
    {e : S.consumerI.E.Op} {l : List (Ev S.consumerI.E)}
    (hp : S.providerI.Path P (.idle π) pp qp')
    (hproj : (Ev.ask e :: l : List (Ev S.consumerI.E)) = upper pp) :
    ∃ pp', S.providerI.Path P (.running e π (S.providerI.initThread e)) pp' qp' ∧
      l = upper pp' := by
  cases pp with
  | nil => simp at hproj
  | cons m pp' =>
    obtain ⟨e', hm, hpp⟩ := path_idle_cons hp
    have hproj2 : (Ev.ask e :: l : List (Ev S.consumerI.E)) = Ev.ask e' :: upper pp' := by
      rw [hproj, hm]
      rfl
    have he : e = e' := Ev.ask.inj (List.cons.inj hproj2).1
    exact ⟨pp', he ▸ hpp, (List.cons.inj hproj2).2⟩

/-- The provider's play answering `v` to the export question `e`: a host-free run of the
provider to a result `r` whose answer is `v`, then the rest of the play. -/
private theorem provider_after_ans {P : Profile} {π : Store Nat}
    {qp' : S.providerI.HState} {pp : List (Move S.providerI.E S.providerI.F)}
    {e : S.consumerI.E.Op} {v : S.consumerI.E.Ar e} {l : List (Ev S.consumerI.E)}
    (hp : S.providerI.Path P (.running e π (S.providerI.initThread e)) pp qp')
    (hproj : (Ev.ans e v :: l : List (Ev S.consumerI.E)) = upper pp) :
    ∃ π' tp' r pp', Reach P (π, S.providerI.initThread e) (π', tp') ∧ ResultAt π' tp' r ∧
      Answer.ofResult? (S.providerI.exports.get e.1) r = some v ∧
      S.providerI.Path P (.idle π') pp' qp' ∧ l = upper pp' := by
  cases pp with
  | nil => simp at hproj
  | cons m pp' =>
    obtain ⟨π', tp', r, w, hm, run, final, answer, hpp⟩ :=
      path_running_cons (I := S.providerI) rfl hp
    have hproj2 : (Ev.ans e v :: l : List (Ev S.consumerI.E)) = Ev.ans e w :: upper pp' := by
      rw [hproj, hm]
      rfl
    have hvw : v = w := eq_of_heq (Ev.ans.inj (List.cons.inj hproj2).1).2
    exact ⟨π', tp', r, pp', run, final, hvw ▸ answer, hpp, (List.cons.inj hproj2).2⟩

/-- **`⊇`, core.** A consumer play against a provider play with matching projections is
simulated by the shared world. -/
theorem sup_core (St : Static S) (P : Profile) {qc qc' : S.consumerI.HState}
    {pc : List (Move S.consumerI.E S.consumerI.F)} (hc : S.consumerI.Path P qc pc qc') :
    ∀ {qp qp' : S.providerI.HState} {pp : List (Move S.providerI.E S.providerI.F)},
      S.providerI.Path P qp pp qp' → lower pc = upper pp →
      ∀ {qs : S.sharedI.HState}, GInv St P qs qp qc →
        ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper pc := by
  intro qp qp' pp hp hproj qs hg
  induction hc generalizing qp qp' pp qs with
  | nil q => exact ⟨[], qs, .nil _, rfl⟩
  | @cons q₁ q₂ q₃ m rest ht hrest ih =>
    show ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper (m :: rest)
    cases ht with
    | call κ f =>
      show ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper (.inr (.ask f) :: rest)
      cases hg with
      | @idle σ π _ hI =>
        have hproj' : lower rest = upper pp := by simpa using hproj
        have hg' : GInv St P (.running f σ (S.sharedI.initThread f)) (.idle π)
            (.running f κ (S.consumerI.initThread f)) := GInv.run .refl (hI.start f)
        obtain ⟨ps, qs', hps, hpf⟩ := ih hp hproj' hg'
        refine ⟨.inr (.ask f) :: ps, qs',
          .cons (ScalarInstance.Trans.call (I := S.sharedI) (P := P) σ f) hps, ?_⟩
        exact congrArg (List.cons (Ev.ask f)) hpf
    | @ucall f κ κ' tc tc' h args e run callout op =>
      show ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper (.inl (.ask e) :: rest)
      cases hg with
      | @run _ σ₀ σ π _ ts₀ ts _ hr hR =>
        obtain ⟨σ₁, ts₁, hr₁, hR₁⟩ := hR.reach run
        obtain ⟨h1, h2⟩ := ifaceOp?_eq op
        have hco : CalloutAt κ' tc' e.1 e.2.1 := by rw [h1, h2]; exact callout
        obtain ⟨pp', hpp, hproj'⟩ := provider_after_ask hp hproj
        obtain ⟨ps, qs', hps, hpf⟩ := ih hpp hproj' (GInv.wait (hr.trans hr₁) hR₁ hco)
        exact ⟨ps, qs', hps, by simpa using hpf⟩
    | @uret f κ tc e v =>
      show ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper (.inl (.ans e v) :: rest)
      cases hg with
      | @wait _ σ₀ σ π _ ts₀ ts _ _ hr hR hco =>
        show ∃ ps qs', S.sharedI.Path P (.running f σ₀ ts₀) ps qs' ∧
          upper ps = upper (.inl (.ans e v) :: rest)
        obtain ⟨π', tp', r, pp', run, final, answer, hpp, hproj'⟩ := provider_after_ans hp hproj
        -- the canonical first step of the provider
        obtain ⟨hlt, tp₀, ts₁, hp₀, hs₁, hP, -⟩ := hR.call (P := P) hco e.2.2
        have hrun : Reach P (π, tp₀) (π', tp') :=
          reach_of_unique_step (fun _ hy => InternalP.pending_unique hy hp₀) run
            (resultAt_no_internal final) hp₀
        obtain ⟨σ₂, ts₂, hr₂, hP₂⟩ := hP.reach hrun
        obtain ⟨-, hC⟩ := hP₂.ret final (fun vs hvs => ⟨_, ofResult?_values (hvs ▸ answer)⟩)
        have hC' : CRel St σ₂ ts₂ π' κ
            (resumeResult κ tc (Answer.toResult (ft := S.consumerI.imports.get e.1) v)) :=
          (ofResult?_toResult' answer).symm ▸ hC
        obtain ⟨ps, qs', hps, hpf⟩ :=
          ih hpp hproj' (GInv.run ((hr.tail hs₁).trans hr₂) hC')
        exact ⟨ps, qs', hps, by simpa using hpf⟩
    | @oret f κ κ' tc tc' r v run final answer =>
      show ∃ ps qs', S.sharedI.Path P qs ps qs' ∧ upper ps = upper (.inr (.ans f v) :: rest)
      cases hg with
      | @run _ σ₀ σ π _ ts₀ ts _ hr hR =>
        show ∃ ps qs', S.sharedI.Path P (.running f σ₀ ts₀) ps qs' ∧
          upper ps = upper (.inr (.ans f v) :: rest)
        obtain ⟨σ₁, ts₁, hr₁, hR₁⟩ := hR.reach run
        obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hR₁.result final
        have hres' : ResultAt σ₁ ts₁ r := by
          simpa only [ren_result_of_ofResult? answer ρ] using hres
        have hproj' : lower rest = upper pp := by simpa using hproj
        obtain ⟨ps, qs', hps, hpf⟩ := ih hp hproj' (GInv.idle hI)
        refine ⟨.inr (.ans f v) :: ps, qs',
          .cons (ScalarInstance.Trans.oret (I := S.sharedI) (hr.trans hr₁) hres' answer) hps, ?_⟩
        exact congrArg (List.cons (Ev.ans f v)) hpf

/-- **`⊇`.** The provider object interacting with the consumer's plays only plays plays of
the shared object. -/
theorem interact_subset (St : Static S) (P : Profile) :
    interact (S.providerI.objPlays P S.sp) (S.consumerI.plays P S.scs) ⊆
      S.sharedI.objPlays P S.sc := by
  rintro t ⟨pc, ⟨qc, hc⟩, ⟨pp, ⟨qp, hp⟩, hpp⟩, rfl⟩
  obtain ⟨ps, qs, hps, hpf⟩ := sup_core St P hc hp hpp.symm (GInv.idle St.idle)
  exact ⟨ps, ⟨qs, hps⟩, hpf⟩

end Silmaril.Proofs.Wasm.Game.Linking.Split
