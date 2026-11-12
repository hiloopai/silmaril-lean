module

public import Silmaril.Proofs.Wasm.Resource.OBClient.Basic

/-!
# The borrowing-client analysis: the protocol invariant

`JO`: the protocol invariant of `I.dlts P I.store` for `(obSpec ρ).comap moveEvent`, with the
held handles of the protocol state as the live list of the client analysis. Export calls of role
exports lend or hand over their argument and start an entering thread (`EntryO`); callouts of the
use import are guarded uses; the allocator's answers add an owned handle; export returns end the
borrows (nothing survives: no global pairs). `obIn_sound`: the ownership sentence over
`wasmSem P`, every profile.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn StoreIn RefIn Avoids isHost typed_refIn answer_refIn callout_mem
  decompose_toAdmin_none ifaceOp?_fst ifaceOp?_snd)

section
variable {I : ScalarInstance} {G R : Nat → Prop} {fs : List Nat} {ia iu : Nat}
  {ρ : OBRoles (ifaceOf I)}

/-- The ownership sentence on the moves of the instance. -/
abbrev πO (I : ScalarInstance) (ρ : OBRoles (ifaceOf I)) :
    Protocol (Option (List (Val × Mode))) (Move I.E I.F) :=
  (obSpec ρ).comap (moveEvent (X := ifaceOf I))

/-- The invariant of a resumed thread. -/
def JRO (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu : Nat) :
    Option (List (Val × Mode)) → Config Nat → Prop
  | none, _ => True
  | some L, c => InvO I G fs ia iu (heldL L) c

/-- **The protocol invariant**: everything holds after an environment fault (`none`); otherwise
an invariant, guarded or entering thread for the held handles. -/
def JO (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu : Nat)
    (ρ : OBRoles (ifaceOf I)) : Option (List (Val × Mode)) → I.HState → Prop
  | none, _ => True
  | some _, .idle s => StoreIn G s ∧ s.funcs = I.store.funcs
  | some L, .running _ s t =>
    (InvO I G fs ia iu (heldL L) (t.config s) ∨ GuardedO I G fs ia iu (heldL L) (t.config s) ∨
      EntryO I G R fs ia iu (heldL L) s t) ∧ s.funcs = I.store.funcs
  | some L, .waiting _ s t e => s.funcs = I.store.funcs ∧
    ∀ (v : I.E.Ar e) (q' : Option (List (Val × Mode))),
      (πO I ρ).step (some L) (.inl (.ans e v)) = some q' →
      JRO I G fs ia iu q' ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

/-! ## Events -/

theorem stepO_ask (L : List (Val × Mode)) (e : I.E.Op) :
    (πO I ρ).step (some L) (.inl (.ask e)) = obStep (some L)
      (if ρ.use e.1 then OEv.ofArgs .use e.2.1 else if ρ.free e.1 then OEv.ofArgs .free e.2.1
        else if ρ.give e.1 then OEv.ofArgs .give e.2.1 else .skip) := rfl

theorem stepO_ans (L : List (Val × Mode)) (e : I.E.Op) (w : I.E.Ar e) :
    (πO I ρ).step (some L) (.inl (.ans e w)) = obStep (some L)
      (if ρ.alloc e.1 then OEv.ofRes .alloc (Answer.toBehaviour (ft := I.imports.get e.1) w)
        else .skip) := rfl

theorem stepO_call (L : List (Val × Mode)) (f : I.F.Op) :
    (πO I ρ).step (some L) (.inr (.ask f)) = obStep (some L)
      (if ρ.lend f.1 then OEv.ofArgs .lend f.2.1 else if ρ.take f.1 then OEv.ofArgs .take f.2.1
        else .skip) := rfl

theorem stepO_ret (L : List (Val × Mode)) (f : I.F.Op) (w : I.F.Ar f) :
    (πO I ρ).step (some L) (.inr (.ans f w)) = some (some (L.filter fun p => p.2 == .owned)) :=
  rfl

/-- The answer of an import other than the allocator: skipped. -/
theorem stepO_ans_skip {L : List (Val × Mode)} {e : I.E.Op} (w : I.E.Ar e)
    (ha : ρ.alloc e.1 = false) : (πO I ρ).step (some L) (.inl (.ans e w)) = some (some L) := by
  rw [stepO_ans, ha]; rfl

/-- A callout with no handle event: skipped. -/
theorem stepO_ask_skip {L : List (Val × Mode)} {e : I.E.Op} (hu : ρ.use e.1 = false)
    (hd : ∀ k, (ρ.free e.1 = true ∨ ρ.give e.1 = true) → OEv.ofArgs k e.2.1 = .skip) :
    (πO I ρ).step (some L) (.inl (.ask e)) = some (some L) := by
  have hsk : (if ρ.use e.1 then OEv.ofArgs .use e.2.1 else if ρ.free e.1 then OEv.ofArgs .free e.2.1
      else if ρ.give e.1 then OEv.ofArgs .give e.2.1 else .skip) = OEv.skip := by
    rw [hu]
    cases hf : ρ.free e.1
    · cases hg : ρ.give e.1
      · rfl
      · exact hd _ (.inr hg)
    · exact hd _ (.inl hf)
  rw [stepO_ask, hsk]; rfl

/-! ## Vis steps -/

section Vis
variable {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} {L : List (Val × Mode)}

/-- A callout of an invariant thread: another import, no handle event. -/
theorem visO_inv (hR : OBIn I G R fs ia iu ρ) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : InvO I G fs ia iu (heldL L) (t.config s)) (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧ JO I G R fs ia iu ρ q' (.waiting f s t e) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1
  have he : e.1.val = h := ifaceOp?_fst op
  have hne : ∀ i : Nat, Avoids G I.store.funcs i → e.1.val ≠ i :=
    fun i hav ei => hav a fi ha (hfy ▸ hf) (by rw [hcode, ← he, ei])
  have hu : ρ.use e.1 = false := (hR.use e.1).trans (by simpa using hne _ hR.core.avU)
  have hal : ρ.alloc e.1 = false := (hR.alloc e.1).trans (by simpa using hne _ hR.core.avA)
  have hfg : ∀ k, (ρ.free e.1 = true ∨ ρ.give e.1 = true) → OEv.ofArgs k e.2.1 = .skip := by
    intro k hk
    exact absurd rfl (hne _ (hR.drop e.1 (by simpa [Bool.or_eq_true] using hk)))
  refine ⟨some L, stepO_ask_skip hu hfg, hfy, fun w q' hq' => ?_⟩
  rw [stepO_ans_skip w hal] at hq'
  cases hq'
  exact resume_invC hy _ (answer_refIn w)

/-- The decomposition of a callout is unique. -/
theorem callout_eq' {h₀ : Nat} {args args₀ : List Val} {E E₀ : Ctx} {a₀ b h : Nat}
    (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args₀))
    (hd : decompose? s (t.config s).code = some (E, b, h₀, args)) : h = h₀ ∧ args₀ = args := by
  have heq := Option.some.inj (hd₀.symm.trans hd)
  simp only [Prod.mk.injEq] at heq
  exact ⟨heq.2.2.1, heq.2.2.2⟩

/-- A guarded use: the handle is held. -/
theorem visO_use (hR : OBIn I G R fs ia iu ρ) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} {v : Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, iu, [v])) (hv : v ∈ heldL L)
    (hres : ∀ r, Client.RefsOK G r →
      InvO I G fs ia iu (heldL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧ JO I G R fs ia iu ρ q' (.waiting f s t e) := by
  obtain ⟨hh, rfl⟩ := callout_eq' hd₀ hd
  have he : e.1.val = iu := (ifaceOp?_fst op).trans hh
  have hargs : e.2.1 = [v] := ifaceOp?_snd op
  have hu : ρ.use e.1 = true := (hR.use e.1).trans (by simp [he])
  have hal : ρ.alloc e.1 = false :=
    (hR.alloc e.1).trans (by simpa [he] using fun e' => hR.core.dAU e'.symm)
  have hstep : (πO I ρ).step (some L) (.inl (.ask e)) = some (some L) := by
    rw [stepO_ask, hu, ite_t rfl, hargs]
    simp [OEv.ofArgs, obStep, (held_iff L v).2 hv]
  refine ⟨some L, hstep, hfy, fun w q' hq' => ?_⟩
  rw [stepO_ans_skip w hal] at hq'
  cases hq'
  show InvO I G fs ia iu (heldL L) _
  rw [resumeResult_config hd]
  exact hres _ (answer_refIn w)

/-- The answer of an allocation adds an owned handle, unless the environment faults. -/
theorem visO_alloc_ans (hR : OBIn I G R fs ia iu ρ) {E : Ctx} {b : Nat}
    (he : e.1.val = ia) (hd : decompose? s (t.config s).code = some (E, b, ia, []))
    (hres₁ : ∀ h, h ∉ heldL L → Client.RefsOK G (.values [h]) → InvO I G fs ia iu (h :: heldL L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, Client.RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvO I G fs ia iu (heldL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩)
    (w : I.E.Ar e) (q' : Option (List (Val × Mode)))
    (hq' : (πO I ρ).step (some L) (.inl (.ans e w)) = some q') :
    JRO I G fs ia iu q' ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  have hal : ρ.alloc e.1 = true := (hR.alloc e.1).trans (by simp [he])
  rw [stepO_ans, hal, ite_t rfl] at hq'
  rw [resumeResult_config hd]
  cases w with
  | values vs =>
    obtain ⟨ws, hws⟩ := vs
    have hres : (I.imports.get e.1).results.length = 1 := by
      have he' : e.1 = ⟨ia, he ▸ e.1.isLt⟩ := Fin.ext he
      rw [he']; exact (hR.core.arA _).2
    obtain ⟨h₁, rfl⟩ := List.length_eq_one_iff.1 ((List.Forall₂.length_eq hws).symm.trans hres)
    by_cases hh : h₁ ∈ heldL L
    · simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep, (held_iff L h₁).2 hh] at hq'
      subst hq'; trivial
    · have hh' : held L h₁ = false := Bool.eq_false_iff.2 fun h' => hh ((held_iff L h₁).1 h')
      simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep, hh'] at hq'
      subst hq'
      exact hres₁ h₁ hh (answer_refIn (Answer.values (ft := I.imports.get e.1) ⟨[h₁], hws⟩))
  | trap =>
    simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep] at hq'
    subst hq'
    exact hres₂ .trap (answer_refIn (Answer.trap (ft := I.imports.get e.1))) (fun _ => nofun)
  | throw a =>
    simp [Answer.toBehaviour, Answer.toResult, OEv.ofRes, obStep] at hq'
    subst hq'
    exact hres₂ (.throw a) (answer_refIn (Answer.throw (ft := I.imports.get e.1) a)) (fun _ => nofun)

/-- A guarded allocation: no event at the question. -/
theorem visO_alloc (hR : OBIn I G R fs ia iu ρ) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, ia, []))
    (hres₁ : ∀ h, h ∉ heldL L → Client.RefsOK G (.values [h]) → InvO I G fs ia iu (h :: heldL L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, Client.RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvO I G fs ia iu (heldL L) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧ JO I G R fs ia iu ρ q' (.waiting f s t e) := by
  obtain ⟨hh, rfl⟩ := callout_eq' hd₀ hd
  have he : e.1.val = ia := (ifaceOp?_fst op).trans hh
  have hargs : e.2.1 = [] := ifaceOp?_snd op
  have hu : ρ.use e.1 = false := (hR.use e.1).trans (by simpa [he] using hR.core.dAU)
  have hfg : ∀ k, (ρ.free e.1 = true ∨ ρ.give e.1 = true) → OEv.ofArgs k e.2.1 = .skip :=
    fun k _ => by rw [hargs]; rfl
  exact ⟨some L, stepO_ask_skip hu hfg, hfy, visO_alloc_ans hR he hd hres₁ hres₂⟩

/-- A callout of a guarded thread: a use or an allocation (the free import does not exist). -/
theorem visO_guard (hR : OBIn I G R fs ia iu ρ) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : GuardedO I G fs ia iu (heldL L) (t.config s)) (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πO I ρ).step (some L) (.inl (.ask e)) = some q' ∧ JO I G R fs ia iu ρ q' (.waiting f s t e) := by
  have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  obtain ⟨E, b, ⟨v, -, hd, hv, hres⟩ | ⟨v, hfr, -⟩ | ⟨-, hd, hres₁, hres₂⟩⟩ :=
    guarded_cases hR.core hf₀ hy
  · exact visO_use hR op hfy hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact absurd hfr (by rw [noImp_host_false hR.core.ok rfl]; exact Bool.false_ne_true)
  · exact visO_alloc hR op hfy hd₀ (by simpa [Thread.config_store] using hd)
      (by simpa [Thread.config_store] using hres₁) (by simpa [Thread.config_store] using hres₂)

/-- An export call: a role export lends or hands over its argument and starts entering. -/
theorem visO_call (hR : OBIn I G R fs ia iu ρ) (hs : StoreIn G s) (hfs : s.funcs = I.store.funcs) :
    ∃ q', (πO I ρ).step (some L) (.inr (.ask f)) = some q' ∧
      JO I G R fs ia iu ρ q' (.running f s (I.initThread f)) := by
  by_cases hr : (ρ.lend f.1 || ρ.take f.1) = true
  · show ∃ q', (πO I ρ).step (some L) (.inr (.ask f)) = some q' ∧
      JO I G R fs ia iu ρ q' (.running f s (I.initThread f))
    obtain ⟨hR₁, hlen⟩ := hR.role f.1 hr
    have hl : f.2.1.length = 1 := (List.Forall₂.length_eq f.2.2).symm.trans hlen
    obtain ⟨h, hh⟩ := List.length_eq_one_iff.1 hl
    obtain ⟨fi, hfi, hexp⟩ := hR.core.ok.export_type f.1
    obtain ⟨fi', code, hfi', hcode, hm, hpl, hok⟩ := hR.ent _ hR₁
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    have hentry : ∀ L' : List (Val × Mode), h ∈ heldL L' →
        EntryO I G R fs ia iu (heldL L') s (I.initThread f) := fun L' hL' =>
      ⟨I.addr f.1, h, fi, code, _, _, by simp [ScalarInstance.initThread, hh], hR₁, hL', hs,
        fun r hr' => typed_refIn (G := G) f.2.2 r (by rw [hh]; exact hr'), hfs ▸ hfi, hcode, hexp,
        by simpa [Ty.length_ofList] using hlen.symm, hm, hpl, hok⟩
    have hcases : ∀ (k : Val → OEv Val) (m : Mode),
        (∀ L' : List (Val × Mode), obStep (some L') (k h) =
          if held L' h = true then some none else some (some ((h, m) :: L'))) →
        ∃ q', obStep (some L) (OEv.ofArgs k f.2.1) = some q' ∧
          JO I G R fs ia iu ρ q' (.running f s (I.initThread f)) := by
      intro k m hk
      rw [hh]
      show ∃ q', obStep (some L) (k h) = some q' ∧ _
      rw [hk]
      by_cases hb : held L h = true
      · exact ⟨none, by rw [ite_t hb], trivial⟩
      · exact ⟨some ((h, m) :: L), by rw [ite_f hb],
          .inr (.inr (hentry _ (by simp [heldL]))), hfs⟩
    rw [stepO_call]
    by_cases hlend : ρ.lend f.1 = true
    · rw [ite_t hlend]; exact hcases .lend .borrowed fun _ => rfl
    · have htake : ρ.take f.1 = true := by simpa [hlend] using hr
      rw [ite_f hlend, ite_t htake]; exact hcases .take .owned fun _ => rfl
  · have hr' : ρ.lend f.1 = false ∧ ρ.take f.1 = false := by simpa using hr
    refine ⟨some L, by rw [stepO_call, hr'.1, hr'.2]; rfl, .inl ?_, hfs⟩
    exact invC_invoke hs (fun p hp => by simp at hp) (hR.plain f.1 (by simpa using hr))
      (typed_refIn f.2.2)

/-- A finished thread: the borrows end, the store invariant holds. -/
theorem visO_ret (hR : OBIn I G R fs ia iu ρ) {r : Result} (final : ResultAt s t r)
    (hx : (InvO I G fs ia iu (heldL L) (t.config s) ∨ GuardedO I G fs ia iu (heldL L) (t.config s) ∨
      EntryO I G R fs ia iu (heldL L) s t) ∧ s.funcs = I.store.funcs) :
    StoreIn G s ∧ s.funcs = I.store.funcs := by
  obtain ⟨hy | hy | hy, hfy⟩ := hx
  · exact ⟨Thread.config_store s t ▸ hy.1.1, hfy⟩
  · have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    obtain ⟨E, b, ⟨v, -, hd, -⟩ | ⟨v, -, hd, -⟩ | ⟨-, hd, -⟩⟩ := guarded_cases hR.core hf₀ hy <;>
      · rw [final, decompose_toAdmin_none] at hd
        cases hd
  · obtain ⟨a, h, -, -, -, -, rfl, -⟩ := hy
    exact absurd final (invoke_ne_result r)

end Vis

/-- The vis steps. -/
theorem jo_vis (hR : OBIn I G R fs ia iu ρ) {P : Profile} {q : Option (List (Val × Mode))}
    {x y : I.HState} {o : Move I.E I.F} (hs : I.DTrans P x (some o) y)
    (hx : JO I G R fs ia iu ρ q x) :
    ∃ q', (πO I ρ).step q o = some q' ∧ JO I G R fs ia iu ρ q' y := by
  rcases q with _ | L
  · exact ⟨none, rfl, trivial⟩
  cases hs with
  | call s f => exact visO_call hR hx.1 hx.2
  | ucall callout op =>
    obtain ⟨hy | hy | hy, hfy⟩ := hx
    · exact visO_inv hR callout op hy hfy
    · exact visO_guard hR callout op hy hfy
    · exact absurd callout (entry_no_callout hy)
  | uret v =>
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (obSpec_oTotal ρ (some L) (.inl (.ans _ v)) trivial)
    exact ⟨q', hq', match q' with
      | none => trivial
      | some _ => ⟨.inl (hx.2 v _ hq'), hx.1⟩⟩
  | oret final answer => exact ⟨_, stepO_ret L _ _, visO_ret hR final hx⟩

/-- **The protocol invariant of the instance's transition system** (every profile). -/
def obLTSInv (hR : OBIn I G R fs ia iu ρ) (P : Profile) :
    LTSInv (I.dlts P I.store) (πO I ρ) where
  J := JO I G R fs ia iu ρ
  init := ⟨hR.core.store, rfl⟩
  tau := by
    intro q x y hst hx
    rcases q with _ | L
    · trivial
    cases hst with
    | @tau f s s' t t' h =>
      obtain ⟨hy | hy | hy, hfy⟩ := hx
      · obtain ⟨f', code', ht', hstep⟩ := h
        have hf₀ : (t.config s).store.funcs = I.store.funcs := by
          rw [Thread.config_store]; exact hfy
        obtain ⟨hz, hfz⟩ := step_invC hR.core hstep hf₀ hy
        subst ht'
        exact ⟨hz.elim .inl (fun hg => .inr (.inl hg)), hfz.trans hf₀⟩
      · obtain ⟨hh, _, hc⟩ := guarded_callout hR.core hfy hy
        exact absurd h (calloutAt_no_internal hc _)
      · obtain ⟨hz, rfl⟩ := entry_step hy h
        exact ⟨.inl hz, hfy⟩
  vis := fun hst hx => jo_vis hR hst hx

/-- **Soundness of the borrowing-client analysis** (every profile): every play of the instance
is accepted by the ownership sentence. -/
theorem obIn_accepts (hR : OBIn I G R fs ia iu ρ) (P : Profile) :
    ∀ p ∈ I.strategy P I.store, (πO I ρ).Accepts p :=
  dlts_accepts (obLTSInv hR P) (obSpec_oTotal ρ)

/-- **The ownership sentence over `wasmSem P`** (every profile). -/
theorem obIn_sound (hR : OBIn I G R fs ia iu ρ) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (WasmProg.ofInstance I) (obSpec ρ) :=
  models_of_plays _ _ (obIn_accepts hR P)

end

end Silmaril.Wasm.Resource.OBClient

/-! ## The checker -/

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (instOf progOf instance? isInstance_instOf mem_exprRF mem_exprCalls
  mem_storeFuncs_of rootsB_mem avoidsB_sound avoidsB Avoids PlOK CallPl isHost)

theorem funcOkE_sound {s : Store Nat} {fs G : List Nat} {ia iu nf a : Nat}
    (h : funcOkE s fs G ia iu nf a = true) :
    ∃ (fi : FuncInst Nat) (code : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm code ∧
      fi.module.funcs = fs ∧ (∀ ins ∈ code.body, PlOK (CallPl (· ∈ G) (isBadC s ia iu nf) fs) ins) ∧
      okL (cfgOf s fs ia iu nf []) fi.module.globals [.loc 0] .other code.body = true := by
  unfold funcOkE at h
  split at h
  · rename_i fi hf
    split at h
    · rename_i code hcode
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨hm, hrf⟩, hcall⟩, hok⟩ := h
      refine ⟨fi, code, hf, hcode, hm, fun ins hins => .inr ⟨fun x hx b hb => ?_,
        fun x hx b hb => ?_⟩, hok⟩
      · simpa [hb] using hrf x (mem_exprRF hins hx)
      · have h₁ := hcall x (mem_exprCalls hins hx)
        simpa only [hb, Bool.or_eq_true, List.contains_iff_mem] using h₁
    · cases h
  · cases h

theorem mem_roleAddrs {I : ScalarInstance} {ρ : NRoles} {a : Nat} (h : a ∈ roleAddrs I ρ) :
    ∃ j, j < I.exports.length ∧ roleB ρ j = true ∧ a = I.addrs.getD j 0 := by
  simp only [roleAddrs, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨j, ⟨hj, hr⟩, rfl⟩ := h
  exact ⟨j, hj, hr, rfl⟩

theorem exportsOK_at {I : ScalarInstance} {G : List Nat} {ia iu : Nat} {ρ : NRoles}
    (h : exportsOK I G ia iu ρ = true) {j : Nat} (hj : j < I.exports.length) :
    (roleB ρ j = true → (I.exports[j]?.map (·.params.length)) = some 1 ∧
      funcOkE I.store (fsOf I) G ia iu (noImp I) (I.addrs.getD j 0) = true) ∧
    (roleB ρ j = false → I.addrs.getD j 0 ∈ G) := by
  have hj' := List.all_eq_true.1 h j (List.mem_range.2 hj)
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · simp only [hr, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hj'
    exact hj'
  · simpa [hr] using hj'

theorem roleOK_at {I : ScalarInstance} {G : List Nat} {ia iu : Nat} {ρ : NRoles}
    (h : roleOK I G ia iu ρ = true) {i : Nat} (hi : i < I.imports.length) :
    ρ.alloc i = (i == ia) ∧ ρ.use i = (i == iu) ∧
      ((ρ.free i || ρ.give i) = true → avoidsB I.store G i = true) := by
  have hi' := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hi'
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hi'
  refine ⟨h₁, h₂, fun hfg => ?_⟩
  rcases h₃ with h₃ | h₃
  · rw [h₃] at hfg; cases hfg
  · exact h₃

/-- **The checker establishes `OBIn`.** -/
theorem obIn_of_checkOBInst {I : ScalarInstance} (hok : I.Ok) {ia iu : Nat} {ρ : NRoles}
    (h : checkOBInst I ia iu ρ = true) :
    OBIn I (· ∈ reachOB I ia iu ρ) (· ∈ roleAddrs I ρ) (fsOf I) ia iu ρ.toOB := by
  simp only [checkOBInst, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAU, hia⟩, hiu⟩, haA⟩, hrA⟩, haU⟩, hfun⟩, hroots⟩, hvA⟩, hvU⟩, hexp⟩,
    hrole⟩ := h
  have hnf : ∀ b, isHost I.store (noImp I) b = false := noImp_host_false hok rfl
  have havF : Avoids (· ∈ reachOB I ia iu ρ) I.store.funcs (noImp I) := by
    intro a fi _ hf hcode
    have h₀ := hnf a
    simp [isHost, hf, hcode] at h₀
  have hdA : ia ≠ noImp I := Nat.ne_of_lt hia
  have hdU : iu ≠ noImp I := Nat.ne_of_lt hiu
  have core : ClientCore I (· ∈ reachOB I ia iu ρ) (fsOf I) ia iu (noImp I) [] :=
    { ok := hok
      closed := fun a fi code ha hf hcode =>
        ⟨(funcOkC_sound (hfun a ha) hf hcode).1, (funcOkC_sound (hfun a ha) hf hcode).2.1⟩
      bodies := fun a fi code ha hf hcode => (funcOkC_sound (hfun a ha) hf hcode).2.2
      store := mem_storeFuncs_of (rootsB_mem hroots)
      avA := avoidsB_sound hvA
      avU := avoidsB_sound hvU
      avF := havF
      pairs := by decide
      init := fun p hp => absurd hp (List.not_mem_nil)
      dAU := hAU
      dAF := hdA
      dUF := hdU
      arA := fun hi => ⟨arity_of haA hi, arity_res hrA hi⟩
      arU := fun hi => arity_of haU hi
      arF := fun hi => absurd hi (Nat.lt_irrefl _) }
  refine ⟨core, fun a ha => ?_, fun j hj => ?_, fun j hj => ?_, fun i => ?_, fun i => ?_,
    fun i hi => ?_⟩
  · obtain ⟨j, hj, hr, rfl⟩ := mem_roleAddrs ha
    exact funcOkE_sound ((exportsOK_at hexp hj).1 hr).2
  · refine ⟨List.mem_map.2 ⟨j.val, List.mem_filter.2 ⟨List.mem_range.2 j.isLt, hj⟩, rfl⟩, ?_⟩
    have hjl : j.val < I.exports.length := j.isLt
    have h₁ := ((exportsOK_at hexp hjl).1 hj).1
    rw [List.getElem?_eq_getElem hjl, Option.map_some, Option.some.injEq] at h₁
    exact h₁
  · exact (exportsOK_at hexp j.isLt).2 (by simpa [roleB, NRoles.toOB] using hj)
  · exact (roleOK_at hrole i.isLt).1
  · exact (roleOK_at hrole i.isLt).2.1
  · exact avoidsB_sound ((roleOK_at hrole i.isLt).2.2 (by simpa [NRoles.toOB] using hi))

/-- **Soundness of the borrowing-client checker on a module** (every profile, no determinism
assumed). -/
theorem checkOB_sound {m : Module} {ia iu : Nat} {ρ : NRoles} (h : checkOB m ia iu ρ = true)
    (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf m) (obSpec ρ.toOB) := by
  simp only [checkOB, Bool.and_eq_true] at h
  obtain ⟨mt, hI⟩ := isInstance_instOf h.1
  exact obIn_sound (obIn_of_checkOBInst hI.ok h.2) P

end Silmaril.Wasm.Resource.OBClient
