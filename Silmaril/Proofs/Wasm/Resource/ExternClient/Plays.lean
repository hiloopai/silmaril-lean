module

public import Silmaril.Proofs.Wasm.Resource.ExternClient.Thread
public import Silmaril.Wasm.Resource.ExternExamples.Thms

/-!
# The `externref` client invariant: every play is accepted

* `JU`: the protocol invariant of `U.lts P` for `keptSpecA S₀ G ia iu if_`. After an environment
  fault (either absorbing state) nothing; a running thread is in a store keeping the instance and
  is invariant (`InvU`) or guarded (`GuardedU`); a waiting thread is prepared for every answer.
* `uClientInv`, **`uClientIn_accepts`**: under `UClientIn U S₀ R G fs ia iu if_`, every play of
  `U.strategy P` is accepted by `keptSpecA S₀ G ia iu if_` (every profile, no determinism).
* `uClientIn_of_checkU`, **`checkU_sound`**: the Boolean checker establishes `UClientIn` with
  `R = reachU`, `G = guardU`.

New proofs, following `Silmaril.Proofs.Wasm.Resource.Client.Plays` and
`Silmaril.Proofs.Wasm.Resource.ExternExamples.Basic` (`keptInv`).
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
  Silmaril.Wasm.Resource.ExternExamples
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn PlOK CallPl FuncsClosed Avoids isHost
  invoke_cfgIn)

/-! ## The sentence on single moves -/

section Steps
variable {ι : Type} {S₀ : Store Nat} {G : Nat → Prop} {ia iu if_ : Nat}

/-- Environment moves never break the sentence. -/
theorem keptSpecA_oTotal : OTotal (keptSpecA (ι := ι) S₀ G ia iu if_) :=
  guardO_oTotal (uClientSpec_oTotal ia iu if_)

theorem stepA_ok {q : Option (List Val)} {m : Move UImp (untypedSig ι)}
    (h : Move.IsO m → EnvKeeps S₀ G m ∧ AllocArity ia m) :
    (keptSpecA (ι := ι) S₀ G ia iu if_).step (some q) m =
      (handleStep .client q (uClientEv ia iu if_ m)).map some := by
  rw [keptSpecA, guardO_ok h]
  rfl

theorem stepA_bad {q : Option (List Val)} {m : Move UImp (untypedSig ι)} (hO : Move.IsO m)
    (h : ¬ (EnvKeeps S₀ G m ∧ AllocArity ia m)) :
    (keptSpecA (ι := ι) S₀ G ia iu if_).step (some q) m = some none :=
  guardO_bad hO h

/-- The two absorbing states of the sentence. -/
def Absorb (q : Option (Option (List Val))) : Prop := ∀ L, q ≠ some (some L)

theorem step_absorb {q : Option (Option (List Val))} (hq : Absorb q)
    (m : Move UImp (untypedSig ι)) :
    ∃ q', (keptSpecA (ι := ι) S₀ G ia iu if_).step q m = some q' ∧ Absorb q' := by
  rcases q with _ | _ | L
  · exact ⟨none, rfl, fun _ => nofun⟩
  · by_cases hm : Move.IsO m → EnvKeeps S₀ G m ∧ AllocArity ia m
    · exact ⟨some none, by rw [stepA_ok hm]; rfl, fun _ => nofun⟩
    · have hO : Move.IsO m := by
        by_contra hn; exact hm fun h => absurd h hn
      exact ⟨none, stepA_bad hO fun h => hm fun _ => h, fun _ => nofun⟩
  · exact absurd rfl (hq L)

end Steps

/-! ## The invariant -/

section LTS
variable {U : UInstance} {S₀ : Store Nat} {R G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}

/-- The invariant of a running thread. -/
def JR (S₀ : Store Nat) (R G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat) :
    Option (Option (List Val)) → Store Nat → Thread → Prop
  | some (some L), s, t => Keeps S₀ G s ∧
    (InvU S₀ R G fs ia iu if_ L (t.config s) ∨ GuardedU S₀ R G fs ia iu if_ L (t.config s))
  | _, _, _ => True

/-- **The protocol invariant** of the untyped instance for `keptSpecA`. -/
def JU (U : UInstance) (S₀ : Store Nat) (R G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat) :
    Option (Option (List Val)) → U.State → Prop
  | _, .idle => True
  | q, .running _ s t => JR S₀ R G fs ia iu if_ q s t
  | some (some L), .waiting _ s t e => ∀ (a : UReply) q',
    (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L)) (.inl (.ans e a)) = some q' →
      JR S₀ R G fs ia iu if_ q' a.store (resumeResult s t a.result)
  | _, .waiting .. => True

theorem ju_absorb {q : Option (Option (List Val))} (hq : Absorb q) (y : U.State) :
    JU U S₀ R G fs ia iu if_ q y := by
  rcases q with _ | _ | L
  · cases y <;> trivial
  · cases y <;> trivial
  · exact absurd rfl (hq L)

theorem thread_store (s : Store Nat) (t : Thread) : (t.config s).store = s :=
  Thread.config_store s t

theorem resume_config' {s s' : Store Nat} {t : Thread} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    (resumeResult s t r).config s' = ⟨s', (t.config s).frame, E.fill r.toAdmin⟩ := by
  simp only [resumeResult, hd]
  rfl

/-- The invariant of an invoked export. -/
theorem invU_invoke {L : List Val} {s : Store Nat} (hs : StoreIn G s) {a : Nat} (ha : R a)
    (hRG : ∀ a, R a → G a) {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) :
    InvU S₀ R G fs ia iu if_ L (invoke s a args) := by
  refine ⟨invoke_cfgIn hs (hRG a ha) hargs, ?_, [], SoundF_nil, ?_⟩
  · show Tight R true False (vals args ++ _)
    rw [tight_vals_append]
    simp [Tight, RefIn, Silmaril.Wasm.Verify.refFuncs, ha]
  · have h := freeP_vals (C := cfgU S₀ fs ia iu if_) (V := vals args ++ [.ref (.func a)])
      (R := [.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]) (fun y hy => by
        rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; simp
        · simp only [List.mem_singleton] at hy; subst hy; simp)
      (freeP_nest trivial fun _ _ _ _ => trivial) L s.globals ({} : Frame).module.globals
      ({} : Frame).locals [] [] trivial
    simpa [invoke] using h

theorem isHost_eq_of {s : Store Nat} {i j a : Nat} (hi : isHost s i a = true)
    (hj : isHost s j a = true) : i = j := isHost_unique hi hj

section Vis
variable {f : U.F.Op} {s : Store Nat} {t : Thread} {L : List Val}

/-- An export call. -/
theorem vis_call (hK : UClientIn U S₀ R G fs ia iu if_) (f : U.F.Op) :
    ∃ q', (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L)) (.inr (.ask f)) = some q' ∧
      JU U S₀ R G fs ia iu if_ q' (.running f f.store (U.init f)) := by
  by_cases hok : EnvKeeps S₀ G (.inr (.ask f) : Move UImp (untypedSig U.X)) ∧
      AllocArity ia (.inr (.ask f) : Move UImp (untypedSig U.X))
  · refine ⟨some (some L), by rw [stepA_ok fun _ => hok]; rfl, hok.1.1, .inl ?_⟩
    exact invU_invoke hok.1.1.2 (hK.exports _) hK.sub hok.1.2
  · exact ⟨none, stepA_bad trivial hok, trivial⟩

/-- The answer to a call of another import: the protocol state is unchanged. -/
theorem vis_ret_other {e : UCall Nat} {E : Ctx} {a : Nat} {L' : List Val}
    (he : e.target ≠ ia)
    (hd : decompose? s (t.config s).code = some (E, a, e.target, e.args))
    (hres : ∀ s' r, Keeps S₀ G s' → RefsOK G r →
      InvU S₀ R G fs ia iu if_ L' ⟨s', (t.config s).frame, E.fill r.toAdmin⟩) :
    ∀ (a' : UReply) q', (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L'))
      (.inl (.ans e a')) = some q' → JR S₀ R G fs ia iu if_ q' a'.store (resumeResult s t a'.result) := by
  intro a' q' hq'
  by_cases hok : EnvKeeps S₀ G (.inl (.ans e a') : Move UImp (untypedSig U.X)) ∧
      AllocArity ia (.inl (.ans e a') : Move UImp (untypedSig U.X))
  · rw [stepA_ok fun _ => hok] at hq'
    simp only [uClientEv, he, ↓reduceIte, handleStep_skip, Option.map_some,
      Option.some.injEq] at hq'
    subst hq'
    refine ⟨hok.1.1, .inl ?_⟩
    rw [resume_config' hd]
    exact hres _ _ hok.1.1 hok.1.2
  · rw [stepA_bad (m := (.inl (.ans e a') : Move UImp (untypedSig U.X))) trivial hok] at hq'
    cases hq'; trivial

/-- A callout of an invariant thread: another import. -/
theorem vis_ucall_inv (hK : UClientIn U S₀ R G fs ia iu if_) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (hk : Keeps S₀ G s)
    (hy : InvU S₀ R G fs ia iu if_ L (t.config s)) :
    ∃ q', (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L))
        (.inl (.ask ⟨h, s, args⟩)) = some q' ∧
      JU U S₀ R G fs ia iu if_ q' (.waiting f s t ⟨h, s, args⟩) := by
  obtain ⟨E, a, hd⟩ := callout
  have hd' : decompose? (t.config s).store (t.config s).code = some (E, a, h, args) := by
    rw [thread_store]; exact hd
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, -, -, hfill⟩ := decompose?_sound hd'
  have hRa : R a := tight_callout hyy E (hfill ▸ hy.2.1)
  have hf₀ : S₀.funcs[a]? = some fi := by
    rw [← hk.1 a (hK.sub a hRa)]; simpa [thread_store] using hf
  have hne : ∀ i, Avoids R S₀.funcs i → h ≠ i := fun i hav e => hav a fi hRa hf₀ (e ▸ hcode)
  refine ⟨some (some L), ?_, ?_⟩
  · rw [stepA_ok (m := (.inl (.ask ⟨h, s, args⟩) : Move UImp (untypedSig U.X)))
      fun hO => False.elim hO]
    simp [uClientEv, hne _ hK.avU, hne _ hK.avF, handleStep_skip]
  · refine vis_ret_other (e := ⟨h, s, args⟩) (hne _ hK.avA) hd fun s' r hk' hr => ?_
    have hc : InvU S₀ R G fs ia iu if_ L
        ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      have := hy
      cases t <;> exact this
    exact invU_store (invU_fill hc (fun _ _ => hole_host hyy r) (CodeIn.toAdmin hr)
      (not_all_callRef hyy) (tight_toAdmin r)) hk'.2

/-- A callout of a guarded thread: a use, a free or an allocation. -/
theorem vis_ucall_guard (hK : UClientIn U S₀ R G fs ia iu if_) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (hk : Keeps S₀ G s)
    (hy : GuardedU S₀ R G fs ia iu if_ L (t.config s)) :
    ∃ q', (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L))
        (.inl (.ask ⟨h, s, args⟩)) = some q' ∧
      JU U S₀ R G fs ia iu if_ q' (.waiting f s t ⟨h, s, args⟩) := by
  have hk' : Keeps S₀ G (t.config s).store := by rw [thread_store]; exact hk
  obtain ⟨E, b, args', h', hHb, hbad, hd, hU, hF, hA⟩ := guardedU_decompose hK hk' hy
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  rw [thread_store] at hd
  have heq := Option.some.inj (hd₀.symm.trans hd)
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  have hPm : (keptSpecA (ι := U.X) S₀ G ia iu if_).step (some (some L))
      (.inl (.ask ⟨h, s, args⟩)) =
      (handleStep .client (some L) (uClientEv ia iu if_
        (.inl (.ask ⟨h, s, args⟩) : Move UImp (untypedSig U.X)))).map some :=
    stepA_ok fun hO => False.elim hO
  by_cases hhu : h = iu
  · subst hhu
    obtain ⟨v, rfl, hv, hres⟩ := hU hHb
    refine ⟨some (some L), ?_, vis_ret_other (e := ⟨h, s, [v]⟩) (fun e => hK.dAU e.symm) hd hres⟩
    rw [hPm]; simp [uClientEv, HEv.useOf, handleStep, hv]
  by_cases hhf : h = if_
  · subst hhf
    obtain ⟨v, rfl, hv, hres⟩ := hF hHb
    refine ⟨some (some (L.erase v)), ?_,
      vis_ret_other (e := ⟨h, s, [v]⟩) (fun e => hK.dAF e.symm) hd hres⟩
    rw [hPm]; simp [uClientEv, hhu, HEv.freeOf, handleStep, hv]
  have hha : h = ia := by
    simp only [isBadC, Bool.or_eq_true] at hbad
    rcases hbad with (h₁ | h₁) | h₁
    · exact isHost_unique hHb h₁
    · exact absurd (isHost_unique hHb h₁) hhu
    · exact absurd (isHost_unique hHb h₁) hhf
  subst hha
  obtain ⟨rfl, hres₁, hres₂⟩ := hA hHb
  refine ⟨some (some L), by rw [hPm]; simp [uClientEv, hhu, hhf, handleStep_skip], ?_⟩
  intro a' q' hq'
  by_cases hok : EnvKeeps S₀ G (.inl (.ans ⟨h, s, []⟩ a') : Move UImp (untypedSig U.X)) ∧
      AllocArity h (.inl (.ans ⟨h, s, []⟩ a') : Move UImp (untypedSig U.X))
  · rw [stepA_ok fun _ => hok] at hq'
    simp only [uClientEv, ↓reduceIte] at hq'
    have hrefs : RefsOK G a'.result := hok.1.2
    rcases hr : a'.result with ws | _ | x
    · obtain ⟨h₁, rfl⟩ := List.length_eq_one_iff.1 (hok.2 rfl ws hr)
      rw [hr] at hq' hrefs
      by_cases hh : h₁ ∈ L
      · simp [HEv.allocOfResult, handleStep, hh, fault] at hq'
        subst hq'; trivial
      · simp [HEv.allocOfResult, handleStep, hh] at hq'
        subst hq'
        refine ⟨hok.1.1, .inl ?_⟩
        rw [resume_config' hd]
        exact hres₁ _ h₁ hh hok.1.1 hrefs
    · rw [hr] at hq' hrefs
      simp [HEv.allocOfResult, handleStep] at hq'
      subst hq'
      refine ⟨hok.1.1, .inl ?_⟩
      rw [resume_config' hd]
      exact hres₂ _ _ hok.1.1 hrefs fun _ => nofun
    · rw [hr] at hq' hrefs
      simp [HEv.allocOfResult, handleStep] at hq'
      subst hq'
      refine ⟨hok.1.1, .inl ?_⟩
      rw [resume_config' hd]
      exact hres₂ _ _ hok.1.1 hrefs fun _ => nofun
  · rw [stepA_bad (m := (.inl (.ans ⟨h, s, []⟩ a') : Move UImp (untypedSig U.X))) trivial hok]
      at hq'
    cases hq'; trivial

end Vis

theorem ju_tau (hK : UClientIn U S₀ R G fs ia iu if_) {P : Profile}
    {q : Option (Option (List Val))} {x y : U.State} (hst : U.Trans P x none y)
    (hJ : JU U S₀ R G fs ia iu if_ q x) : JU U S₀ R G fs ia iu if_ q y := by
  cases hst with
  | @tau f s s' t t' hi =>
    rcases q with _ | _ | L
    · trivial
    · trivial
    obtain ⟨hk, hy | hy⟩ := hJ
    · obtain ⟨f', code', rfl, hstep⟩ := hi
      have hk₀ : Keeps S₀ G (t.config s).store := by rw [thread_store]; exact hk
      obtain ⟨hz, hfun, hsi⟩ := step_invU hK hstep hk₀ hy
      have hfs : s'.funcs = s.funcs := by simpa [thread_store] using hfun
      exact ⟨⟨fun a ha => by rw [hfs]; exact hk.1 a ha, hsi⟩, hz⟩
    · exfalso
      obtain ⟨E, b, args, h, -, -, hd, -⟩ :=
        guardedU_decompose hK (by rw [thread_store]; exact hk) hy
      rw [thread_store] at hd
      exact calloutAt_no_internal ⟨E, b, hd⟩ _ hi

theorem ju_vis (hK : UClientIn U S₀ R G fs ia iu if_) {P : Profile}
    {q : Option (Option (List Val))} {x y : U.State} {o : Move U.E U.F}
    (hst : U.Trans P x (some o) y) (hJ : JU U S₀ R G fs ia iu if_ q x) :
    ∃ q', (keptSpecA (ι := U.X) S₀ G ia iu if_).step q o = some q' ∧
      JU U S₀ R G fs ia iu if_ q' y := by
  rcases q with _ | _ | L
  · obtain ⟨q', h₁, h₂⟩ := step_absorb (S₀ := S₀) (G := G) (ia := ia) (iu := iu) (if_ := if_)
      (q := none) (fun _ => nofun) o
    exact ⟨q', h₁, ju_absorb h₂ y⟩
  · obtain ⟨q', h₁, h₂⟩ := step_absorb (S₀ := S₀) (G := G) (ia := ia) (iu := iu) (if_ := if_)
      (q := some none) (fun _ => nofun) o
    exact ⟨q', h₁, ju_absorb h₂ y⟩
  cases hst with
  | call f => exact vis_call hK f
  | ucall callout =>
    obtain ⟨hk, hy | hy⟩ := hJ
    · exact vis_ucall_inv hK callout hk hy
    · exact vis_ucall_guard hK callout hk hy
  | uret a =>
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (keptSpecA_oTotal (ι := U.X) (S₀ := S₀) (G := G) (ia := ia) (iu := iu) (if_ := if_)
        (some (some L)) (.inl (.ans _ a)) trivial)
    exact ⟨q', hq', hJ a q' hq'⟩
  | @oret f s t r final =>
    exact ⟨some (some L), by
      rw [stepA_ok (m := (.inr (.ans f ⟨s, r⟩) : Move UImp (untypedSig U.X)))
        fun hO => False.elim hO]
      simp [uClientEv, handleStep_skip], trivial⟩

/-- **The protocol invariant of the untyped system** for `keptSpecA` (every profile). -/
def uClientInv (hK : UClientIn U S₀ R G fs ia iu if_) (P : Profile) :
    LTSInv (U.lts P) (keptSpecA (ι := U.X) S₀ G ia iu if_) where
  J := JU U S₀ R G fs ia iu if_
  init := trivial
  tau hst hJ := ju_tau hK hst hJ
  vis hst hJ := ju_vis hK hst hJ

/-- **Soundness of the `externref` client analysis** (every profile, no determinism): every
play of the untyped instance is accepted by `keptSpecA`. -/
theorem uClientIn_accepts (hK : UClientIn U S₀ R G fs ia iu if_) (P : Profile) :
    ∀ p ∈ U.strategy P, (keptSpecA (ι := U.X) S₀ G ia iu if_).Accepts p :=
  untyped_accepts (uClientInv hK P) keptSpecA_oTotal

end LTS

/-! ## The checker -/

section Check
open Silmaril.Wasm.Verify (avoidsB_sound rootsB avoidsB)

variable {U : UInstance} {S₀ : Store Nat} {fs addrs : List Nat} {ia iu if_ : Nat}

theorem isBadC_lt {a : Nat} (h : isBadC S₀ ia iu if_ a = true) : a < S₀.funcs.length := by
  simp only [isBadC, Bool.or_eq_true] at h
  have hh : ∃ i, isHost S₀ i a = true := by rcases h with (h | h) | h <;> exact ⟨_, h⟩
  obtain ⟨i, hi⟩ := hh
  obtain ⟨fi, hfi, -⟩ := isHost_some hi
  exact (List.getElem?_eq_some_iff.1 hfi).1

theorem isBadC_host {a : Nat} {fi : FuncInst Nat} (h : isBadC S₀ ia iu if_ a = true)
    (hf : S₀.funcs[a]? = some fi) : ∃ i, fi.code = .host i := by
  simp only [isBadC, Bool.or_eq_true] at h
  have hh : ∃ i, isHost S₀ i a = true := by rcases h with (h | h) | h <;> exact ⟨_, h⟩
  obtain ⟨i, hi⟩ := hh
  obtain ⟨fi', hfi', hc⟩ := isHost_some hi
  rw [hf] at hfi'; cases hfi'
  exact ⟨i, hc⟩

theorem funcOkU_split {R : List Nat} {a : Nat} (h : funcOkU S₀ fs R ia iu if_ a = true) :
    funcOkC S₀ fs R ia iu if_ [] a = true ∧
      ∀ fi code, S₀.funcs[a]? = some fi → fi.code = .wasm code → noDynL code.body = true := by
  simp only [funcOkU, Bool.and_eq_true] at h
  refine ⟨h.1, fun fi code hf hcode => ?_⟩
  have h₂ := h.2
  simp only [hf, hcode] at h₂
  exact h₂

theorem wasm_of_guardU {a : Nat} {fi : FuncInst Nat} {code : Func}
    (ha : a ∈ guardU S₀ fs addrs ia iu if_) (hf : S₀.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) : a ∈ reachU S₀ fs addrs ia iu if_ := by
  rcases List.mem_append.1 ha with ha | ha
  · exact ha
  · obtain ⟨i, hi⟩ := isBadC_host (List.mem_filter.1 ha).2 hf
    rw [hi] at hcode; cases hcode

theorem hostTy_of_hostTyB {a : Nat} {fi : FuncInst Nat} (h : hostTyB S₀ ia iu if_ a = true)
    (ha : isBadC S₀ ia iu if_ a = true) (hf : S₀.funcs[a]? = some fi) :
    ∃ ps rs, Expand fi.type (.func ps rs) ∧ (isHost S₀ ia a = true → ps.length = 0) ∧
      (isHost S₀ ia a = false → ps.length = 1) := by
  simp only [hostTyB, hf] at h
  split at h
  · rename_i ps rs hex
    have h₁ : (isHost S₀ ia a = false ∨ ps.length = 0) ∧
        ((isHost S₀ iu a = false ∧ isHost S₀ if_ a = false) ∨ ps.length = 1) := by
      simpa using h
    refine ⟨ps, rs, Expand.iff.2 hex, fun hA => h₁.1.resolve_left (by simp [hA]), fun hA => ?_⟩
    have hb : isHost S₀ iu a = true ∨ isHost S₀ if_ a = true := by simpa [isBadC, hA] using ha
    exact h₁.2.resolve_left fun h' => by rcases hb with hb | hb <;> simp_all
  · cases h

theorem badU_mem {a : Nat} (ha : isBadC S₀ ia iu if_ a = true) : a ∈ badU S₀ ia iu if_ :=
  List.mem_filter.2 ⟨List.mem_range.2 (isBadC_lt ha), ha⟩

/-- **The checker establishes `UClientIn`.** -/
theorem uClientIn_of_checkU (h : checkU S₀ fs addrs ia iu if_ = true)
    (hU : ∀ x, U.addr x ∈ addrs) :
    UClientIn U S₀ (· ∈ reachU S₀ fs addrs ia iu if_) (· ∈ guardU S₀ fs addrs ia iu if_) fs
      ia iu if_ := by
  simp only [checkU, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, rootsB,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hAU, hAF⟩, hUF⟩, hfun⟩, hroots⟩, hvA⟩, hvU⟩, hvF⟩, hty⟩ := h
  exact ⟨fun a ha => List.mem_append_left _ ha, fun a ha => List.mem_append_right _ (badU_mem ha),
    fun _ _ _ ha hf hcode => wasm_of_guardU ha hf hcode,
    fun a _ _ ha hf hcode => ⟨(funcOkC_sound (funcOkU_split (hfun a ha)).1 hf hcode).1,
      (funcOkC_sound (funcOkU_split (hfun a ha)).1 hf hcode).2.1⟩,
    fun a _ _ ha hf hcode => (funcOkC_sound (funcOkU_split (hfun a ha)).1 hf hcode).2.2,
    fun a fi code ha hf hcode => (funcOkU_split (hfun a ha)).2 fi code hf hcode,
    fun x => by simpa using hroots _ (hU x),
    avoidsB_sound hvA, avoidsB_sound hvU, avoidsB_sound hvF, hAU, hAF, hUF,
    fun a _ ha hf => hostTy_of_hostTyB (hty a (badU_mem ha)) ha hf⟩

/-- **Soundness of the `externref` client checker** (every profile, no determinism): every play
of an untyped instance whose exports the checker saw is accepted by `keptSpecA` with the guard
set `guardU`. -/
theorem checkU_sound (h : checkU S₀ fs addrs ia iu if_ = true) (hU : ∀ x, U.addr x ∈ addrs)
    (P : Profile) :
    ∀ p ∈ U.strategy P,
      (keptSpecA (ι := U.X) S₀ (· ∈ guardU S₀ fs addrs ia iu if_) ia iu if_).Accepts p :=
  uClientIn_accepts (uClientIn_of_checkU h hU) P

end Check

end Silmaril.Wasm.Resource.ExternClient
