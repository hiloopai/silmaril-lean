module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.KSim

/-!
# Bind-then-resume and the direct resume have the same behaviours

From the one-step simulation `sim_step`:

* `sim_steps`, `sim_diverges`, **`sim_behaviours`**: runs, divergence and behaviours of a
  configuration are those of its image under a store relation `KRel ρ B` (code avoiding `B`);
* `rnL_id`, `avL_mono`: renaming fixes code that only mentions slots it fixes;
* `ContNat L C`: the continuation `C` commutes with every renaming that fixes the first `L`
  slots, and keeps code away from any set of slots `≥ L` (true of the continuations `cont.new`,
  `cont.bind`, `suspend` and `switch` build from such code);
* **`post_eq`**: the configuration after bind-then-resume (one more consumed slot, at the end)
  and the one after the direct resume have the same `StepFXR` behaviours: `KRel` relates the two
  stores both ways, ignoring the extra slot one way;
* `stepR_bind_det`, `behavioursFXR_of_det`: the typed `cont.bind` is deterministic, and a
  configuration with one successor has its successor's behaviours;
* **`bind_resume_eq`**: under `StepFXR` (no host calls), with `cont.bind` binding `|vs|` values
  and `resume` taking `|ws|`, binding `vs` and resuming with `ws` **has exactly the behaviours**
  of resuming the original continuation with `vs ++ ws`, when the store's continuations are
  natural (`ContNat`) and `vs ++ ws` mention only existing slots.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume Silmaril.Wasm.Models.FXResumeT
open Silmaril.Proofs.Wasm.Models.FXResume (bound set_append_length)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {ρ : Nat → Nat} {B : Nat → Prop}

/-- The image of a configuration under a store `K₂` and the renaming `ρ`. -/
def img (ρ : Nat → Nat) (x : ConfigFX H) (K₂ : List (Option ContFX)) : ConfigFX H :=
  ⟨x.store, K₂, x.frame, rnL ρ x.code⟩

/-! ## Runs, divergence, behaviours -/

theorem sim_steps {x y : ConfigFX H} (h : StepsFXR P host fx x y) {K₂ : List (Option ContFX)}
    (hK : KRel ρ B x.conts K₂) (hx : avL B x.code) :
    ∃ K₂', StepsFXR P host fx (img ρ x K₂) (img ρ y K₂') ∧ KRel ρ B y.conts K₂' ∧
      avL B y.code := by
  induction h with
  | refl => exact ⟨K₂, .refl, hK, hx⟩
  | tail _ hs ih =>
    obtain ⟨K₁, hs₁, hK₁, hx₁⟩ := ih
    obtain ⟨K₂', hs₂, hK₂, hx₂⟩ := sim_step hs K₁ hK₁ hx₁
    exact ⟨K₂', hs₁.tail hs₂, hK₂, hx₂⟩

theorem sim_diverges {x : ConfigFX H} (hd : Silmaril.InfiniteTrace (StepFXR P host fx) x)
    {K₂ : List (Option ContFX)} (hK : KRel ρ B x.conts K₂) (hx : avL B x.code) :
    Silmaril.InfiniteTrace (StepFXR P host fx) (img ρ x K₂) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun d => ∃ (x : ConfigFX H) (K₂ : List (Option ContFX)), KRel ρ B x.conts K₂ ∧
      avL B x.code ∧ Silmaril.InfiniteTrace (StepFXR P host fx) x ∧ d = img ρ x K₂) ?_
    ⟨x, K₂, hK, hx, hd, rfl⟩
  rintro _ ⟨x, K₂, hK, hx, hd, rfl⟩
  obtain ⟨y, hy, hdy⟩ := hd.unfold
  obtain ⟨K₂', hs, hK', hy'⟩ := sim_step hy K₂ hK hx
  exact ⟨_, hs, y, K₂', hK', hy', hdy, rfl⟩

/-- **Behaviours are kept by the simulation that ignores consumed slots.** -/
theorem sim_behaviours {x : ConfigFX H} {K₂ : List (Option ContFX)} (hK : KRel ρ B x.conts K₂)
    (hx : avL B x.code) : behavioursFXR P host fx x ⊆ behavioursFXR P host fx (img ρ x K₂) := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨K₂', hs, -, -⟩ := sim_steps hrun hK hx
    refine Or.inl ⟨img ρ d K₂', r, hs, ?_, rfl⟩
    show rnL ρ d.code = _
    rw [hd, rnL_map_core]
  · exact Or.inr ⟨rfl, sim_diverges hdiv hK hx⟩

/-! ## Renaming that fixes the mentioned slots -/

mutual
theorem rnA_id {L : Nat} (hρ : ∀ i < L, ρ i = i) :
    ∀ a : AdminFX, avA (fun i => L ≤ i) a → rnA ρ a = a
  | .core _, _ => rfl
  | .fx _, _ => rfl
  | .block _ _, _ => rfl
  | .loop _ _, _ => rfl
  | .if_ _ _ _, _ => rfl
  | .label _ _ b, h => by simp only [rnA]; rw [rnL_id hρ b h]
  | .frame _ _ b, h => by simp only [rnA]; rw [rnL_id hρ b h]
  | .handler _ b, h => by simp only [rnA]; rw [rnL_id hρ b h]
  | .contRef k, h => by simp only [rnA]; rw [hρ k (Nat.lt_of_not_le h)]
theorem rnL_id {L : Nat} (hρ : ∀ i < L, ρ i = i) :
    ∀ c : List AdminFX, avL (fun i => L ≤ i) c → rnL ρ c = c
  | [], _ => rfl
  | a :: c, h => by simp only [rnL]; rw [rnA_id hρ a h.1, rnL_id hρ c h.2]
end

mutual
theorem avA_mono {B B' : Nat → Prop} (hB : ∀ i, B' i → B i) :
    ∀ a : AdminFX, avA B a → avA B' a
  | .core _, _ => trivial
  | .fx _, _ => trivial
  | .block _ _, _ => trivial
  | .loop _ _, _ => trivial
  | .if_ _ _ _, _ => trivial
  | .label _ _ b, h => avL_mono hB b h
  | .frame _ _ b, h => avL_mono hB b h
  | .handler _ b, h => avL_mono hB b h
  | .contRef k, h => fun hk => h (hB k hk)
theorem avL_mono {B B' : Nat → Prop} (hB : ∀ i, B' i → B i) :
    ∀ c : List AdminFX, avL B c → avL B' c
  | [], _ => trivial
  | a :: c, h => ⟨avA_mono hB a h.1, avL_mono hB c h.2⟩
end

/-! ## Natural continuations -/

/-- **`C` is natural below `L`**: it commutes with every renaming fixing the slots below `L`,
and keeps code away from every set of slots that are all `≥ L`. -/
def ContNat (L : Nat) (C : ContFX) : Prop :=
  ∀ (ρ : Nat → Nat) (B : Nat → Prop), (∀ i < L, ρ i = i) → (∀ i < L, ¬ B i) → ContR ρ B C C

/-- The continuation that `cont.new` builds is natural. -/
theorem contNat_call (L a : Nat) (t : Silmaril.Wasm.Validation.DefType) :
    ContNat L ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType t)]⟩ :=
  fun _ _ _ _ => contR_call a t

/-- A store of natural continuations, with one slot consumed. -/
theorem natural_set {K : List (Option ContFX)} {k : Nat}
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C) :
    ∀ (i : Nat) (C : ContFX), (K.set k none)[i]? = some (some C) → ContNat (K.set k none).length C := by
  intro i C hi
  rw [List.length_set]
  by_cases hik : i = k
  · subst hik
    rw [List.getElem?_set] at hi
    split at hi <;> simp_all
  · rw [getElem?_set_of_ne hik] at hi
    exact hK i C hi

/-! ## The two final configurations -/

section Post

variable {K : List (Option ContFX)} {L : Nat}

/-- The renaming from after bind-then-resume to after the direct resume: drop slot `L`. -/
def dropAt (L : Nat) (i : Nat) : Nat := if i < L + 1 then i else i - 1

/-- The renaming from after the direct resume to after bind-then-resume: skip slot `L`. -/
def skipAt (L : Nat) (i : Nat) : Nat := if i < L then i else i + 1

theorem okContR {i : Nat} {c : Option ContFX} {ρ : Nat → Nat} {B : Nat → Prop}
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C) (hρ : ∀ i < K.length, ρ i = i)
    (hB : ∀ i < K.length, ¬ B i) (hi : K[i]? = some c) : OContR ρ B c c := by
  cases c with
  | none => trivial
  | some C => exact hK i C hi ρ B hρ hB

/-- After bind-then-resume, against after the direct resume. -/
theorem kRel_drop (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C) :
    KRel (dropAt K.length) (· = K.length) (K ++ [none]) K := by
  have hρ : ∀ i < K.length, dropAt K.length i = i := fun i hi => by simp [dropAt]; omega
  refine ⟨?_, fun j => by simp [dropAt], fun j => by simp; omega, ?_⟩
  · intro i c hi hc
    have hlt : i < K.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      simp at this; omega
    rw [List.getElem?_append_left hlt] at hc
    refine ⟨c, by rw [hρ i hlt]; exact hc, okContR hK hρ (fun i hi h => by omega) hc⟩
  · intro i i' hi hi' he
    simp only [dropAt] at he
    split at he <;> split at he <;> omega

/-- After the direct resume, against after bind-then-resume. -/
theorem kRel_skip (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C) :
    KRel (skipAt K.length) (fun _ => False) K (K ++ [none]) := by
  have hρ : ∀ i < K.length, skipAt K.length i = i := fun i hi => by simp [skipAt, hi]
  refine ⟨?_, fun j => by simp [skipAt]; omega, fun _ h => h, ?_⟩
  · intro i c _ hc
    have hlt : i < K.length := (List.getElem?_eq_some_iff.mp hc).1
    refine ⟨c, ?_, okContR hK hρ (fun _ _ h => h) hc⟩
    rw [hρ i hlt, List.getElem?_append_left hlt]
    exact hc
  · intro i i' _ _ he
    simp only [skipAt] at he
    split at he <;> split at he <;> omega

/-- **The two final configurations have the same behaviours.** -/
theorem post_eq {s : Store H} {f : Frame} {c : List AdminFX}
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C)
    (hc : avL (fun i => K.length ≤ i) c) :
    behavioursFXR P host fx ⟨s, K ++ [none], f, c⟩ = behavioursFXR P host fx ⟨s, K, f, c⟩ := by
  have hd : rnL (dropAt K.length) c = c :=
    rnL_id (fun i hi => by simp [dropAt]; omega) c hc
  have hs : rnL (skipAt K.length) c = c := rnL_id (fun i hi => by simp [skipAt, hi]) c hc
  refine Set.Subset.antisymm ?_ ?_
  · have h := sim_behaviours (P := P) (host := host) (fx := fx)
      (x := ⟨s, K ++ [none], f, c⟩) (kRel_drop hK) (avL_mono (fun i h => by omega) c hc)
    simpa [img, hd] using h
  · have h := sim_behaviours (P := P) (host := host) (fx := fx)
      (x := ⟨s, K, f, c⟩) (kRel_skip hK) (avL_mono (fun _ h => h.elim) c hc)
    simpa [img, hs] using h

end Post

/-! ## One successor -/

/-- Behaviours of a configuration with one successor are the successor's. -/
theorem behavioursFXR_of_det {x y₀ : ConfigFX H}
    (hnr : ∀ r : Result, x.code ≠ r.toAdmin.map .core) (hstep : StepFXR P host fx x y₀)
    (hdet : ∀ y, StepFXR P host fx x y → y = y₀) :
    behavioursFXR P host fx x = behavioursFXR P host fx y₀ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
    · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, hrest⟩
      · exact absurd hd (hnr r)
      · exact Or.inl ⟨d, r, hdet y hy ▸ hrest, hd, rfl⟩
    · obtain ⟨y, hy, htr⟩ := hdiv.unfold
      exact Or.inr ⟨rfl, hdet y hy ▸ htr⟩
  · rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact Or.inl ⟨d, r, Relation.ReflTransGen.head hstep hrun, hd, rfl⟩
    · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.fold hstep hdiv⟩

/-- Code with an FX instruction is not a result. -/
theorem not_result_of_fx {c : List AdminFX} {i : FXInstr} (h : AdminFX.fx i ∈ c) :
    ∀ r : Result, c ≠ r.toAdmin.map .core := by
  intro r hr
  rw [hr] at h
  obtain ⟨a, -, ha⟩ := List.mem_map.mp h
  cases ha

/-- **The typed `cont.bind` is deterministic** (no host calls). -/
theorem stepR_bind_det {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal}
    {n : Nat} {ct ct' : TypeIdx} {T : List AdminFX} {y y' : ConfigFX H}
    (h : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.contBind ct ct') :: T⟩ y)
    (h' : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.contBind ct ct') :: T⟩
      y') : y = y' := by
  obtain ⟨V₁, V₂, hV, hA, hy⟩ :=
    Silmaril.Proofs.Wasm.Models.FXBindT.step_contBindT (stepFXR_incl h) V n ct ct' T rfl
  obtain ⟨W₁, W₂, hW, hA', hy'⟩ :=
    Silmaril.Proofs.Wasm.Models.FXBindT.step_contBindT (stepFXR_incl h') V n ct ct' T rfl
  have hlen := Silmaril.Proofs.Wasm.Models.FXBindT.bindArity_unique hA hA'
  obtain ⟨rfl, rfl⟩ := split_eq (hV.symm.trans hW) hlen
  rcases hy with ⟨C, hk, rfl⟩ | ⟨hk, rfl⟩ <;> rcases hy' with ⟨C', hk', rfl⟩ | ⟨hk', rfl⟩
  · rw [hk] at hk'
    cases hk'
    rfl
  · rw [hk] at hk'
    cases hk'
  · rw [hk] at hk'
    cases hk'
  · rfl

/-! ## Bind-then-resume equals the direct resume -/

section Eq

variable {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} {C : ContFX}
  {ct ct' : TypeIdx} {hs : List OnClause} {hs' : List HClause} {ws vs : List FVal}

theorem bindResumeSrc_eq (ws vs : List FVal) (k : Nat) (ct ct' : TypeIdx) (hs : List OnClause) :
    bindResumeSrc ws vs k ct ct' hs =
      fvals (ws ++ vs) ++ .contRef k :: .fx (.contBind ct ct') :: [.fx (.resume ct' hs)] := by
  simp [bindResumeSrc, fvals]

/-- The configuration after the bind. -/
def midCfg (s : Store H) (K : List (Option ContFX)) (f : Frame) (k : Nat) (C : ContFX)
    (vs ws : List FVal) (ct' : TypeIdx) (hs : List OnClause) : ConfigFX H :=
  ⟨s, K.set k none ++ [some (bound C vs)], f, fvals ws ++ [.contRef K.length, .fx (.resume ct' hs)]⟩

theorem src_eq_mid (hk : K[k]? = some (some C)) (hb : BindArity f.module ct ct' vs.length) :
    behavioursFXR P noHost fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩ =
      behavioursFXR P noHost fx (midCfg s K f k C vs ws ct' hs) := by
  have hstep : StepFXR P noHost fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      (midCfg s K f k C vs ws ct' hs) := bind_resume_bindR hk hb
  refine behavioursFXR_of_det (not_result_of_fx (i := .resume ct' hs) (by simp [bindResumeSrc]))
    hstep ?_
  intro y hy
  rw [bindResumeSrc_eq] at hy hstep
  exact stepR_bind_det hy hstep

theorem mid_eq_post (hr : hs.mapM (resolve s f) = some hs')
    (ha : ResumeArity f.module ct' ws.length) :
    behavioursFXR P noHost fx (midCfg s K f k C vs ws ct' hs) =
      behavioursFXR P noHost fx
        ⟨s, K.set k none ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have hstep := bind_resume_resumeR (P := P) (host := noHost) (fx := fx) (K' := K.set k none)
    (C := C) (vs := vs) (ws := ws) (ct' := ct') hr ha
  rw [List.length_set] at hstep
  refine behavioursFXR_of_det (not_result_of_fx (i := .resume ct' hs) (by simp [midCfg]))
    hstep ?_
  intro y hy
  exact stepR_resume_det (T := []) hy hstep

theorem direct_eq_post (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (hb : BindArity f.module ct ct' vs.length) (ha : ResumeArity f.module ct' ws.length) :
    behavioursFXR P noHost fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩ =
      behavioursFXR P noHost fx
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have hstep := resume_directR (P := P) (host := noHost) (fx := fx) (s := s) (K := K) (f := f)
    (hs := hs) (hs' := hs') (ws := ws) (vs := vs) hk hr hb ha
  refine behavioursFXR_of_det (not_result_of_fx (i := .resume ct hs) (by simp)) hstep ?_
  intro y hy
  exact stepR_resume_det (T := []) hy hstep

/-- **Bind-then-resume has exactly the behaviours of the direct resume** (`StepFXR`, no host
calls), for a store of natural continuations and arguments mentioning existing slots only. -/
theorem bind_resume_eq (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (hb : BindArity f.module ct ct' vs.length) (ha : ResumeArity f.module ct' ws.length)
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C)
    (hV : avL (fun i => K.length ≤ i) (fvals (vs ++ ws))) :
    behavioursFXR P noHost fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩ =
      behavioursFXR P noHost fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩ := by
  rw [src_eq_mid hk hb, mid_eq_post hr ha, direct_eq_post hk hr hb ha]
  have hK' := natural_set (k := k) hK
  have hlen : (K.set k none).length = K.length := List.length_set
  have hC : ContNat K.length C := hK k C hk
  have hcode : avL (fun i => (K.set k none).length ≤ i)
      [.handler hs' (C.plug (fvals (vs ++ ws)))] := by
    rw [hlen]
    exact ⟨(hC id _ (fun _ _ => rfl) (fun i hi h => by omega) _ hV).1, trivial⟩
  exact post_eq hK' hcode

/-- The `cont.new` continuation of `a` at type `t`. -/
def callCont (a : Nat) (t : Silmaril.Wasm.Validation.DefType) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType t)]⟩

/-- **An instance**: a store holding one `cont.new` continuation, Core arguments. The
hypotheses of `bind_resume_eq` hold. -/
theorem bind_resume_eq_call {a : Nat} {t : Silmaril.Wasm.Validation.DefType} {Vs Ws : List Val}
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' (liftV Vs).length)
    (ha : ResumeArity f.module ct' (liftV Ws).length) :
    behavioursFXR P noHost fx ⟨s, [some (callCont a t)], f, bindResumeSrc (liftV Ws) (liftV Vs) 0 ct ct' hs⟩ =
      behavioursFXR P noHost fx
        ⟨s, [some (callCont a t)], f, fvals (liftV Vs ++ liftV Ws) ++ [.contRef 0, .fx (.resume ct hs)]⟩ := by
  refine bind_resume_eq rfl hr hb ha ?_ ?_
  · intro i C hi
    have hi0 : i = 0 := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simpa using this
    subst hi0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact contNat_call _ a t
  · have he : liftV Vs ++ liftV Ws = liftV (Vs ++ Ws) := by simp [liftV]
    rw [he, fvals_liftV]
    exact avL_cvals _

end Eq

end Silmaril.Proofs.Wasm.Models.FXResumeT
