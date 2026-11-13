module

public import Silmaril.Proofs.Wasm.Det.NaN.Step
public import Silmaril.Wasm.Det.Core.Thms

/-!
# Runs of the fragment agree up to NaN payloads (proofs)

`CStep set` is a step of the deterministic profile `Pc` from a configuration of the fragment,
followed by canonicalisation. By `step_good`, every host-free step at an arbitrary profile
`P` of a fragment configuration `c` is mapped to a `CStep` from `canonCfg c` (`cstep_of_step`),
and `CStep` has silmaril-lean's one-step diamond (`cstep_join`, from `Det.DStep.join'`), so its
normal forms are unique (`nf_unique_of_join`). Non-trapping stops are normal forms and keep
their kind under canonicalisation (`outAt_canon`), and resuming the same import call with the
same answer keeps two configurations with the same canonical image together (`resume_canon`).

* `runs_canon`: two runs from configurations with the same canonical image, with the same
  import calls and answers, that both reach non-trapping stops, reach stops with the same
  canonical image;
* `nanDetCfg_of_nCfg`: hence `NaNDetCfg P c` for every fragment configuration, at every `P`;
* `runs_store`: without `global.set`, runs keep the store;
* `eq_of_canonOut`: outputs equal up to NaN payloads, one of them NaN-free, are equal;
* `nanFreeOut_of_canonical`: the output sink condition holds as soon as one run at the
  deterministic profile `Pc` returns a NaN-free result.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.NaN
open Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

variable {set : Bool}

/-- A step of the deterministic profile from a fragment configuration, canonicalised. -/
def CStep (set : Bool) (a b : Config Nat) : Prop :=
  NCfg set a ∧ ∃ e, Step Pc Det.noHost a e ∧ canonCfg e = b

theorem cstep_of_step {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c')
    (hc : NCfg set c) : CStep set (canonCfg c) (canonCfg c') :=
  ⟨nCfg_canon.mpr hc, (step_good h hc).proj⟩

theorem nCfg_steps {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hc : NCfg set c) : NCfg set d := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact (step_good hs ih).inv

theorem csteps_of_steps {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hc : NCfg set c) : Relation.ReflTransGen (CStep set) (canonCfg c) (canonCfg d) := by
  induction h with
  | refl => exact .refl
  | tail hcd hs ih => exact ih.tail (cstep_of_step hs (nCfg_steps hcd hc))

/-- **The one-step diamond of canonical steps** (silmaril-lean's `Det.DStep.join'`). -/
theorem cstep_join {x a b : Config Nat} (ha : CStep set x a) (hb : CStep set x b) :
    Det.Join (CStep set) a b := by
  obtain ⟨hx, e₁, h₁, rfl⟩ := ha
  obtain ⟨-, e₂, h₂, rfl⟩ := hb
  obtain ⟨z, hz₁, hz₂⟩ := Det.DStep.join' (o := neverFail) h₁ h₂
  have he₁ : NCfg set e₁ := (step_good h₁ hx).inv
  have he₂ : NCfg set e₂ := (step_good h₂ hx).inv
  refine ⟨canonCfg z, ?_, ?_⟩
  · cases hz₁ with
    | refl => exact .refl
    | single h => exact .single (cstep_of_step h he₁)
  · cases hz₂ with
    | refl => exact .refl
    | single h => exact .single (cstep_of_step h he₂)

/-- A canonicalised non-trapping stop has the canonicalised output. -/
theorem outAt_canon {d : Config Nat} {o : Out} (h : OutAt d o) : OutAt (canonCfg d) (canonOut o) := by
  cases h with
  | @ret r hr hc =>
    refine .ret (r := canonResult r) ?_ ?_
    · cases r <;> simp_all [canonResult]
    · show canonAdmins d.code = _
      rw [hc]
      cases r <;> simp [Result.toAdmin, canonResult, canonInstr]
  | @call E a h args hd =>
    refine .call (E := canonCtx E) (a := a) ?_
    show decompose? (canonStore d.store) (canonAdmins d.code) = _
    rw [decompose?_congr (canonStore_funcs d.store), decompose?_canon, hd]
    rfl

theorem stop_canon {d : Config Nat} (h : Stop d) : Stop (canonCfg d) :=
  ⟨_, outAt_canon h.choose_spec⟩

theorem cstep_normal {d : Config Nat} (h : Stop d) : ∀ w, ¬ CStep set (canonCfg d) w :=
  fun _ ⟨_, _, he, _⟩ => Stop.no_step (stop_canon h) he

/-- **Host-free runs to non-trapping stops from configurations with the same canonical image
end at stops with the same canonical image.** -/
theorem segs_canon {P : Profile} {x y dx dy : Config Nat} (hx : NCfg set x) (hy : NCfg set y)
    (hxy : canonCfg x = canonCfg y) (h₁ : Steps P Det.noHost x dx) (h₂ : Steps P Det.noHost y dy)
    (s₁ : Stop dx) (s₂ : Stop dy) : canonCfg dx = canonCfg dy := by
  have r₁ : Relation.ReflTransGen (CStep set) (canonCfg x) (canonCfg dx) := csteps_of_steps h₁ hx
  have r₂ : Relation.ReflTransGen (CStep set) (canonCfg x) (canonCfg dy) := by
    rw [hxy]
    exact csteps_of_steps h₂ hy
  exact nf_unique_of_join (fun ha hb => cstep_join ha hb) r₁ r₂ (cstep_normal s₁)
    (cstep_normal s₂)

/-- Fragment code around a hole stays fragment code when the hole is refilled. -/
theorem nAdms_fill : ∀ (E : Ctx) {xs ys : List Admin}, NAdms set (E.fill xs) → NAdms set ys →
    NAdms set (E.fill ys)
  | .top pre rest, xs, ys, h, hy => by
    have h' := nAdms_append.mp (nAdms_append.mp h).1
    simp only [Ctx.fill, nAdms_append]
    exact ⟨⟨h'.1, hy⟩, (nAdms_append.mp h).2⟩
  | .label pre n cont E rest, xs, ys, h, hy => by
    have h' := nAdms_append.mp h
    have h'' := nAdms_append.mp h'.1
    have hl : NAdm set (.label n cont (E.fill xs)) := h''.2.1
    simp only [Ctx.fill, nAdms_append, nAdms_cons, nAdms_nil, and_true]
    exact ⟨⟨h''.1, hl.1, nAdms_fill E hl.2 hy⟩, h'.2⟩
  | .handler pre n cs E rest, xs, ys, h, _ => by
    have h' := nAdms_append.mp (nAdms_append.mp h).1
    exact h'.2.1.elim
  | .frame pre n f E rest, xs, ys, h, hy => by
    have h' := nAdms_append.mp h
    have h'' := nAdms_append.mp h'.1
    have hl : NAdm set (.frame n f (E.fill xs)) := h''.2.1
    simp only [Ctx.fill, nAdms_append, nAdms_cons, nAdms_nil, and_true]
    exact ⟨⟨h''.1, nAdms_fill E hl hy⟩, h'.2⟩

theorem nAdms_result (r : Result) : NAdms set r.toAdmin := by
  cases r <;> simp [Result.toAdmin, NAdm, nanInstr, floatOk]

/-- Resuming an import call keeps the fragment. -/
theorem nCfg_resume {d : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} (hd : NCfg set d)
    (hdec : decompose? d.store d.code = some (E, a, h, args)) (r : Result) :
    NCfg set (resumeAt d E r) := by
  obtain ⟨fi, yy, ps, rs, -, -, -, -, -, hcode⟩ := decompose?_sound hdec
  have h₁ : NAdms set (E.fill (vals args ++ [.ref (.func a), yy])) := hcode ▸ hd.1
  exact ⟨nAdms_fill E h₁ (nAdms_result r), hd.2⟩

/-- Resuming the same import call with the same answer keeps the canonical images equal. -/
theorem resume_canon {d₁ d₂ : Config Nat} (h : canonCfg d₁ = canonCfg d₂) {E₁ E₂ : Ctx}
    {a₁ a₂ hh : Nat} {args : List Val}
    (hd₁ : decompose? d₁.store d₁.code = some (E₁, a₁, hh, args))
    (hd₂ : decompose? d₂.store d₂.code = some (E₂, a₂, hh, args)) (r : Result) :
    canonCfg (resumeAt d₁ E₁ r) = canonCfg (resumeAt d₂ E₂ r) := by
  have hs : canonStore d₁.store = canonStore d₂.store := congrArg Config.store h
  have hf : canonFrame d₁.frame = canonFrame d₂.frame := congrArg Config.frame h
  have hc : canonAdmins d₁.code = canonAdmins d₂.code := congrArg Config.code h
  have e₁ : decompose? d₁.store (canonAdmins d₁.code) = some (canonRedex (E₁, a₁, hh, args)) := by
    rw [decompose?_canon, hd₁]
    rfl
  have e₂ : decompose? d₁.store (canonAdmins d₂.code) = some (canonRedex (E₂, a₂, hh, args)) := by
    rw [decompose?_congr (s' := d₁.store) (s := d₂.store) (by
      rw [← canonStore_funcs d₁.store, hs, canonStore_funcs]), decompose?_canon, hd₂]
    rfl
  have hE : canonCtx E₁ = canonCtx E₂ := by
    rw [hc] at e₁
    have he := e₁.symm.trans e₂
    simp only [canonRedex, Option.some.injEq, Prod.mk.injEq] at he
    exact he.1
  simp only [canonCfg, resumeAt, canonCtx_fill, hs, hf, hE]

/-- **Runs with the same calls agree up to NaN payloads.** -/
theorem runs_canon {P : Profile} : ∀ (tr : List Call) {x y dx dy : Config Nat}, NCfg set x →
    NCfg set y → canonCfg x = canonCfg y → Runs P x tr dx → Runs P y tr dy → Stop dx →
    Stop dy → canonCfg dx = canonCfg dy
  | [], _, _, _, _, hx, hy, hxy, .stop h₁, .stop h₂, s₁, s₂ => segs_canon hx hy hxy h₁ h₂ s₁ s₂
  | _ :: tr, _, _, _, _, hx, hy, hxy, .call h₁ hd₁ hk₁, .call h₂ hd₂ hk₂, s₁, s₂ => by
    have he : canonCfg _ = canonCfg _ :=
      segs_canon hx hy hxy h₁ h₂ ⟨_, .call hd₁⟩ ⟨_, .call hd₂⟩
    exact runs_canon tr (nCfg_resume (nCfg_steps h₁ hx) hd₁ _) (nCfg_resume (nCfg_steps h₂ hy) hd₂ _)
      (resume_canon he hd₁ hd₂ _) hk₁ hk₂ s₁ s₂

/-- **Every fragment configuration is deterministic up to NaN payloads**, at every profile. -/
theorem nanDetCfg_of_nCfg {P : Profile} {c : Config Nat} (hc : NCfg set c) : NaNDetCfg P c := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have he : canonCfg d₁ = canonCfg d₂ := runs_canon tr hc hc rfl h₁ h₂ ⟨_, ho₁⟩ ⟨_, ho₂⟩
  have hu₁ : OutAt (canonCfg d₁) (canonOut o₁) := outAt_canon ho₁
  have hu₂ : OutAt (canonCfg d₁) (canonOut o₂) := he ▸ outAt_canon ho₂
  exact ⟨OutAt.unique hu₁ hu₂, congrArg Config.store he⟩

/-- **Without `global.set`, runs of the fragment keep the store.** -/
theorem runs_store {P : Profile} : ∀ {c d : Config Nat} {tr : List Call}, NCfg false c →
    Runs P c tr d → d.store = c.store
  | _, _, _, hc, .stop h => steps_store hc h
  | c, d, _, hc, @Runs.call _ _ e _ E _ _ _ r _ h hd hk => by
    have h₁ : d.store = (resumeAt e E r).store := runs_store (nCfg_resume (nCfg_steps h hc) hd _) hk
    have h₂ : e.store = c.store := steps_store hc h
    exact h₁.trans h₂
where
  steps_store {c d : Config Nat} (hc : NCfg false c) (h : Steps P Det.noHost c d) :
      d.store = c.store := by
    induction h with
    | refl => rfl
    | tail hcd hs ih => exact ((step_good hs (nCfg_steps hcd hc)).store rfl).trans ih

/-! ## Outputs -/

theorem nanBits_false {t : NumType} {b : BitVec t.width} (h : nanBits t b = false)
    {b' : BitVec t.width} (he : canonBits t b' = canonBits t b) : b' = b := by
  rcases t with t | t
  · exact he
  · cases t
    · have hn : ¬ (Numerics.asF32 b).IsNaN := by
        simpa [nanBits, Silmaril.Numeric.Ieee754.F32.isNaN] using h
      exact canon32_inj he.symm hn
    · have hn : ¬ (Numerics.asF64 b).IsNaN := by
        simpa [nanBits, Silmaril.Numeric.Ieee754.F64.isNaN] using h
      exact canon64_inj he.symm hn

/-- A value that is not a NaN is determined by its canonical image. -/
theorem canonVal_inj {v w : Val} (h : canonVal w = canonVal v) (hv : nanVal v = false) :
    w = v := by
  match v, w, h with
  | .num ⟨t, b⟩, .num ⟨t', b'⟩, h =>
    have h₁ : (⟨t', canonBits t' b'⟩ : NumVal) = ⟨t, canonBits t b⟩ := Val.num.inj h
    obtain ⟨rfl, hb⟩ := (NumVal.mk.injEq _ _ _ _).mp h₁
    have hb' : canonBits t' b' = canonBits t' b := eq_of_heq hb
    rw [nanBits_false hv hb']
  | .vec b, .vec b', h => exact h
  | .ref r, .ref r', h => exact h
  | .num ⟨_, _⟩, .vec _, h => cases h
  | .num ⟨_, _⟩, .ref _, h => cases h
  | .vec _, .num ⟨_, _⟩, h => cases h
  | .vec _, .ref _, h => cases h
  | .ref _, .num ⟨_, _⟩, h => cases h
  | .ref _, .vec _, h => cases h

theorem canonVals_inj : ∀ {vs ws : List Val}, ws.map canonVal = vs.map canonVal →
    (∀ v ∈ vs, nanVal v = false) → ws = vs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | v :: vs, w :: ws, h, hv => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [canonVal_inj h.1 (hv v List.mem_cons_self),
      canonVals_inj h.2 (fun u hu => hv u (List.mem_cons_of_mem _ hu))]

/-- **Outputs equal up to NaN payloads, one of them NaN-free, are equal.** -/
theorem eq_of_canonOut {o₁ o₂ : Out} (h : canonOut o₁ = canonOut o₂) (hf : OutNaNFree o₁) :
    o₂ = o₁ := by
  rcases o₁ with r₁ | ⟨h₁, a₁⟩ <;> rcases o₂ with r₂ | ⟨h₂, a₂⟩ <;>
    simp only [canonOut, Out.ret.injEq, Out.call.injEq, reduceCtorEq] at h
  · rcases r₁ with vs₁ | e₁ | _ <;> rcases r₂ with vs₂ | e₂ | _ <;>
      simp only [canonResult, Result.values.injEq, reduceCtorEq] at h
    · rw [canonVals_inj h.symm hf]
    · rw [h]
    · rfl
  · rw [h.1, canonVals_inj h.2.symm hf]

theorem nanVal_canon : ∀ v : Val, nanVal (canonVal v) = nanVal v
  | .num ⟨.int _, _⟩ => rfl
  | .num ⟨.float .f32, b⟩ => by
    by_cases hb : (Numerics.asF32 b).IsNaN
    · have h₁ : canonVal (.num ⟨.float .f32, b⟩) = .num ⟨.float .f32, nan32⟩ := by
        simp only [canonVal, canonBits, canon32_nan hb]
      rw [h₁]
      simp [nanVal, nanBits, Silmaril.Numeric.Ieee754.F32.isNaN, hb, nan32_isNaN]
    · have h₁ : canonVal (.num ⟨.float .f32, b⟩) = .num ⟨.float .f32, b⟩ := by
        simp only [canonVal, canonBits, canon32_ok hb]
      rw [h₁]
  | .num ⟨.float .f64, b⟩ => by
    by_cases hb : (Numerics.asF64 b).IsNaN
    · have h₁ : canonVal (.num ⟨.float .f64, b⟩) = .num ⟨.float .f64, nan64⟩ := by
        simp only [canonVal, canonBits, canon64_nan hb]
      rw [h₁]
      simp [nanVal, nanBits, Silmaril.Numeric.Ieee754.F64.isNaN, hb, nan64_isNaN]
    · have h₁ : canonVal (.num ⟨.float .f64, b⟩) = .num ⟨.float .f64, b⟩ := by
        simp only [canonVal, canonBits, canon64_ok hb]
      rw [h₁]
  | .vec _ => rfl
  | .ref _ => rfl

theorem outNaNFree_canon {o : Out} (h : OutNaNFree (canonOut o)) : OutNaNFree o := by
  rcases o with ⟨vs | e | _⟩ | ⟨hh, args⟩
  · intro v hv
    have h₁ := h (canonVal v) (List.mem_map_of_mem hv)
    rwa [nanVal_canon] at h₁
  · trivial
  · trivial
  · intro v hv
    have h₁ := h (canonVal v) (List.mem_map_of_mem hv)
    rwa [nanVal_canon] at h₁

/-- The outputs of `canonOut (.ret r)` are NaN-free when those of `.ret r` are. -/
theorem outNaNFree_canonOut {r : Result} (hf : OutNaNFree (.ret r)) :
    OutNaNFree (canonOut (.ret r)) := by
  rcases r with vs | _ | _
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [nanVal_canon]
    exact hf w hw
  · trivial
  · trivial

/-- **The output sink from one run of the deterministic profile.** If a run of `c` at `Pc`
returns a result (not an import call) whose values are not NaNs, every run of `c` at every
profile, with any import calls, stops only at NaN-free outputs (in fact it makes no import
call). -/
theorem nanFreeOut_of_canonical {P : Profile} {c n : Config Nat} (hc : NCfg set c)
    (hn : Steps Pc Det.noHost c n) {r : Result} (hr : OutAt n (.ret r))
    (hf : OutNaNFree (.ret r)) : NaNFreeOut P c := by
  have rn : Relation.ReflTransGen (CStep set) (canonCfg c) (canonCfg n) := csteps_of_steps hn hc
  have hu₂ : OutAt (canonCfg n) (canonOut (.ret r)) := outAt_canon hr
  have seg : ∀ d, Steps P Det.noHost c d → Stop d → canonCfg d = canonCfg n := fun d h hd =>
    nf_unique_of_join (fun ha hb => cstep_join ha hb) (csteps_of_steps h hc) rn
      (cstep_normal hd) (cstep_normal ⟨_, hr⟩)
  intro tr d o hd ho
  cases hd with
  | stop h =>
    have hu₁ : OutAt (canonCfg n) (canonOut o) := seg d h ⟨_, ho⟩ ▸ outAt_canon ho
    have ho' : canonOut o = canonOut (.ret r) := OutAt.unique hu₁ hu₂
    exact outNaNFree_canon (ho' ▸ outNaNFree_canonOut hf)
  | call h hd _ =>
    have hu₁ : OutAt (canonCfg n) _ := seg _ h ⟨_, .call hd⟩ ▸ outAt_canon (.call hd)
    exact absurd (OutAt.unique hu₁ hu₂) (by simp [canonOut])

end Silmaril.Proofs.Wasm.Det.NaN
