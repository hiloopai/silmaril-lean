module

public import Silmaril.Proofs.Wasm.Det.Stateless.Step
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Stateless code: runs, determinism and statelessness (proofs)

* `inv_step`, `inv_resume`, `inv_invoke`: the invariant `Inv` is closed under host-free steps
  and under resuming an import call with any answer, and holds of the invocation of a function
  of `A`;
* `detCfg_of_inv`: an `Inv` configuration is deterministic modulo traps and imports at every
  profile (its steps are steps of the deterministic profile `profile o`);
* `runs_swap`: a run (with import calls) from an `Inv` configuration is a run, with the same
  frames, code and calls, from the same frame and code in any store agreeing on the functions
  and the globals of `R`;
* `obsAgree_of_agree`: hence two such configurations agree on their non-trapping outputs;
* `runs_outside`: a run changes only the globals of `W`;
* the per-function and per-module consequences (`detFn_of_good`, `statelessFn_of_good`,
  `callReach_outside`, `statelessFn_callReach`, `statelessModule_of_good`,
  `detModule_of_good`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Stateless
  Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

variable {A R W : Nat → Bool}

/-! ## The invariant -/

theorem inv_step {P : Profile} {c c' : Config Nat} (hc : Inv A R W c)
    (h : Step P Det.noHost c c') : Inv A R W c' ∧ SStep A R W none c c' := by
  have hS : SStep A R W none c c' := step_sl h hc.1 hc.2.1 none hc.2.2
  obtain ⟨e, -, hs, -⟩ := hS.eff
  have hf : c'.store.funcs = c.store.funcs := by rw [hs, Eff.app_funcs]
  exact ⟨⟨hf ▸ hc.1, hS.ok, hS.pair⟩, hS⟩

/-- Replacing a host-call redex by an answer keeps the invariant. -/
theorem fill_resume {m : ModuleInst} {q : Option Admin} (E : Ctx) {args : List Val} {a : Nat}
    {yy : Admin} (hyy : yy.IsCallRef) (r : Result)
    (hok : okL A R W m (E.fill (vals args ++ [.ref (.func a), yy])))
    (hp : PairedFrom A q (E.fill (vals args ++ [.ref (.func a), yy]))) :
    okL A R W m (E.fill r.toAdmin) ∧ PairedFrom A q (E.fill r.toAdmin) := by
  induction E generalizing m q with
  | top pre rest =>
    show okL A R W m (vals pre ++ r.toAdmin ++ rest) ∧ PairedFrom A q (vals pre ++ r.toAdmin ++ rest)
    have hok₀ : okL A R W m (vals pre ++ (vals args ++ [.ref (.func a), yy]) ++ rest) := hok
    have hp₀ : PairedFrom A q (vals pre ++ (vals args ++ [.ref (.func a), yy]) ++ rest) := hp
    have hok' : okL A R W m rest := (okL_append.mp hok₀).2
    have hp₁ : PairedFrom A (lastOr q (vals pre ++ (vals args ++ [.ref (.func a), yy]))) rest :=
      (pairedFrom_append.mp hp₀).2
    have hl : lastOr q (vals pre ++ (vals args ++ [.ref (.func a), yy])) = some yy := by
      rw [lastOr_append]; exact lastOr_callRef
    have hrest : PairedFrom A (lastOr q (vals pre ++ r.toAdmin)) rest :=
      pairedFrom_head (hl ▸ hp₁) (not_blk_callRef hyy)
    have hp' : PairedFrom A q (vals pre ++ r.toAdmin ++ rest) :=
      pairedFrom_append.mpr ⟨pairedFrom_append.mpr ⟨pairedFrom_vals _ _, pairedFrom_toAdmin _ _⟩,
        hrest⟩
    have hok'' : okL A R W m (vals pre ++ r.toAdmin ++ rest) :=
      okL_append.mpr ⟨okL_append.mpr ⟨okL_vals _, okL_toAdmin _⟩, hok'⟩
    exact ⟨hok'', hp'⟩
  | label pre n cont E rest ih =>
    show okL A R W m (vals pre ++ [.label n cont (E.fill r.toAdmin)] ++ rest) ∧
      PairedFrom A q (vals pre ++ [.label n cont (E.fill r.toAdmin)] ++ rest)
    have hok₀ : okL A R W m (vals pre ++
        [.label n cont (E.fill (vals args ++ [.ref (.func a), yy]))] ++ rest) := hok
    have hp₀ : PairedFrom A q (vals pre ++
        [.label n cont (E.fill (vals args ++ [.ref (.func a), yy]))] ++ rest) := hp
    have hl : slInstrs A R W m cont = true ∧
        okL A R W m (E.fill (vals args ++ [.ref (.func a), yy])) ∧
        PairedFrom A none (E.fill (vals args ++ [.ref (.func a), yy])) :=
      (okL_append.mp (okL_append.mp hok₀).1).2.1
    have hin : okL A R W m (E.fill r.toAdmin) ∧ PairedFrom A none (E.fill r.toAdmin) :=
      ih hl.2.1 hl.2.2
    have hn : ¬ Blk A (lastOr q (vals pre ++
        [.label n cont (E.fill (vals args ++ [.ref (.func a), yy]))])) := by simp [Blk]
    have hrest : PairedFrom A (lastOr q (vals pre ++ [.label n cont (E.fill r.toAdmin)])) rest :=
      pairedFrom_head (pairedFrom_append.mp hp₀).2 hn
    have hp' : PairedFrom A q (vals pre ++ [.label n cont (E.fill r.toAdmin)] ++ rest) :=
      pairedFrom_append.mpr ⟨pairedFrom_append.mpr ⟨pairedFrom_vals _ _,
        fun h => absurd h (by simp), trivial⟩, hrest⟩
    have hok' : okL A R W m (vals pre ++ [.label n cont (E.fill r.toAdmin)] ++ rest) :=
      okL_append.mpr ⟨okL_append.mpr ⟨okL_vals _, ⟨hl.1, hin.1, hin.2⟩, trivial⟩,
        (okL_append.mp hok₀).2⟩
    exact ⟨hok', hp'⟩
  | handler pre n cs E rest _ =>
    have hok₀ : okL A R W m (vals pre ++
        [.handler n cs (E.fill (vals args ++ [.ref (.func a), yy]))] ++ rest) := hok
    exact (okA_handler (okL_append.mp (okL_append.mp hok₀).1).2.1).elim
  | frame pre n f E rest ih =>
    show okL A R W m (vals pre ++ [.frame n f (E.fill r.toAdmin)] ++ rest) ∧
      PairedFrom A q (vals pre ++ [.frame n f (E.fill r.toAdmin)] ++ rest)
    have hok₀ : okL A R W m (vals pre ++
        [.frame n f (E.fill (vals args ++ [.ref (.func a), yy]))] ++ rest) := hok
    have hp₀ : PairedFrom A q (vals pre ++
        [.frame n f (E.fill (vals args ++ [.ref (.func a), yy]))] ++ rest) := hp
    have hl : okL A R W f.module (E.fill (vals args ++ [.ref (.func a), yy])) ∧
        PairedFrom A none (E.fill (vals args ++ [.ref (.func a), yy])) :=
      (okL_append.mp (okL_append.mp hok₀).1).2.1
    have hin : okL A R W f.module (E.fill r.toAdmin) ∧ PairedFrom A none (E.fill r.toAdmin) :=
      ih hl.1 hl.2
    have hn : ¬ Blk A (lastOr q (vals pre ++
        [.frame n f (E.fill (vals args ++ [.ref (.func a), yy]))])) := by simp [Blk]
    have hrest : PairedFrom A (lastOr q (vals pre ++ [.frame n f (E.fill r.toAdmin)])) rest :=
      pairedFrom_head (pairedFrom_append.mp hp₀).2 hn
    have hp' : PairedFrom A q (vals pre ++ [.frame n f (E.fill r.toAdmin)] ++ rest) :=
      pairedFrom_append.mpr ⟨pairedFrom_append.mpr ⟨pairedFrom_vals _ _,
        fun h => absurd h (by simp), trivial⟩, hrest⟩
    have hok' : okL A R W m (vals pre ++ [.frame n f (E.fill r.toAdmin)] ++ rest) :=
      okL_append.mpr ⟨okL_append.mpr ⟨okL_vals _, ⟨hin.1, hin.2⟩, trivial⟩,
        (okL_append.mp hok₀).2⟩
    exact ⟨hok', hp'⟩

theorem inv_resume {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} (r : Result)
    (hc : Inv A R W c) (hd : decompose? c.store c.code = some (E, a, h, args)) :
    Inv A R W (resumeAt c E r) := by
  obtain ⟨fi, yy, ps, rs, -, -, hyy, -, -, hcode⟩ := decompose?_sound hd
  have hok : okL A R W c.frame.module (E.fill (vals args ++ [.ref (.func a), yy])) :=
    hcode ▸ hc.2.1
  have hp : PairedFrom A none (E.fill (vals args ++ [.ref (.func a), yy])) := hcode ▸ hc.2.2
  have h' := fill_resume E hyy r hok hp
  exact ⟨hc.1, h'.1, h'.2⟩

theorem inv_invoke {s : Store Nat} {a : Nat} (vs : List Val) (hg : GoodFuns A R W s.funcs)
    (ha : A a = true) : Inv A R W (invoke s a vs) := by
  refine ⟨hg, ?_, ?_⟩
  · simp [invoke]
  · refine pairedFrom_append.mpr ⟨pairedFrom_vals _ _, ?_⟩
    exact ⟨fun h => absurd h (by simp), fun _ => ha, trivial⟩

/-- The invariant is closed (`Silmaril.Wasm.Det.Core.Closed`). -/
theorem inv_closed (P : Profile) : Closed P (Inv A R W) :=
  ⟨fun _ _ hc h => (inv_step hc h).1, fun _ _ _ _ _ r hc hd => inv_resume r hc hd⟩

/-! ## Determinism -/

/-- A grow oracle (any will do: subset code never grows anything). -/
def anyOracle : GrowOracle := fun _ _ _ _ => false

/-- A step of subset code is a step of every profile. -/
theorem step_profile {P P' : Profile} {c c' : Config Nat} (hc : Inv A R W c)
    (h : Step P Det.noHost c c') : Step P' Det.noHost c c' := by
  obtain ⟨-, hS⟩ := inv_step hc h
  obtain ⟨e, -, hs, hst⟩ := hS.eff
  have h₁ : Step P' Det.noHost ⟨c.store, c.frame, c.code⟩ ⟨e.app c.store, c'.frame, c'.code⟩ :=
    hst P' c.store (Agree.refl R c.store)
  rw [← hs] at h₁
  exact h₁

/-- **Subset code is deterministic modulo traps and imports**, at every profile. -/
theorem detCfg_of_inv {P : Profile} {c : Config Nat} (hc : Inv A R W c) : DetCfg P c :=
  detCfg_of_detUpTo (o := anyOracle) (inv_closed P)
    (fun _ hd _ he => .inl (step_profile hd he)) hc

/-! ## Runs in agreeing stores -/

/-- The same frame and code in the store `t`. -/
def swapStore (t : Store Nat) (c : Config Nat) : Config Nat := ⟨t, c.frame, c.code⟩

theorem steps_swap {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hc : Inv A R W c) {t : Store Nat} (ht : Agree R t c.store) :
    ∃ dt, Steps P Det.noHost (swapStore t c) (swapStore dt d) ∧ Agree R dt d.store ∧
      Inv A R W d := by
  induction h with
  | refl => exact ⟨t, .refl, ht, hc⟩
  | tail _ hs ih =>
    obtain ⟨dt, hst, hag, hinv⟩ := ih
    obtain ⟨hinv', hS⟩ := inv_step hinv hs
    obtain ⟨e, -, he, hstep⟩ := hS.eff
    have hag' : Agree R (e.app dt) _ := he ▸ Agree.app e hag
    exact ⟨e.app dt, hst.tail (hstep P dt hag), hag', hinv'⟩

theorem runs_swap {P : Profile} {c d : Config Nat} {tr : List Call} (h : Runs P c tr d)
    (hc : Inv A R W c) {t : Store Nat} (ht : Agree R t c.store) :
    ∃ dt, Runs P (swapStore t c) tr (swapStore dt d) ∧ Agree R dt d.store := by
  induction h generalizing t with
  | stop hs =>
    obtain ⟨dt, hst, hag, -⟩ := steps_swap hs hc ht
    exact ⟨dt, .stop hst, hag⟩
  | @call c d e E a hh args r tr hs hd hk ih =>
    obtain ⟨dt, hst, hag, hinv⟩ := steps_swap hs hc ht
    have hd' : decompose? (swapStore dt d).store (swapStore dt d).code = some (E, a, hh, args) :=
      (decompose?_congr hag.1 d.code).trans hd
    obtain ⟨et, hk', hag'⟩ := ih (inv_resume r hinv hd) (t := dt) hag
    exact ⟨et, .call hst hd' hk', hag'⟩

theorem outAt_swap {d : Config Nat} {o : Out} (h : OutAt d o) {t : Store Nat}
    (ht : t.funcs = d.store.funcs) : OutAt (swapStore t d) o := by
  cases h with
  | ret hr hc => exact .ret hr hc
  | call hd => exact .call ((decompose?_congr ht _).trans hd)

/-- **Statelessness for agreeing stores**: subset code from the same frame and code in two stores
agreeing on the functions and the globals of `R` has the same non-trapping outputs against the
same answers, at every profile. -/
theorem obsAgree_of_agree {P : Profile} {c₁ c₂ : Config Nat} (hc : Inv A R W c₁)
    (hag : Agree R c₁.store c₂.store) (hf : c₁.frame = c₂.frame) (hcode : c₁.code = c₂.code) :
    ObsAgree P c₁ c₂ := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have hc₂ : Inv A R W c₂ := ⟨hag.1 ▸ hc.1, hf ▸ hcode ▸ hc.2.1, hcode ▸ hc.2.2⟩
  obtain ⟨dt, hrun, hag'⟩ := runs_swap h₂ hc₂ hag
  have hc₁ : swapStore c₁.store c₂ = c₁ := by
    simp only [swapStore, ← hf, ← hcode]
  have ho : OutAt (swapStore dt d₂) o₂ := outAt_swap ho₂ hag'.1
  exact ((detCfg_of_inv hc) tr d₁ _ o₁ o₂ h₁ (hc₁ ▸ hrun) ho₁ ho).1

/-! ## Runs change only the globals of `W` -/

theorem steps_outside {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hc : Inv A R W c) : Outside W d.store c.store ∧ Inv A R W d := by
  induction h with
  | refl => exact ⟨Agree.refl _ _, hc⟩
  | tail _ hs ih =>
    obtain ⟨hout, hinv⟩ := ih
    obtain ⟨hinv', hS⟩ := inv_step hinv hs
    obtain ⟨e, he, hst, -⟩ := hS.eff
    exact ⟨Agree.trans (hst ▸ Eff.outside he _) hout, hinv'⟩

theorem runs_outside {P : Profile} {c d : Config Nat} {tr : List Call} (h : Runs P c tr d)
    (hc : Inv A R W c) : Outside W d.store c.store := by
  induction h with
  | stop hs => exact (steps_outside hs hc).1
  | call hs hd _ ih =>
    obtain ⟨hout, hinv⟩ := steps_outside hs hc
    exact Agree.trans (ih (inv_resume _ hinv hd)) hout

theorem Eff.app_length (e : Eff) (s : Store Nat) : (e.app s).globals.length = s.globals.length := by
  cases e with
  | keep => rfl
  | set a v => exact List.length_modify ..

theorem steps_length {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hc : Inv A R W c) : d.store.globals.length = c.store.globals.length ∧ Inv A R W d := by
  induction h with
  | refl => exact ⟨rfl, hc⟩
  | tail _ hs ih =>
    obtain ⟨hl, hinv⟩ := ih
    obtain ⟨hinv', hS⟩ := inv_step hinv hs
    obtain ⟨e, -, hst, -⟩ := hS.eff
    exact ⟨by rw [hst, Eff.app_length, hl], hinv'⟩

/-- Runs of subset code keep the number of globals. -/
theorem runs_length {P : Profile} {c d : Config Nat} {tr : List Call} (h : Runs P c tr d)
    (hc : Inv A R W c) : d.store.globals.length = c.store.globals.length := by
  induction h with
  | stop hs => exact (steps_length hs hc).1
  | call hs hd _ ih =>
    obtain ⟨hl, hinv⟩ := steps_length hs hc
    exact (ih (inv_resume _ hinv hd)).trans hl

/-! ## Functions and modules -/

theorem invoke_frame (s : Store Nat) (a : Nat) (vs : List Val) : (invoke s a vs).frame = {} := rfl

theorem invoke_code_eq {s t : Store Nat} (h : t.funcs = s.funcs) (a : Nat) (vs : List Val) :
    (invoke t a vs).code = (invoke s a vs).code := by
  simp only [invoke, h]

/-- **Determinism of subset functions**, at every profile. -/
theorem detFn_of_good {P : Profile} {s : Store Nat} {a : Nat} (hg : GoodFuns A R W s.funcs)
    (ha : A a = true) : DetFn P s a :=
  fun vs _ => detCfg_of_inv (inv_invoke vs hg ha)

/-- **Statelessness of subset functions** over the stores agreeing with `s₀` on the functions
and the globals of `R`, at every profile. -/
theorem statelessFn_of_good {P : Profile} {s₀ : Store Nat} {a : Nat}
    (hg : GoodFuns A R W s₀.funcs) (ha : A a = true) :
    StatelessFn P (fun s => Agree R s s₀) a := by
  intro s₁ s₂ vs h₁ h₂ _ _
  have hag : Agree R s₁ s₂ := Agree.trans h₁ (Agree.symm h₂)
  exact obsAgree_of_agree (inv_invoke vs (h₁.1 ▸ hg) ha) hag rfl (invoke_code_eq hag.1 a vs)

/-- The call states of a module whose entry functions are subset functions writing only the
globals of `W` differ from the initial store only at these globals. -/
theorem callReach_outside {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hg : GoodFuns A R W s₀.funcs) (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true)
    (hs : CallReach P Entry s₀ s) : Outside W s s₀ := by
  induction hs with
  | init => exact Agree.refl _ _
  | @call s a vs tr d r hs ha hok hr _ ih =>
    obtain ⟨fi, -, -, hfi, -, -⟩ := hok
    have hf : s.funcs = s₀.funcs := ih.1
    have hA : A a = true := hE a fi ha (hf ▸ hfi)
    exact Agree.trans (runs_outside hr (inv_invoke vs (hf ▸ hg) hA)) ih

/-- The call states of a module whose entries are subset functions have the globals of the
initial store. -/
theorem callReach_length {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hg : GoodFuns A R W s₀.funcs) (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true)
    (hs : CallReach P Entry s₀ s) : s.globals.length = s₀.globals.length := by
  induction hs with
  | init => rfl
  | @call s a vs tr d r hs ha hok hr _ ih =>
    obtain ⟨fi, -, -, hfi, -, -⟩ := hok
    have hf : s.funcs = s₀.funcs := CallReach.funcs_eq hs
    have hA : A a = true := hE a fi ha (hf ▸ hfi)
    exact (runs_length hr (inv_invoke vs (hf ▸ hg) hA)).trans ih

/-- **A subset function is stateless over the call states of a module** whose entries are subset
functions (`hm`, writing the globals of `W`), when the globals it reads are not in `W`. -/
theorem statelessFn_callReach {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat} {a : Nat}
    {Am Rm : Nat → Bool} (hm : GoodFuns Am Rm W s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → Am a = true)
    {W' : Nat → Bool} (hf : GoodFuns A R W' s₀.funcs) (ha : A a = true)
    (hRW : ∀ g, R g = true → W g = false) : StatelessFn P (CallReach P Entry s₀) a :=
  StatelessFn.anti (fun _ hs => Agree.anti (callReach_outside hm hE hs) fun g hg => by simp [hRW g hg])
    (statelessFn_of_good hf ha)

/-- **A subset function reading no global is stateless over the call states of any module.** -/
theorem statelessFn_callReach_funcs {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat} {a : Nat}
    (hf : GoodFuns A (fun _ => false) W s₀.funcs) (ha : A a = true) :
    StatelessFn P (CallReach P Entry s₀) a :=
  StatelessFn.anti (fun _ hs => ⟨CallReach.funcs_eq hs, fun _ h => absurd h (by simp)⟩)
    (statelessFn_of_good hf ha)

/-- **A module whose entries are subset functions without global writes is stateless.** -/
theorem statelessModule_of_good {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A R (fun _ => false) s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true) :
    StatelessModule P Entry s₀ := by
  intro a ha s₁ s₂ vs h₁ h₂ hok₁ hok₂
  have hA : A a = true := by
    obtain ⟨fi, -, -, hfi, -, -⟩ := hok₁
    exact hE a fi ha (CallReach.funcs_eq h₁ ▸ hfi)
  exact statelessFn_callReach hm hE hm hA (fun _ _ => rfl) s₁ s₂ vs h₁ h₂ hok₁ hok₂

/-- **A module whose entries are subset functions is deterministic.** -/
theorem detModule_of_good {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A R W s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true) : DetModule P Entry s₀ := by
  intro s hs a ha vs hok
  have hf : s.funcs = s₀.funcs := CallReach.funcs_eq hs
  have hA : A a = true := by
    obtain ⟨fi, -, -, hfi, -, -⟩ := hok
    exact hE a fi ha (hf ▸ hfi)
  exact detFn_of_good (hf ▸ hm) hA vs hok

end Silmaril.Proofs.Wasm.Det.Stateless
