module

public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Det.Game.Instance.Defs
public import Silmaril.Wasm.Game.Linking.Store.Thms

/-!
# Determinism of the linked store from the shared store (step A, store level)

The linked module and the shared world are closed: their stores hold no host function, so a run
has no import call and a non-trapping stop is a result. A call state of the linked store is
related (`StoreRelation.Related`) to a call state of the shared store (`callReach_shared`, by
the store-level reverse simulation `linker_steps_reflect`); two runs of an export invocation in
the linked store are matched by two runs in the related shared store with the same results, and
the linked final stores are determined by the shared ones and their (unchanged) functions
(`linker_target_eq`).

New proofs (no source file).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Link.Store

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- The store holds no host function. -/
def NoHostFn (s : Store Nat) : Prop :=
  ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi → fi.code = .host h → False

theorem NoHostFn.of_funcs {s s₀ : Store Nat} (h : s.funcs = s₀.funcs) (h₀ : NoHostFn s₀) :
    NoHostFn s := fun a fi k hfi hc => h₀ a fi k (h ▸ hfi) hc

theorem NoHostFn.of_wellFormed {I : ScalarInstance} (hI : I.imports = []) {s : Store Nat}
    (hw : I.WellFormed s) : NoHostFn s := by
  intro a fi h hfi hc
  obtain ⟨hlt, -⟩ := hw.host_type a fi h hfi hc
  rw [hI] at hlt
  exact Nat.not_lt_zero _ hlt

theorem NoHostFn.no_decompose {s : Store Nat} (hs : NoHostFn s) {code : List Admin} {E : Ctx}
    {a h : Nat} {args : List Val} (hd : decompose? s code = some (E, a, h, args)) : False := by
  obtain ⟨fi, -, -, -, hfi, hc, -⟩ := decompose?_sound hd
  exact hs a fi h hfi hc

/-- In a store without host functions, runs have no import call. -/
theorem runs_noHost {c d : Config Nat} {tr : List Call} (hc : NoHostFn c.store)
    (h : Runs P c tr d) : tr = [] ∧ Steps P (Det.noHost (H := Nat)) c d := by
  cases h with
  | stop hs => exact ⟨rfl, hs⟩
  | call hs hd _ =>
    have hf := Runs.funcs_eq (Runs.stop (P := P) hs)
    exact ((hc.of_funcs hf).no_decompose hd).elim

/-- In a store without host functions, a non-trapping stop is a result. -/
theorem outAt_noHost {d : Config Nat} {o : Out} (hd : NoHostFn d.store) (h : OutAt d o) :
    ∃ r, o = .ret r ∧ r ≠ .trap ∧ d.code = r.toAdmin := by
  cases h with
  | ret hr hc => exact ⟨_, rfl, hr, hc⟩
  | call hdec => exact (hd.no_decompose hdec).elim

variable (S : Setup)

/-- Call states of the linked store come from related, typed call states of the shared store. -/
theorem callReach_shared (hS : S.Scalar) {E : Nat → Prop} {s' : Store Nat}
    (h : CallReach P E S.sl s') :
    ∃ s, CallReach P E S.sc s ∧ StoreRelation.Related s s' ∧ StoreOk s := by
  induction h with
  | init => exact ⟨S.sc, .init, S.sc_related_sl, hS.shared.storeOk⟩
  | @call s' a vs tr d r hs' ha hok hr hd ih =>
    obtain ⟨s, hs, hrel, hsok⟩ := ih
    have hn : NoHostFn s' :=
      NoHostFn.of_funcs (CallReach.funcs_eq hs') (NoHostFn.of_wellFormed rfl hS.linked)
    obtain ⟨rfl, run⟩ := runs_noHost hn hr
    have hok' := linker_invokeOk_reverse hrel hok
    obtain ⟨e, run', he, hrel'⟩ := linker_steps_reflect hrel hsok hok' run hd
    exact ⟨e.store, .call hs ha hok' (.stop run') he, hrel',
      invoke_steps_storeOk hsok hok' run'⟩

/-- **Step A, store level**: determinism of the shared store gives determinism of the linked
store. -/
theorem linked_detModule_of_shared (hS : S.Scalar)
    (hD : DetModule P (entry S.sharedI) S.sc) : DetModule P (entry S.linkedI) S.sl := by
  intro s' hs' a ha vs hok tr d₁ d₂ o₁ o₂ r₁ r₂ ho₁ ho₂
  obtain ⟨s, hs, hrel, hsok⟩ := callReach_shared S hS hs'
  have hn : NoHostFn s' :=
    NoHostFn.of_funcs (CallReach.funcs_eq hs') (NoHostFn.of_wellFormed rfl hS.linked)
  obtain ⟨rfl, run₁⟩ := runs_noHost hn r₁
  obtain ⟨-, run₂⟩ := runs_noHost hn r₂
  have hf₁ : d₁.store.funcs = s'.funcs := Runs.funcs_eq r₁
  have hf₂ : d₂.store.funcs = s'.funcs := Runs.funcs_eq r₂
  obtain ⟨q₁, rfl, hq₁, hc₁⟩ := outAt_noHost (hn.of_funcs hf₁) ho₁
  obtain ⟨q₂, rfl, hq₂, hc₂⟩ := outAt_noHost (hn.of_funcs hf₂) ho₂
  have hok' := linker_invokeOk_reverse hrel hok
  obtain ⟨e₁, se₁, he₁, hrel₁⟩ := linker_steps_reflect hrel hsok hok' run₁ hc₁
  obtain ⟨e₂, se₂, he₂, hrel₂⟩ := linker_steps_reflect hrel hsok hok' run₂ hc₂
  obtain ⟨ho, hst⟩ := hD s hs a ha vs hok' [] e₁ e₂ _ _ (.stop se₁) (.stop se₂)
    (.ret hq₁ he₁) (.ret hq₂ he₂)
  exact ⟨ho, linker_target_eq hrel₁ hrel₂ hst (hf₁.trans hf₂.symm)⟩

/-- **Step A, store level, statelessness**: statelessness of the shared store gives
statelessness of the linked store. -/
theorem linked_statelessModule_of_shared (hS : S.Scalar)
    (hD : StatelessModule P (entry S.sharedI) S.sc) :
    StatelessModule P (entry S.linkedI) S.sl := by
  intro a ha s₁' s₂' vs hs₁' hs₂' hok₁ hok₂ tr d₁ d₂ o₁ o₂ r₁ r₂ ho₁ ho₂
  obtain ⟨s₁, hs₁, hrel₁, hsok₁⟩ := callReach_shared S hS hs₁'
  obtain ⟨s₂, hs₂, hrel₂, hsok₂⟩ := callReach_shared S hS hs₂'
  have hn₁ : NoHostFn s₁' :=
    NoHostFn.of_funcs (CallReach.funcs_eq hs₁') (NoHostFn.of_wellFormed rfl hS.linked)
  have hn₂ : NoHostFn s₂' :=
    NoHostFn.of_funcs (CallReach.funcs_eq hs₂') (NoHostFn.of_wellFormed rfl hS.linked)
  obtain ⟨rfl, run₁⟩ := runs_noHost hn₁ r₁
  obtain ⟨-, run₂⟩ := runs_noHost hn₂ r₂
  obtain ⟨q₁, rfl, hq₁, hc₁⟩ := outAt_noHost (hn₁.of_funcs (Runs.funcs_eq r₁)) ho₁
  obtain ⟨q₂, rfl, hq₂, hc₂⟩ := outAt_noHost (hn₂.of_funcs (Runs.funcs_eq r₂)) ho₂
  have hok₁' := linker_invokeOk_reverse hrel₁ hok₁
  have hok₂' := linker_invokeOk_reverse hrel₂ hok₂
  obtain ⟨e₁, se₁, he₁, -⟩ := linker_steps_reflect hrel₁ hsok₁ hok₁' run₁ hc₁
  obtain ⟨e₂, se₂, he₂, -⟩ := linker_steps_reflect hrel₂ hsok₂ hok₂' run₂ hc₂
  exact hD a ha s₁ s₂ vs hs₁ hs₂ hok₁' hok₂' [] e₁ e₂ _ _ (.stop se₁) (.stop se₂)
    (.ret hq₁ he₁) (.ret hq₂ he₂)

end Silmaril.Proofs.Wasm.Det.Link.Store
