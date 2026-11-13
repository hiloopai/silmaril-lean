module

public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# the stripped host `stripHostAt host s₀`

* `stripHostAt_finite`, `stripHostAt_ok`: finite and `HostOk` whenever `host` is. No hypothesis on
  export names is needed: at `stripStore s₀` the host answers stripped outcomes of a call at the
  typed store `s₀`, and Core typing survives removing exports (`Round7.storeOk_strip`,
  `valOk_withFuncs`, `extend_strip`).
* `hostRelAt_strip`, `hostRelAt_unstrip`: `host` at `s₀` and `stripHostAt host s₀` at
  `stripStore s₀` match each other up to export lists, in both directions.
* `hostStrippedAt_strip`: at `stripStore s₀` the stripped host returns only export-free stores.
* `stripHostAt_of_blind`: for an export-blind host, `stripHostAt host s₀ = host`.
* `hostRelAt_of_blind`: an export-blind host is related to itself at any two stores with the same
  stripped form, which is what `Round7.exRel_step` used.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round7

variable {H : Type}

/-! ## Stripping, idempotently -/

theorem stripOutcome_stripOutcome (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result) :
    stripOutcome (stripOutcome o) = stripOutcome o := by
  cases o with
  | returned s r => simp only [stripOutcome, stripStore_stripStore]
  | diverged => rfl

/-- A store is the stripped store with its own function instances put back. -/
theorem stripStore_withOwn (s : Store H) : { stripStore s with funcs := s.funcs } = s := by
  cases s
  rfl

/-- Values typed at the stripped store are typed at the store. -/
theorem valOk_of_strip {s : Store H} {v : Val} {t : CValType} (h : ValOk (stripStore s) v t) :
    ValOk s v t := by
  have hF : s.funcs.map stripFI = (stripStore s).funcs.map stripFI := (funcs_stripStore s).symm
  have := valOk_withFuncs hF h
  rwa [stripStore_withOwn] at this

/-- Values typed at a store are typed at the stripped store. -/
theorem valOk_strip {s : Store H} {v : Val} {t : CValType} (h : ValOk s v t) :
    ValOk (stripStore s) v t :=
  valOk_withFuncs (funcs_stripStore s) h

/-- Store extension survives stripping both stores. -/
theorem extend_strip {s s' : Store H} (h : Extend s s') : Extend (stripStore s) (stripStore s') := by
  refine ⟨h.tags, h.globals, h.mems, h.tables, ⟨?_, ?_⟩, h.datas, h.elems, h.structs, h.arrays,
    h.exns⟩
  · simp only [stripStore_eq, List.length_map]
    exact h.funcs.1
  · intro i x hx
    simp only [stripStore_eq, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, ht, hm, hw, hh⟩ := h.funcs.2 i a ha
    refine ⟨stripFI b, ?_, ht, ?_, hw, hh⟩
    · simp only [stripStore_eq, List.getElem?_map, hb, Option.map_some]
    · simp only [stripFI, hm]

/-- A typed result stays typed at the stripped store. -/
theorem resultTyped_strip {s : Store H} {r : Result} {ts : List CValType}
    (h : ResultTyped s r ts) : ResultTyped (stripStore s) r ts := by
  cases r with
  | values vs => exact h.imp fun _ _ hv => valOk_strip hv
  | throw a => exact h
  | trap => trivial

/-- A function instance of the stripped store is the stripped form of one of the store. -/
theorem mem_stripStore {s : Store H} {fi : FuncInst H} (h : fi ∈ (stripStore s).funcs) :
    ∃ fi₀ ∈ s.funcs, stripFI fi₀ = fi :=
  List.mem_map.mp h

/-! ## The stripped host -/

theorem stripHostAt_at {host : HostSemantics H} {s₀ : Store H} (hs₀ : StoreOk s₀) {h : H}
    {vs : List Val} {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result} :
    stripHostAt host s₀ h (stripStore s₀) vs o ↔
      ∃ o₀, host h s₀ vs o₀ ∧ o = stripOutcome o₀ := by
  constructor
  · rintro (⟨-, -, ho⟩ | ⟨hn, -⟩)
    · exact ho
    · exact absurd ⟨rfl, hs₀⟩ hn
  · exact fun ho => .inl ⟨rfl, hs₀, ho⟩

theorem stripHostAt_off {host : HostSemantics H} {s₀ s : Store H}
    (hn : ¬ (s = stripStore s₀ ∧ StoreOk s₀)) {h : H} {vs : List Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result} :
    stripHostAt host s₀ h s vs o ↔ host h s vs o := by
  constructor
  · rintro (⟨hs, ho, -⟩ | ⟨-, ho⟩)
    · exact absurd ⟨hs, ho⟩ hn
    · exact ho
  · exact fun ho => .inr ⟨hn, ho⟩

/-- **The stripped host is finite.** -/
theorem stripHostAt_finite {host : HostSemantics H} (hf : HostFinite host) (s₀ : Store H) :
    HostFinite (stripHostAt host s₀) := by
  intro h s vs
  by_cases hc : s = stripStore s₀ ∧ StoreOk s₀
  · obtain ⟨rfl, hs₀⟩ := hc
    obtain ⟨os, hos⟩ := hf h s₀ vs
    refine ⟨os.map stripOutcome, fun o => ?_⟩
    rw [stripHostAt_at hs₀, List.mem_map]
    exact ⟨fun ⟨o₀, ho, he⟩ => ⟨o₀, (hos o₀).mp ho, he.symm⟩,
      fun ⟨o₀, ho, he⟩ => ⟨o₀, (hos o₀).mpr ho, he.symm⟩⟩
  · obtain ⟨os, hos⟩ := hf h s vs
    exact ⟨os, fun o => (stripHostAt_off hc).trans (hos o)⟩

/-- One outcome of `host` at a typed `s₀`, stripped, is well-behaved at `stripStore s₀`. -/
theorem stripOutcome_ok {s₀ : Store H} {rs : List CValType}
    (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result)
    (ho : match o with
      | .diverged => True
      | .returned s' r => StoreOk s' ∧ Extend s₀ s' ∧ ResultTyped s' r rs) :
    match stripOutcome o with
      | .diverged => True
      | .returned s' r => StoreOk s' ∧ Extend (stripStore s₀) s' ∧ ResultTyped s' r rs := by
  cases o with
  | diverged => trivial
  | returned s' r =>
    obtain ⟨hs', he, hr⟩ := ho
    exact ⟨storeOk_strip hs', extend_strip he, resultTyped_strip hr⟩

/-- **The stripped host is `HostOk`** whenever `host` is. -/
theorem stripHostAt_ok {host : HostSemantics H} (hh : HostOk host) (s₀ : Store H) :
    HostOk (stripHostAt host s₀) := by
  intro s fi h vs ps rs hs hfi hcode hexp hvs
  by_cases hc : s = stripStore s₀ ∧ StoreOk s₀
  · obtain ⟨rfl, hs₀⟩ := hc
    obtain ⟨fi₀, hfi₀, rfl⟩ := mem_stripStore hfi
    obtain ⟨⟨out, hout⟩, hall⟩ :=
      hh s₀ fi₀ h vs ps rs hs₀ hfi₀ hcode hexp (hvs.imp fun _ _ hv => valOk_of_strip hv)
    refine ⟨⟨stripOutcome out, (stripHostAt_at hs₀).mpr ⟨out, hout, rfl⟩⟩, fun o ho => ?_⟩
    obtain ⟨o₀, ho₀, rfl⟩ := (stripHostAt_at hs₀).mp ho
    exact stripOutcome_ok o₀ (hall o₀ ho₀)
  · obtain ⟨⟨out, hout⟩, hall⟩ := hh s fi h vs ps rs hs hfi hcode hexp hvs
    exact ⟨⟨out, (stripHostAt_off hc).mpr hout⟩, fun o ho => hall o ((stripHostAt_off hc).mp ho)⟩

/-- **`host` at `s₀` is matched by the stripped host at `stripStore s₀`.** -/
theorem hostRelAt_strip (host : HostSemantics H) {s₀ : Store H} (hs₀ : StoreOk s₀) :
    HostRelAt host (stripHostAt host s₀) s₀ (stripStore s₀) := fun _ _ o ho =>
  ⟨stripOutcome o, (stripHostAt_at hs₀).mpr ⟨o, ho, rfl⟩, (stripOutcome_stripOutcome o).symm⟩

/-- **The stripped host at `stripStore s₀` is matched by `host` at `s₀`.** -/
theorem hostRelAt_unstrip (host : HostSemantics H) {s₀ : Store H} (hs₀ : StoreOk s₀) :
    HostRelAt (stripHostAt host s₀) host (stripStore s₀) s₀ := fun _ _ _ ho => by
  obtain ⟨o₀, ho₀, rfl⟩ := (stripHostAt_at hs₀).mp ho
  exact ⟨o₀, ho₀, stripOutcome_stripOutcome o₀⟩

/-- **At `stripStore s₀` the stripped host returns only export-free stores.** -/
theorem hostStrippedAt_strip (host : HostSemantics H) {s₀ : Store H} (hs₀ : StoreOk s₀) :
    HostStrippedAt (stripHostAt host s₀) (stripStore s₀) := fun _ _ s' r ho => by
  obtain ⟨o₀, -, he⟩ := (stripHostAt_at hs₀).mp ho
  cases o₀ with
  | diverged => exact absurd he (by simp [stripOutcome])
  | returned s₁ r₁ =>
    simp only [stripOutcome, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at he
    rw [he.1, stripStore_stripStore]

/-- **For an export-blind host the stripped host is the host.** -/
theorem stripHostAt_of_blind {host : HostSemantics H} (hb : HostExportBlind host) (s₀ : Store H) :
    stripHostAt host s₀ = host := by
  funext h s vs o
  apply propext
  by_cases hc : s = stripStore s₀ ∧ StoreOk s₀
  · obtain ⟨rfl, hs₀⟩ := hc
    rw [stripHostAt_at hs₀]
    constructor
    · rintro ⟨o₀, ho₀, rfl⟩
      exact hb.1 _ _ _ _ ho₀
    · intro ho
      obtain ⟨o₀, ho₀, he⟩ := hb.2 _ _ _ _ ho
      exact ⟨o₀, ho₀, he⟩
  · exact stripHostAt_off hc

/-- **An export-blind host is related to itself** at two stores with the same stripped form. -/
theorem hostRelAt_of_blind {host : HostSemantics H} (hb : HostExportBlind host) {s₁ s₂ : Store H}
    (hs : stripStore s₁ = stripStore s₂) : HostRelAt host host s₁ s₂ := fun _ _ o ho => by
  have h₁ := hb.1 _ _ _ _ ho
  rw [hs] at h₁
  obtain ⟨o', ho', he⟩ := hb.2 _ _ _ _ h₁
  exact ⟨o', ho', he⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
