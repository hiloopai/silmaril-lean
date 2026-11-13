module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Grows
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Store
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# The Core 3.0 engine at an arbitrary profile is lawful

`core3P P` (`Silmaril.Wasm.Component.Reference.core3P`) is silmaril-lean's `core3` engine with the
internal step `InternalP P` (a Core step under profile `P` with no host) and the status
`flatStatus (statusP P)`. The laws of `CoreEngine.Lawful` that mention neither are those of
`core3` (`core3_lawful`). The others are proved here for every profile:

* `internalP_grows`: an internal step grows the store (`Grows`, the untyped store extension of
  the component copy), from `Step.grows`, which holds for every profile;
* `statusP_callout_prefix`: a callout status of `statusP P` persists in every store with more
  functions, for any profile on either side (the proof of `statusC_callout_prefix`, with
  `statusP` for `statusC`);
* `Grows.extendsP`: growth is store extension of `core3P P`;
* `statusP_no_step_*`: a thread whose status is `returned`, `callout` or `stuck` takes no
  internal step (`Step.not_quiet`, `Step.noRedex`, and the definition of `stuck`);
* `statusP_allocHost_callout`: invoking an allocated host function with matching arity is a
  callout (from silmaril-lean's `allocHost_callout`, whose status agrees with `statusP` on
  callouts).

Source: the structure follows the component copy of the old silmaril engine laws
(`Silmaril/Raw/Wasm/Component/Engine/Core3/{Grows,Extends,Store,Instance}.lean`, copied from
`an earlier development`), with the computable status
`statusC (stepI o)` replaced by the relational `statusP P`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Core3G

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store Config Step Val)
open Silmaril.Wasm.SingleThreaded (Thread Status CallResult decompose? Ctx GrowOracle Quiet
  quiet_vals quiet_trap
  quiet_throwing decompose?_none_of_noRedex allocHost allocHost_callout neverFail ofFlat status)
open Silmaril.Wasm.Component.Engine.Core3 (Grows Step.grows decompose?_prefix
  Thread.config_code_prefix Thread.loaded_of_decompose? mapM_toFlat?_map_ofFlat)
open Silmaril.Wasm.Numerics (Profile)

local notation "flatStatus" => Silmaril.Wasm.Component.Reference.flatStatus
local notation "core3P" => Silmaril.Wasm.Component.Reference.core3P
local notation "FlatValue" => Silmaril.Wasm.Component.Engine.FlatValue
local notation "V1FuncType" => Silmaril.Wasm.V1.FuncType

variable {H : Type} {P : Profile}

/-! ## Internal steps grow the store -/

theorem internalP_grows {s s' : Store H} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
    Grows s s' := by
  obtain ⟨f', code', -, h⟩ := h
  simpa [Silmaril.Wasm.SingleThreaded.Thread.config_store] using Step.grows h

/-! ## Callouts persist -/

theorem decompose?_of_statusP_callout {P' : Profile} {s : Store H} {t : Thread} {hc : H}
    {args : List Val} (h : statusP P' s t = .callout hc args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, hc, args) := by
  unfold statusP at h
  dsimp only at h
  split_ifs at h
  all_goals
    revert h
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    all_goals simp

/-- **A callout status persists** in every store with more functions, for any profiles. -/
theorem statusP_callout_prefix {P' : Profile} {s s' : Store H} (hg : s.funcs <+: s'.funcs)
    {t : Thread} {hc : H} {args : List Val} (h : statusP P s t = .callout hc args) :
    statusP P' s' t = .callout hc args := by
  obtain ⟨E, a, hd⟩ := decompose?_of_statusP_callout h
  have hcode := Thread.config_code_prefix hg (Thread.loaded_of_decompose? hd)
  have hd' := decompose?_prefix hg hd
  unfold statusP at h ⊢
  dsimp only at h ⊢
  rw [hcode, hd']
  rw [hd] at h
  dsimp only at h ⊢
  exact h

/-! ## The flat status -/

theorem flatStatus_eq_callout {st : Status H} {hc : H} {args : List FlatValue}
    (h : flatStatus st = .callout hc args) : ∃ hc' args', st = .callout hc' args' := by
  rcases st with _ | (vs | _) | ⟨hc', args'⟩ | _
  · cases h
  · simp only [Silmaril.Wasm.Component.Reference.flatStatus] at h
    split at h <;> cases h
  · cases h
  · exact ⟨hc', args', rfl⟩
  · cases h

theorem flatStatus_eq_returned {st : Status H} {r : Silmaril.Wasm.Component.Engine.CallResult}
    (h : flatStatus st = .returned r) :
    (∃ vs, st = .returned (.values vs)) ∨ st = .returned .trap := by
  rcases st with _ | (vs | _) | ⟨hc', args'⟩ | _
  · cases h
  · exact Or.inl ⟨vs, rfl⟩
  · exact Or.inr rfl
  · simp only [Silmaril.Wasm.Component.Reference.flatStatus] at h
    split at h <;> cases h
  · cases h

theorem flatStatus_eq_stuck {st : Status H} (h : flatStatus st = .stuck) :
    st = .stuck ∨ (∃ vs, st = .returned (.values vs)) ∨ ∃ hc args, st = .callout hc args := by
  rcases st with _ | (vs | _) | ⟨hc', args'⟩ | _
  · cases h
  · exact Or.inr (Or.inl ⟨vs, rfl⟩)
  · cases h
  · exact Or.inr (Or.inr ⟨hc', args', rfl⟩)
  · exact Or.inl rfl

/-- **Growth is store extension of `core3P P`.** -/
theorem Grows.extendsP {s s' : Store H} (hg : Grows s s') : (core3P P).Extends s s' where
  funcType _ _ h := hg.funcType h
  memAddrType _ _ h := hg.memAddrType h
  memSize _ _ h := hg.memSize h
  tableAddrType _ _ h := hg.tableAddrType h
  callout t hc args h := by
    change flatStatus (statusP P s' t) = .callout hc args
    change flatStatus (statusP P s t) = .callout hc args at h
    obtain ⟨hc', args', e⟩ := flatStatus_eq_callout h
    rw [statusP_callout_prefix (P' := P) hg.funcs e, ← e]
    exact h

/-! ## Parked threads take no internal step -/

theorem no_internal_of_quiet {s : Store H} {t : Thread} (hq : Quiet (t.config s).code)
    (y : Store H × Thread) : ¬ InternalP P (s, t) y := by
  rintro ⟨f', code', -, hstep⟩
  exact Silmaril.Wasm.SingleThreaded.Step.not_quiet hstep hq

theorem no_internal_of_decompose {s : Store H} {t : Thread} {x : Ctx × Nat × H × List Val}
    (hd : decompose? s (t.config s).code = some x) (y : Store H × Thread) :
    ¬ InternalP P (s, t) y := by
  rintro ⟨f', code', -, hstep⟩
  have hn := decompose?_none_of_noRedex (Silmaril.Wasm.SingleThreaded.Step.noRedex hstep)
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hn
  rw [hd] at hn
  cases hn

theorem statusP_returned_quiet {s : Store H} {t : Thread} {r : CallResult}
    (h : statusP P s t = .returned r) : Quiet (t.config s).code := by
  unfold statusP at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · obtain ⟨vs, hv⟩ := h1
    rw [hv]
    exact quiet_vals vs
  · rw [h2]
    exact quiet_trap
  · obtain ⟨a, ha⟩ := h3
    rw [ha]
    exact quiet_throwing a
  all_goals
    revert h
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    all_goals simp

theorem statusP_returned_no_step {s : Store H} {t : Thread} {r : CallResult}
    (h : statusP P s t = .returned r) (y : Store H × Thread) : ¬ InternalP P (s, t) y :=
  no_internal_of_quiet (statusP_returned_quiet h) y

theorem statusP_callout_no_step {s : Store H} {t : Thread} {hc : H} {args : List Val}
    (h : statusP P s t = .callout hc args) (y : Store H × Thread) : ¬ InternalP P (s, t) y := by
  obtain ⟨E, a, hd⟩ := decompose?_of_statusP_callout h
  exact no_internal_of_decompose hd y

theorem statusP_stuck_no_step {s : Store H} {t : Thread} (h : statusP P s t = .stuck)
    (y : Store H × Thread) : ¬ InternalP P (s, t) y := by
  intro hy
  unfold statusP at h
  dsimp only at h
  split_ifs at h
  all_goals
    revert h
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    all_goals simp_all

/-- The no-step law for every parked flat status. -/
theorem flat_no_step {s : Store H} {t : Thread} {y : Store H × Thread}
    (h : flatStatus (statusP P s t) = .stuck ∨
      (∃ r, flatStatus (statusP P s t) = .returned r) ∨
      ∃ hc args, flatStatus (statusP P s t) = .callout hc args) :
    ¬ InternalP P (s, t) y := by
  rcases h with h | ⟨r, h⟩ | ⟨hc, args, h⟩
  · rcases flatStatus_eq_stuck h with e | ⟨vs, e⟩ | ⟨hc, args, e⟩
    · exact statusP_stuck_no_step e y
    · exact statusP_returned_no_step e y
    · exact statusP_callout_no_step e y
  · rcases flatStatus_eq_returned h with ⟨vs, e⟩ | e
    · exact statusP_returned_no_step e y
    · exact statusP_returned_no_step e y
  · obtain ⟨hc', args', e⟩ := flatStatus_eq_callout h
    exact statusP_callout_no_step e y

/-! ## Allocated host functions are callouts -/

/-- A callout of silmaril-lean's relational status is a callout of `statusP P`, for every
profile: both classify the code by the same tests up to the last branch. -/
theorem statusP_callout_of_status {o : GrowOracle} {s : Store H} {t : Thread} {hc : H}
    {args : List Val} (hs : status o s t = .callout hc args) :
    statusP P s t = .callout hc args := by
  unfold status at hs
  unfold statusP
  dsimp only at hs ⊢
  split_ifs at hs ⊢
  all_goals
    revert hs
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    all_goals simp

theorem statusP_allocHost_callout {s s' : Store H} {ft : V1FuncType} {h : H} {a : Nat}
    {args : List FlatValue} (e : allocHost s ft h = (s', a))
    (hl : args.length = ft.params.length) :
    flatStatus (statusP P s' (Thread.invokeFlat a args)) = .callout h args := by
  have hc := allocHost_callout (o := neverFail) s ft h (args.map ofFlat)
    (by rw [List.length_map, hl])
  rw [e] at hc
  dsimp only at hc
  unfold Thread.invokeFlat
  rw [statusP_callout_of_status hc]
  simp only [Silmaril.Wasm.Component.Reference.flatStatus, mapM_toFlat?_map_ofFlat]

end Silmaril.Proofs.Wasm.Component.Core3G
