module

public import Silmaril.Wasm.Link.PreparedObservation
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.NoRedex
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Linked behaviour sets, divergence included

Reuses the existing linker simulation rather than introducing a second one.

Helpers for `link_sound` (`Binaryen/Merge.lean`): the terminal agreement of
(`PreparedObservation`) lifted to whole behaviour sets of the deterministic
host-free profile.

* `no_diverges_of_nf`: a configuration that reaches a normal form has no
  infinite run. Peaks join in at most one step (`Det.DStep.join'`) and two
  different steps both shrink the code (`Det.DStep.shrink`), so the pair
  (distance to the normal form, code size) decreases lexicographically along any
  run.
* `diverges_or_nf`: every configuration diverges or reaches a normal form.
* `diverges_forward`: the lockstep simulation `WholeSimulation.step` maps an
  infinite source run to an infinite linked run.
* `stuck_transfer`: a typed source configuration that is neither terminal nor
  able to step is blocked on a host call (`decompose?`, via progress under the
  total diverging host); the linked configuration related to it is blocked on the
  same host function, hence does not step and is not terminal.
-/

namespace Silmaril.Wasm.Binaryen.LinkBehaviours

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Link.GC.AdminRelation Silmaril.Wasm.Link.GC.Simulation

variable {H : Type}

/-! ## Normal forms exclude divergence -/

theorem no_diverges_aux {o : GrowOracle} {y : Config H}
    (hy : ∀ z, ¬ Step (profile o) noHost y z) :
    ∀ (k n : Nat) (x : Config H), sizeOf x.code = n →
      NSteps (Step (profile o) noHost) k x y → ¬ InfiniteTrace (Step (profile o) noHost) x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro x hsz hk hinf
  obtain ⟨x1, hx1, hinf1⟩ := hinf.unfold
  cases hk with
  | refl => exact hy _ hx1
  | @head _ y1 _ k' hxy1 hrest =>
    by_cases heq : x1 = y1
    · subst heq
      exact ihk k' (by omega) _ _ rfl hrest hinf1
    · obtain ⟨s, f, code⟩ := x
      rcases Det.DStep.shrink (o := o) _ s f code x1 y1 rfl hx1 hxy1 with h | ⟨-, -, hlt, -⟩
      · exact heq h
      · obtain ⟨m, hm, hm'⟩ := NSteps.of_step_join (fun ha hb => Det.DStep.join' ha hb) hy
          (NSteps.head hxy1 hrest) hx1
        rcases Nat.lt_or_ge m (k' + 1) with hlt' | hge
        · exact ihk m hlt' _ _ rfl hm' hinf1
        · have hmk : m = k' + 1 := by omega
          subst hmk
          exact ihn _ (by rw [← hsz]; exact hlt) x1 rfl hm' hinf1

/-- **A configuration reaching a normal form does not diverge.** -/
theorem no_diverges_of_nf {o : GrowOracle} {x y : Config H}
    (hxy : Steps (profile o) noHost x y) (hy : ∀ z, ¬ Step (profile o) noHost y z) :
    ¬ Diverges (profile o) noHost x := by
  obtain ⟨k, hk⟩ := NSteps.of_rtg hxy
  exact no_diverges_aux hy k _ x rfl hk

/-- Every configuration diverges or reaches a normal form. -/
theorem diverges_or_nf {P : Profile} {host : HostSemantics H} (x : Config H) :
    Diverges P host x ∨ ∃ y, Steps P host x y ∧ ∀ z, ¬ Step P host y z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnd, hall⟩ := hcon
  exact hnd (InfiniteTrace.coinduct (fun y => Steps P host x y)
    (fun y hy => let ⟨z, hz⟩ := hall y hy; ⟨z, hz, hy.tail hz⟩) .refl)

/-! ## Forward divergence -/

/-- **An infinite typed source run has an infinite linked run.** -/
theorem diverges_forward {P : Profile} {mode : Mode} {cs ct : Config H} {rs : List CValType}
    (typed : ConfigOk cs rs) (hm : Matching mode cs ct) (hd : Diverges P noHost cs) :
    Diverges P noHost ct := by
  refine InfiniteTrace.coinduct
    (fun t => ∃ s, ConfigOk s rs ∧ Matching mode s t ∧ InfiniteTrace (Step P noHost) s) ?_
    ⟨cs, typed, hm, hd⟩
  rintro t ⟨s, hs, hst, hinf⟩
  obtain ⟨s1, hs1, hinf1⟩ := hinf.unfold
  obtain ⟨t1, ht1, hm1⟩ := WholeSimulation.step hs1 hst (AdminScope.config_scope hs)
    (function_scopes (ConfigOk.storeOk hs))
  exact ⟨t1, ht1, s1, WholeSimulation.hostfree_typed hs (.single hs1), hm1, hinf1⟩

/-! ## Host-call blocking -/

/-- A host-call redex in any context is found by `decompose?`. -/
theorem decompose?_fill_isSome {s : Store H} {args : List Val} {a : Nat} {c : Admin} {h : H}
    (hc : c.isCallRef = true) (ha : hostArity? s a = some (h, args.length)) :
    ∀ E : Ctx, (decompose? s (E.fill (vals args ++ [.ref (.func a), c]))).isSome = true := by
  intro E
  induction E with
  | top pre rest =>
    have hfill : Ctx.fill (.top pre rest) (vals args ++ [.ref (.func a), c]) =
        vals ((pre ++ args) ++ [.ref (.func a)]) ++ c :: rest := by
      simp [Ctx.fill, Val.toAdmin]
    rw [hfill, decompose?_top hc ha (by simp)]
    rfl
  | label pre n cont E rest ih =>
    have hsv : splitVals (Ctx.fill (.label pre n cont E rest) (vals args ++ [.ref (.func a), c])) =
        (pre, .label n cont (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsv, decompHead_label]
    simpa using ih
  | handler pre n cs E rest ih =>
    have hsv : splitVals (Ctx.fill (.handler pre n cs E rest) (vals args ++ [.ref (.func a), c])) =
        (pre, .handler n cs (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsv, decompHead_handler]
    simpa using ih
  | frame pre n f E rest ih =>
    have hsv : splitVals (Ctx.fill (.frame pre n f E rest) (vals args ++ [.ref (.func a), c])) =
        (pre, .frame n f (E.fill (vals args ++ [.ref (.func a), c])) :: rest) := by
      simp only [Ctx.fill, List.append_assoc, List.singleton_append]
      exact splitVals_vals_cons rfl rest
    rw [decompose?_of_split hsv, decompHead_frame]
    simpa using ih

/-- A code with a host-call redex does not take a host-free step. -/
theorem no_step_of_decompose {P : Profile} {c : Config H} (h : decompose? c.store c.code ≠ none) :
    ∀ z, ¬ Step P noHost c z :=
  fun _ hz => h (decompose?_none_of_noRedex (Step.noRedex hz))

/-- A terminal code has no host-call redex. -/
theorem decompose?_result {s : Store H} (r : Result) : decompose? s r.toAdmin = none := by
  cases r with
  | values vs => exact decompose?_vals_nil
  | trap =>
    exact decompose?_vals_cons_none (vs := []) (d := .trap) (r := []) rfl
      (fun _ _ => decompHead_trap)
  | throw a =>
    exact decompose?_vals_cons_none (vs := [.ref (.exn a)]) (d := .plain .throwRef) (r := []) rfl
      (fun _ _ => decompHead_plain rfl)

/-- Relocation keeps `call_ref`. -/
theorem instruction?_isCallRef {r : Relocation} {i j : Instr} (h : instruction? r i = some j)
    (hc : (Admin.plain i).IsCallRef) : (Admin.plain j).IsCallRef := by
  cases i <;> try exact (hc : False).elim
  rename_i t
  simp only [instruction?] at h
  cases ho : shiftIdx? r.types t with
  | none => simp [ho] at h
  | some x =>
    simp [ho] at h
    subst h
    trivial

/-- The relation keeps a lone `call_ref`. -/
theorem control_callRef {mode : Mode} {src tgt : ModuleInst} {c : Admin} {Y : List Admin}
    (hc : c.IsCallRef) (h : Control mode src tgt [c] Y) :
    ∃ c', c'.isCallRef = true ∧ Y = [c'] := by
  cases h with
  | plain hr rest =>
    rw [rest.nil_left]
    refine ⟨_, ?_, rfl⟩
    cases mode with
    | same =>
      change _ = _ at hr
      subst hr
      exact Admin.isCallRef_of_IsCallRef hc
    | relocated r => exact Admin.isCallRef_of_IsCallRef (instruction?_isCallRef hr hc)
  | @val _ _ _ _ _ v rest =>
    have h1 := Admin.val?_of_IsCallRef hc
    rw [Admin.val?_toAdmin] at h1
    cases h1
  | callRefType rest =>
    rw [rest.nil_left]
    exact ⟨_, rfl, rfl⟩
  | ref rest => exact (hc : False).elim
  | returnCallRefType rest => exact (hc : False).elim
  | throwRef rest => exact (hc : False).elim
  | label _ _ _ => exact (hc : False).elim
  | handler _ _ => exact (hc : False).elim
  | frame _ _ _ => exact (hc : False).elim
  | trap _ => exact (hc : False).elim

/-- The relation keeps the shape of a context. -/
theorem control_fill : ∀ (E : Ctx) {mode : Mode} {src tgt : ModuleInst} {X ys : List Admin},
    Control mode src tgt (E.fill X) ys →
    ∃ (E' : Ctx) (mode' : Mode) (src' tgt' : ModuleInst) (Y : List Admin),
      ys = E'.fill Y ∧ Control mode' src' tgt' X Y := by
  intro E
  induction E with
  | top pre rest =>
    intro mode src tgt X ys h
    simp only [Ctx.fill, List.append_assoc] at h
    obtain ⟨r1, rfl, h1⟩ := h.values_prefix
    obtain ⟨Y, R, rfl, hY, -⟩ := h1.split
    exact ⟨.top pre R, mode, src, tgt, Y, by simp [Ctx.fill], hY⟩
  | label pre n cont E rest ih =>
    intro mode src tgt X ys h
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨r1, rfl, h1⟩ := h.values_prefix
    obtain ⟨cont', body', rest', rfl, -, hb, -⟩ := h1.label_cons
    obtain ⟨E', mode', src', tgt', Y, rfl, hY⟩ := ih hb
    exact ⟨.label pre n cont' E' rest', mode', src', tgt', Y, by simp [Ctx.fill], hY⟩
  | handler pre n cs E rest ih =>
    intro mode src tgt X ys h
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨r1, rfl, h1⟩ := h.values_prefix
    obtain ⟨-, -, body', rest', rfl, hb, -⟩ := h1.handler_cons
    obtain ⟨E', mode', src', tgt', Y, rfl, hY⟩ := ih hb
    exact ⟨.handler pre n cs E' rest', mode', src', tgt', Y, by simp [Ctx.fill], hY⟩
  | frame pre n f E rest ih =>
    intro mode src tgt X ys h
    simp only [Ctx.fill, List.append_assoc, List.singleton_append] at h
    obtain ⟨r1, rfl, h1⟩ := h.values_prefix
    obtain ⟨innerMode, f', body', rest', rfl, -, hb, -⟩ := h1.frame_cons
    obtain ⟨E', mode', src', tgt', Y, rfl, hY⟩ := ih hb
    exact ⟨.frame pre n f' E' rest', mode', src', tgt', Y, by simp [Ctx.fill], hY⟩

/-- **A stuck typed source configuration is blocked on a host call, and so is the
linked configuration related to it.** -/
theorem stuck_transfer {o : GrowOracle} {mode : Mode} {cs ct : Config H} {rs : List CValType}
    (hm : Matching mode cs ct) (typed : ConfigOk cs rs)
    (hnt : ¬ ∃ r : Result, cs.code = r.toAdmin)
    (hno : ∀ x, ¬ Step (profile o) noHost cs x) : decompose? ct.store ct.code ≠ none := by
  rcases Config.progress (P := profile o) (host := divHost) divHost_ok typed with hT | ⟨c', hc'⟩
  · exact absurd hT hnt
  rcases Step.split_host hc' with hstep | ⟨E, a, hh, args, hd, -⟩
  · exact absurd hstep (hno c')
  obtain ⟨fi, yy, ps, rs', hf, hcode, hyy, he, hlen, hfill⟩ := decompose?_sound hd
  have hctl := hm.code
  rw [hfill] at hctl
  obtain ⟨E', mode', src', tgt', Y, hY, hYc⟩ := control_fill E hctl
  obtain ⟨r1, rfl, h1⟩ := hYc.values_prefix
  obtain ⟨r2, rfl, h2⟩ := h1.ref_cons
  obtain ⟨c'', hc'', rfl⟩ := control_callRef hyy h2
  obtain ⟨fi', hf', hF⟩ := hm.stores.function_lookup hf
  have hfi : fi' = fi := by
    cases hF with
    | same => rfl
    | relocated _ _ _ => cases hcode
  subst hfi
  have ha := hostArity?_of hf' hcode he
  rw [← hlen] at ha
  rw [hY]
  have hsome := decompose?_fill_isSome (s := ct.store) hc'' ha E'
  intro hnone
  rw [hnone] at hsome
  cases hsome

end Silmaril.Wasm.Binaryen.LinkBehaviours
