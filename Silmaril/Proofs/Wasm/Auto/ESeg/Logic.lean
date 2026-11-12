module

public import Silmaril.Proofs.Wasm.Auto.ESeg.Check
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Examples.Common.Thms

/-! # From exec-level equivalence to the every-run logic

The e-graph certificates prove equivalences of the straight-line interpreter `exec`
(`Silmaril.Wasm.Auto.EGraph.SegEquiv`, `Silmaril.Wasm.Auto.ESeg.BodyEquiv`). Here they become the
every-run statements of the equiv track (`Silmaril.Wasm.Auto.Equiv.SegEquiv` and `OutEquiv`:
the weakest preconditions `Wp m P host` agree, in both readings `HWP`/`TWP`, every profile
and host relation, for every postcondition, or every postcondition blind to the locals), for
segments whose effect summary is typed and trap-free (`checkPure`):

* `pure_runs`: such a segment runs (`exec` gives a result) in every frame typed by `Γ`;
* `wp_exec_iff`: the weakest precondition of code that `exec` runs is that of its result
  (forward by `Silmaril.Wasm.Examples.Common.Wp.exec_eq`, backward along `exec_sound`'s run by
  `HWP.step_inv`/`TSafe.step_inv`);
* `wp_vals_iff`: values satisfy `Wp` exactly when they satisfy the normal postcondition;
* **`equivSeg_of_segEquiv`**: `EGraph.SegEquiv Γ a b` gives `Equiv.SegEquiv Γ [] a b`;
* **`outEquiv_of_bodyEquiv`**: `BodyEquiv Γ a b` gives `Equiv.OutEquiv Γ [] a b`: the two
  bodies have the same every-run weakest precondition for every postcondition blind to the
  locals, in particular the function postconditions of the call rules (the function-level
  statement).

Trapping segments (division) keep the exec-level statement only; their every-run reading
needs the trap rules (`Wp.intBinOp_trap`, `Safe.trap_post`) and is left open.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec_sound Post localVal?)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.EGraph

variable {H : Type}

/-- **A typed, trap-free segment runs** in every frame typed by `Γ`. -/
theorem pure_runs {Γ : List IntType} {a : List Instr} (ha : checkPure Γ a = true) (s : Store H)
    {f : Frame} (rs : List Val) (hf : FrameOk Γ f) : ∃ r, exec s f rs a = some r := by
  simp only [checkPure, Bool.and_eq_true] at ha
  obtain ⟨hl, ha⟩ := ha
  have hl' : Γ.length < 2 ^ 32 := by simpa [localsOk] using hl
  split at ha
  · rename_i A hA
    have hdef : ∀ e ∈ A.terms, (e.eval f).isSome := by
      intro e he
      have k := List.all_eq_true.mp ha e he
      simp only [Bool.and_eq_true, Option.isSome_iff_exists] at k
      obtain ⟨hn, t, ht⟩ := k
      obtain ⟨x, hx⟩ := noTrap_total hf ht hn
      simp [hx]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (den_isSome_iff.mpr hdef)
    exact ⟨_, by rw [lift_exec hl' hA s rs hf, hp]; rfl⟩
  · cases ha

theorem wp_steps_inv' {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {c c' : Config H} (hs : Steps P host c c') (h : Wp m P host c.store c.frame c.code Q) :
    Wp m P host c'.store c'.frame c'.code Q := by
  induction hs with
  | refl => exact h
  | tail _ hst ih =>
    cases m
    · exact HWP.step_inv ih hst
    · exact TSafe.step_inv ih hst

/-- **Code that `exec` runs** has the weakest precondition of its result. -/
theorem wp_exec_iff {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {s s' : Store H} {f f' : Frame} {vs rs' : List Val} {a : List Instr} (rest : List Admin)
    (he : exec s f vs.reverse a = some (s', f', rs')) :
    Wp m P host s f (vals vs ++ expression a ++ rest) Q ↔
      Wp m P host s' f' (vals rs'.reverse ++ rest) Q := by
  constructor
  · intro hw
    have hs := exec_sound (P := P) (host := host) rest he
    rw [List.reverse_reverse] at hs
    exact wp_steps_inv' hs hw
  · exact Silmaril.Wasm.Examples.Common.Wp.exec_eq he

/-- Values satisfy the weakest precondition exactly when they satisfy the normal
postcondition. -/
theorem wp_vals_iff {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {s : Store H} {f : Frame} {vs : List Val} :
    Wp m P host s f (vals vs) Q ↔ Q s f (.normal vs) :=
  ⟨fun h => HWP.sound_vals (Wp.hwp h) Relation.ReflTransGen.refl, Wp.of_vals⟩

/-! ## The frames of the equiv track are typed -/

theorem frameOk_frameAt {lt : List IntType} (hl : lt.length < 2 ^ 32) (f : Frame)
    (ρ : Equiv.Env) : FrameOk lt (Equiv.frameAt f ρ (Equiv.initState lt [])) := by
  intro i t hi
  have hlt : i < lt.length := (List.getElem?_eq_some_iff.mp hi).1
  have ht : lt[i] = t := (List.getElem?_eq_some_iff.mp hi).2
  refine ⟨Equiv.ev ρ t (.var i), ?_⟩
  simp only [localVal?, Frame.local?, Equiv.frameAt, Equiv.initState, List.getElem?_map,
    List.getElem?_mapIdx]
  rw [lidx_toNat (by omega), hi]
  rfl

theorem codeAt_init (lt : List IntType) (ρ : Equiv.Env) (us : List Val) (a : List Instr)
    (rest : List Admin) :
    Equiv.codeAt ρ (Equiv.initState lt []) us a rest = vals us ++ expression a ++ rest := by
  simp [Equiv.codeAt, Equiv.stackAt, Equiv.initState]

/-! ## The bridges -/

/-- **Segment equivalence in the every-run logic**: typed, trap-free segments that are
exec-equivalent on frames typed by `Γ` have the same every-run weakest precondition in every
context (the second segment then runs too). -/
theorem equivSeg_of_segEquiv {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b)
    (ha : checkPure Γ a = true) : Equiv.SegEquiv Γ [] a b := by
  intro m P H host s f ρ us rest Q
  have hl : Γ.length < 2 ^ 32 := by
    simp only [checkPure, Bool.and_eq_true, localsOk, decide_eq_true_eq] at ha; exact ha.1
  have hf := frameOk_frameAt hl f ρ
  obtain ⟨⟨s₁, f₁, r₁⟩, h₁⟩ := pure_runs ha s us.reverse hf
  have h₂ : exec s (Equiv.frameAt f ρ (Equiv.initState Γ [])) us.reverse b = some (s₁, f₁, r₁) := by
    rw [← h s _ us.reverse hf, h₁]
  rw [codeAt_init, codeAt_init, wp_exec_iff rest h₁, wp_exec_iff rest h₂]

/-- **Function bodies in the every-run logic**: typed, trap-free bodies that are equivalent up
to their locals have the same every-run weakest precondition for every postcondition blind to
the locals (such as `funcPost` and `bodyPost` of the call rules). -/
theorem outEquiv_of_bodyEquiv {Γ : List IntType} {a b : List Instr} (h : BodyEquiv Γ a b)
    (ha : checkPure Γ a = true) (hb : checkPure Γ b = true) : Equiv.OutEquiv Γ [] a b := by
  intro m P H host s f ρ us Q hQ
  have hl : Γ.length < 2 ^ 32 := by
    simp only [checkPure, Bool.and_eq_true, localsOk, decide_eq_true_eq] at ha; exact ha.1
  have hf := frameOk_frameAt hl f ρ
  obtain ⟨⟨s₁, f₁, r₁⟩, h₁⟩ := pure_runs ha s us.reverse hf
  obtain ⟨⟨s₂, f₂, r₂⟩, h₂⟩ := pure_runs hb s us.reverse hf
  have ho := h s _ us.reverse hf
  rw [h₁, h₂] at ho
  obtain ⟨rfl, hmod, rfl⟩ := ho
  rw [codeAt_init, codeAt_init, wp_exec_iff [] h₁, wp_exec_iff [] h₂]
  simp only [List.append_nil]
  rw [wp_vals_iff, wp_vals_iff]
  exact hQ s₁ f₁ f₂ _ hmod

end Silmaril.Proofs.Wasm.Auto.ESeg
