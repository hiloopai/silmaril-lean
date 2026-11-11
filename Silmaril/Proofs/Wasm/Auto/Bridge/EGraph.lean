module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Mod
public import Silmaril.Wasm.Auto.EGraph.Thms

/-!
# E-graph certificates at the function level

`modEquiv_of_segEquiv`: an e-graph certificate (`Silmaril.Wasm.Auto.EGraph.SegEquiv`, equal runs of
the straight-line interpreter `exec` from every frame typed by `Γ`) on the bodies of two
summarised exports with the same local types `Γ` proves `ModEquiv` at every profile. The bodies
must be plain (`plainI`: no `select`, `block`, `if`), so that their summaries are runs of `exec`
(`Silmaril.Wasm.Auto.Equiv.sexec_exec`), and have fewer than `2^32` locals.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Core (exec localVal?)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModEquiv)

/-- On plain code, `xexec` is `sexec`. -/
theorem sexec_of_xexec : ∀ (n : Nat) {S S' : SState} {a : List Instr},
    (∀ i ∈ a, plainI i = true) → xexec n S a = some S' → sexec S a = some S'
  | 0, _, _, _, _, h => by simp [xexec] at h
  | n + 1, S, S', [], _, h => by
    have hS : S = S' := by simpa [xexec] using h
    rw [hS]
    rfl
  | n + 1, S, S', i :: is, hp, h => by
    have hi : plainI i = true := hp i List.mem_cons_self
    have hd : xone (xexec n) S i = sstep S i := xone_default
      (by rintro ⟨ts, rfl⟩; simp [plainI] at hi) (by rintro ⟨bt, b, rfl⟩; simp [plainI] at hi)
      (by rintro ⟨bt, b₁, b₂, rfl⟩; simp [plainI] at hi)
    have hrest : ∀ i ∈ is, plainI i = true := fun i' hi' => hp i' (List.mem_cons_of_mem _ hi')
    simp only [xexec, hd] at h
    simp only [sexec]
    split at h
    · rename_i S₁ h₁
      rw [h₁]
      exact sexec_of_xexec n hrest h
    · cases h

/-- A frame denoted by a symbolic state with locals of types `Γ` is typed by `Γ`. -/
theorem frameOk_frameAt {Γ : List IntType} {S : SState} (hΓ : S.locals.map (·.1) = Γ)
    (hn : Γ.length < 2 ^ 32) (f : Frame) (ρ : Env) : EGraph.FrameOk Γ (frameAt f ρ S) := by
  intro i t hi
  have hlt : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : S.locals.length = Γ.length := by simpa using congrArg List.length hΓ
  have hil : i < S.locals.length := hlen ▸ hlt
  have ht : (S.locals[i]'hil).1 = t := by
    have h₁ : (S.locals.map (·.1))[i]? = some t := hΓ ▸ hi
    simpa [hil] using h₁
  have hidx : (EGraph.lidx i).toNat = i := by
    have hi32 : i < 4294967296 := Nat.lt_trans hlt hn
    simp [EGraph.lidx, Idx.toNat, Fin.ofNat, hi32]
  refine ⟨ht ▸ ev ρ (S.locals[i]'hil).1 (S.locals[i]'hil).2, ?_⟩
  simp only [localVal?, Frame.local?, hidx, frameAt, List.getElem?_map, List.getElem?_eq_getElem hil,
    Option.map_some]
  subst ht
  rfl

/-- The body of a summarised export, with its local types. -/
theorem fnSum_body {m : Module} {j : Nat} {A : FnSum} {Γ : List IntType} {a : List Instr}
    (hA : fnSum? m j = some A) (ha : fnBody? m j = some (Γ, a)) :
    ∃ ls, Γ = A.params ++ ls ∧ xexec fnFuel (fnInit A.params ls) a = some A.final := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSum?_inv hA
  obtain ⟨code, ps, rs, ls, S, hcode, hps, hrs, hls, hx, -, rfl⟩ := sumOf_inv hs
  have hb : fnBody? m j = some (ps ++ ls, code.body) := by
    simp only [fnBody?, fnBodyI, hI, hft, hfi, hcode, hps, hls]
  obtain ⟨rfl, rfl⟩ : Γ = ps ++ ls ∧ a = code.body := by
    have h₁ : some (Γ, a) = some (ps ++ ls, code.body) := ha.symm.trans hb
    simpa using h₁
  exact ⟨ls, rfl, hx⟩

/-- A plain summarised body runs, by `exec`, to its summary's stack. -/
theorem exec_of_fnSum {m : Module} {j : Nat} {A : FnSum} {Γ : List IntType} {a : List Instr}
    (hA : fnSum? m j = some A) (ha : fnBody? m j = some (Γ, a)) (hpa : ∀ i ∈ a, plainI i = true)
    {H : Type} (s : Store H) (f : Frame) (ρ : Env) :
    ∃ ls F', Γ = A.params ++ ls ∧
      exec s (frameAt f ρ (fnInit A.params ls)) [] a = some (s, F', stackAt ρ A.final) := by
  obtain ⟨ls, hΓ, hx⟩ := fnSum_body hA ha
  have hs : sexec (fnInit A.params ls) a = some A.final := sexec_of_xexec fnFuel hpa hx
  have he := sexec_exec (ρ := ρ) hs s f []
  refine ⟨ls, frameAt f ρ A.final, hΓ, ?_⟩
  simpa [fnInit, stackAt] using he

/-- The local types of `fnInit`. -/
theorem fnInit_types (ps ls : List IntType) : (fnInit ps ls).locals.map (·.1) = ps ++ ls := by
  have h₁ : (ps.mapIdx fun i t => (t, Term.var i)).map (·.1) = ps := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  simp [fnInit, Function.comp_def, h₁]

/-- What `egraphLiftOk` checks. -/
theorem egraphLiftOk_inv {m₁ m₂ : Module} {j : Nat} {Γ : List IntType} {a b : List Instr}
    (hok : egraphLiftOk m₁ m₂ j Γ = true) (ha : fnBody? m₁ j = some (Γ, a))
    (hb : fnBody? m₂ j = some (Γ, b)) :
    ∃ A B, fnSum? m₁ j = some A ∧ fnSum? m₂ j = some B ∧ A.params = B.params ∧
      (∀ i ∈ a, plainI i = true) ∧ (∀ i ∈ b, plainI i = true) ∧ Γ.length < 2 ^ 32 := by
  unfold egraphLiftOk at hok
  rw [ha, hb] at hok
  split at hok
  · rename_i A B Γ₁ a' Γ₂ b' hA hB ha' hb'
    simp only [Option.some.injEq, Prod.mk.injEq] at ha' hb'
    obtain ⟨-, rfl⟩ := ha'
    obtain ⟨-, rfl⟩ := hb'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
    exact ⟨A, B, hA, hB, hok.1.1.1.1.1, hok.1.1.2, hok.1.2, hok.2⟩
  · cases hok

/-- **An e-graph certificate on the bodies proves module equivalence**, at every profile, for
every reflexive relation, under the decidable side conditions `egraphLiftOk`. -/
theorem modEquiv_of_egraph {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} {Γ : List IntType} {a b : List Instr}
    (hok : egraphLiftOk m₁ m₂ j Γ = true) (ha : fnBody? m₁ j = some (Γ, a))
    (hb : fnBody? m₂ j = some (Γ, b)) (h : EGraph.SegEquiv Γ a b) :
    ModEquiv R P m₁ m₂ j := by
  obtain ⟨A, B, hA, hB, hp, hpa, hpb, hn⟩ := egraphLiftOk_inv hok ha hb
  refine modEquiv_of_out hR hA hB hp fun vs _ => ?_
  obtain ⟨ls, F₁, hΓ₁, he₁⟩ := exec_of_fnSum hA ha hpa (H := Nat) {} {} (envOfVals vs)
  obtain ⟨ls', F₂, hΓ₂, he₂⟩ := exec_of_fnSum hB hb hpb (H := Nat) {} {} (envOfVals vs)
  have hls : ls' = ls := by
    rw [hp] at hΓ₁
    exact List.append_cancel_left (hΓ₂.symm.trans hΓ₁)
  subst hls
  have hok' : EGraph.FrameOk Γ (frameAt {} (envOfVals vs) (fnInit A.params ls')) :=
    frameOk_frameAt (by rw [fnInit_types, hΓ₁]) hn _ _
  have hseg := h (H := Nat) {} _ [] hok'
  rw [he₁, hp, he₂] at hseg
  have hst : stackAt (envOfVals vs) A.final = stackAt (envOfVals vs) B.final := by
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hseg
    simpa using hseg.2
  simp only [fnOut, hst]

end Silmaril.Proofs.Wasm.Auto.Bridge