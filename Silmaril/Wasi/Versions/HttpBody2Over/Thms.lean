module

public import Silmaril.Wasi.Versions.HttpBody2Over.Handle.Thms

@[expose] public section

/-!
# HTTP with response bodies across versions: 0.2 over 0.3, theorems

PROVED (standard axioms):

* **`httpB2Over3_sat`, `httpB2Over3_model`**: for every body web `B`, every number of rounds
  and every host of the 0.3 theory with bodies `body3Th B`, the buffering composite
  `httpB2Over3 rounds` is a model of the 0.2 theory with bodies `bodyTh B`. Invariant `JB2`
  (`Silmaril.Wasi.Versions.HttpBody2Over.Defs`); the program of `handle` is
  `Silmaril.Wasi.Versions.HttpBody2Over.Handle`, the buffered answers
  `Silmaril.Wasi.Versions.HttpBody2Over.Steps`.

With `httpB3Over2_model` (`Silmaril.Wasi.Versions.HttpBodyOver`) this gives HTTP response bodies
in both directions. Both are safety results over **every** host of the respective theory; the
components may trap when `rounds` run out, and both theories admit traps.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- A forwarded `set-authority` keeps `JB2`. -/
theorem setAuthB_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    Wp (body3Th B) (.call (jSetAuth, a) fun r => .pure (st, r))
      (fun x q3' => ∃ q2', (bodyTh B).step q2 (.imp setAuthority a x.2) = some q2' ∧ JB2 B x.1 q3' q2')
      q3 := by
  intro r q3' hs
  have hq : q3' = { q3 with base := http3Next q3.base (.imp setAuth3 a r) } :=
    (body3Th_http_inv (f := setAuth3) (by decide) hs).2
  have h2 : (bodyTh B).step q2 (.imp setAuthority a r) =
      some { q2 with base := httpNext q2.base (.imp setAuthority a r) } :=
    bodyTh_of_httpTh (by decide) (gated_step_of (i := HttpSt.init) (n := httpNext)
      (httpOk_ne B.web q2.base (f := setAuthority) (by decide) (by decide) a r))
  refine ⟨_, h2, ?_⟩
  rw [hq, httpNext_setAuth, http3Next_setAuth]
  exact ⟨by simp [hJ.1], hJ.2.1, hJ.2.2⟩

/-- A forwarded `set-path-with-query` keeps `JB2`. -/
theorem setPathB_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    Wp (body3Th B) (.call (jSetPath, a) fun r => .pure (st, r))
      (fun x q3' => ∃ q2', (bodyTh B).step q2 (.imp setPath a x.2) = some q2' ∧ JB2 B x.1 q3' q2')
      q3 := by
  intro r q3' hs
  have hq : q3' = { q3 with base := http3Next q3.base (.imp setPath3 a r) } :=
    (body3Th_http_inv (f := setPath3) (by decide) hs).2
  have h2 : (bodyTh B).step q2 (.imp setPath a r) =
      some { q2 with base := httpNext q2.base (.imp setPath a r) } :=
    bodyTh_of_httpTh (by decide) (gated_step_of (i := HttpSt.init) (n := httpNext)
      (httpOk_ne B.web q2.base (f := setPath) (by decide) (by decide) a r))
  refine ⟨_, h2, ?_⟩
  rw [hq, httpNext_setPath, http3Next_setPath]
  exact ⟨hJ.1, by simp [hJ.2.1], hJ.2.2.1, hJ.2.2.2⟩

/-- An exported function that is none of the outgoing ones is a 0.2 body function. -/
theorem bodyFn_of_mem {f : FnName} (hm : f ∈ httpBodyImports) (h₁ : f ≠ setAuthority)
    (h₂ : f ≠ setPath) (h₃ : f ≠ httpHandle) (h₄ : f ≠ futGet) (h₅ : f ≠ respStatus) :
    isBodyFn f = true := by
  rcases hm with hm | hm
  · simp only [httpImports_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> contradiction
  · simp only [bodyFns2_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The invariant of `httpB2Over3`. -/
theorem httpB2Over3_inv (B : BWeb) (rounds : Nat) :
    WpInv (httpB2Over3 rounds) {} (body3Th B) (bodyTh B) (JB2 B) where
  init := ⟨rfl, rfl, fun _ _ h => by simp [lookup] at h,
    fun _ _ h => by simp [lookup, bodyTh, gated, HttpSt.init] at h,
    fun _ _ h => by simp [lookup, bodyTh, gated] at h,
    fun _ _ _ h => by simp [lookup, bodyTh, gated] at h,
    fun _ _ h => by simp [lookup, bodyTh, gated] at h,
    fun _ _ h => by simp [lookup, bodyTh, gated] at h⟩
  call := by
    intro st q3 q2 q hJ
    by_cases h₁ : q.1.1 = setAuthority
    · simp only [httpB2Over3, h₁, ↓reduceIte]
      exact setAuthB_step B hJ q.2
    by_cases h₂ : q.1.1 = setPath
    · simp only [httpB2Over3, h₂, show setPath ≠ setAuthority by decide, ↓reduceIte]
      exact setPathB_step B hJ q.2
    by_cases h₃ : q.1.1 = httpHandle
    · simp only [httpB2Over3, h₃, show httpHandle ≠ setAuthority by decide,
        show httpHandle ≠ setPath by decide, ↓reduceIte]
      exact wp_handleB B rounds hJ q.2
    by_cases h₄ : q.1.1 = futGet
    · simp only [httpB2Over3, h₄, show futGet ≠ setAuthority by decide,
        show futGet ≠ setPath by decide, show futGet ≠ httpHandle by decide, ↓reduceIte]
      exact getResB_step B hJ q.2
    by_cases h₅ : q.1.1 = respStatus
    · simp only [httpB2Over3, h₅, show respStatus ≠ setAuthority by decide,
        show respStatus ≠ setPath by decide, show respStatus ≠ httpHandle by decide,
        show respStatus ≠ futGet by decide, ↓reduceIte]
      exact statusResB_step B hJ q.2
    simp only [httpB2Over3, h₁, h₂, h₃, h₄, h₅, ↓reduceIte]
    exact bodyRes2_step B hJ (bodyFn_of_mem q.1.2 h₁ h₂ h₃ h₄ h₅) q.2

/-- **The component guarantee of HTTP with bodies, 0.2 over 0.3.** -/
theorem httpB2Over3_sat (B : BWeb) (rounds : Nat) :
    (agP (body3Th B) (retG (bodyTh B))).holds (ofSBody (httpB2Over3 rounds) {}) :=
  ag_of_wpInv (httpB2Over3_inv B rounds)

/-- **HTTP with response bodies, 0.2 over 0.3**: over every host of the 0.3 theory with bodies
of the body web `B`, the buffering composite is a model of the 0.2 theory with bodies of the
same web. -/
theorem httpB2Over3_model (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBody3Fns}
    (hη : (hostSat (body3Th B).Accepts).holds η) :
    (hostSat (bodyTh B).Accepts).holds (link η (ofSBody (httpB2Over3 rounds) {})) :=
  link_model (httpB2Over3_sat B rounds) hη

end Silmaril.Wasi.Versions.Net
