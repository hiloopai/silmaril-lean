module

public import Silmaril.Wasi.Versions.HttpFieldsOver.Defs
public import Silmaril.Wasi.Versions.HttpFields.Thms

@[expose] public section

/-!
# HTTP headers across versions: theorems

PROVED (standard axioms):

* **`fields2Over3_model`**: over every host of the 0.3 `fields` theory, the forwarding
  composite is a model of the 0.2 one. Invariant: the two theory states are equal.
* **`fields3Over2_model`**: over every host of the 0.2 `fields` theory, the composite (with
  `get-and-delete` as `get` then `delete`) is a model of the 0.3 one. Same invariant.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- An exported function has its operation. -/
theorem opD_of {N : FieldsFns} {f : FnName} (hm : f ∈ N.fns) : N.op f = some (opD N f) := by
  have hs : (N.op f).isSome = true := hm
  unfold opD
  cases h : N.op f with
  | none => rw [h] at hs; cases hs
  | some o => rfl

/-- A forwarded call: the two theories take the same step. -/
theorem fwd_step {N N' : FieldsFns} {f f' : FnName} {o : FOp} (h : N.op f = some o)
    (h' : N'.op f' = some o) {q q' : FSt} {a : List Val} {r : Option (List Val)}
    (hs : (fieldsTh N').step q (.imp f' a r) = some q') : (fieldsTh N).step q (.imp f a r) = some q' := by
  rw [fieldsTh_step N' h'] at hs
  rw [fieldsTh_step N h]
  exact hs

/-- The invariant of `fields2Over3`. -/
theorem fields2Over3_inv :
    WpInv fields2Over3 () (fieldsTh fieldsFns3) (fieldsTh fieldsFns2) (fun _ q3 q2 => q2 = q3) where
  init := rfl
  call := by
    intro _ q3 q2 q hJ r q3' hs
    exact ⟨q3', hJ ▸ fwd_step (opD_of q.1.2) (op3_fn3 _) hs, rfl⟩

/-- **`fields` 0.2 over 0.3**: over every host of the 0.3 `fields` theory, the composite is a
model of the 0.2 one. -/
theorem fields2Over3_model {Y : Sig.{0}} {η : Host Y fieldsFns3.fns}
    (hη : (hostSat (fieldsTh fieldsFns3).Accepts).holds η) :
    (hostSat (fieldsTh fieldsFns2).Accepts).holds (link η (ofSBody fields2Over3 ())) :=
  link_model (ag_of_wpInv fields2Over3_inv) hη

/-! ## `get-and-delete` over 0.2 -/

/-- `get` keeps the state. -/
theorem opNext_get (q : FSt) (a : List Val) (r : Option (List Val)) : opNext .get q a r = q := by
  simp [opNext, FOp.mutates]

/-- A failed `delete` / `get-and-delete` keeps the state. -/
theorem opNext_fail {o : FOp} (ho : o = .delete ∨ o = .getDel) (q : FSt) (a : List Val)
    {r : Option (List Val)} (h : isOkAns r = false) : opNext o q a r = q := by
  rcases ho with rfl | rfl <;> simp [opNext, FOp.mutates, h]

/-- A successful `get-and-delete` moves the state as a successful `delete`. -/
theorem opNext_getDel (q : FSt) (a : List Val) (x : Val) {r : Option (List Val)}
    (h : isOkAns r = true) : opNext .getDel q a (some [okV (some x)]) = opNext .delete q a r := by
  have h1 : isOkAns (some [okV (some x)]) = true := rfl
  simp only [opNext, FOp.mutates, h, h1, Bool.and_self, ↓reduceIte]
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 hd =>
    cases hl : lookup hd q with
    | none => simp only [hl]
    | some o =>
      cases o with
      | none => simp only [hl]
      | some m =>
        simp only [hl]
        rcases a' with _ | ⟨nv, a''⟩ <;> rfl
  all_goals rfl

/-- A trap passes every check. -/
theorem opOk_none (o : FOp) (q : FSt) (a : List Val) : opOk o q a none = true := by
  unfold opOk
  split
  · split
    · cases o <;> rfl
    · rfl
  · rfl

/-- An error of `get-and-delete` passes the check. -/
theorem opOk_getDel_err (q : FSt) (a : List Val) (e : Option Val) :
    opOk .getDel q a (some [.variant 1 e]) = true := by
  unfold opOk
  split
  · split
    · next a' m _ => rcases a' with _ | ⟨nv, a''⟩ <;> rfl
    · rfl
  · rfl

/-- The values `get` answered pass the check of `get-and-delete`. -/
theorem opOk_getDel_ok (q : FSt) (a : List Val) (x : Val) (h : opOk .get q a (some [x]) = true) :
    opOk .getDel q a (some [okV (some x)]) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 hd =>
    cases hl : lookup hd q with
    | none => simp [opOk, hl]
    | some o =>
      cases o with
      | none => simp [opOk, hl]
      | some m =>
        have h' : opCheck .get m a' (some [x]) = true := by simpa [opOk, hl] using h
        simp only [opOk, hl]
        rcases a' with _ | ⟨nv, a''⟩
        · rfl
        · cases hn : nameOf nv <;> simp_all [opCheck, okV]
  all_goals rfl

/-- A step of the 0.3 theory on `get-and-delete`. -/
theorem getDel_step {f : FnName} (hf : fieldsFns3.op f = some .getDel) {q q' : FSt} {a : List Val}
    {r : Option (List Val)} (hok : opOk .getDel q a r = true) (hq : opNext .getDel q a r = q') :
    (fieldsTh fieldsFns3).step q (.imp f a r) = some q' := by
  rw [fieldsTh_step _ hf, hok, hq]; rfl

/-- After `get` answered `x`: `delete`, then the answer. -/
theorem wp_delK {f : FnName} (hf : fieldsFns3.op f = some .getDel) (q : FSt) (a : List Val)
    (x : Val) (hok₁ : opOk .get q a (some [x]) = true) :
    Wp (fieldsTh fieldsFns2) (.call (iFDel2, a) (delK x))
      (fun x q' => ∃ qG', (fieldsTh fieldsFns3).step q (.imp f a x.2) = some qG' ∧ qG' = q') q := by
  intro r₂ q₂ hs₂
  have hs₂' : (if opOk .delete q a r₂ then some (opNext .delete q a r₂) else none) = some q₂ := by
    rw [← fieldsTh_step _ (op2_fn2 (o := .delete) (by decide))]; exact hs₂
  have hq₂ : q₂ = opNext .delete q a r₂ := by
    by_cases hc : opOk .delete q a r₂ = true
    · simpa [hc] using hs₂'.symm
    · simp [hc] at hs₂'
  unfold delK
  by_cases hr : isOkAns r₂ = true
  · simp only [hr, ↓reduceIte]
    exact ⟨q₂, getDel_step hf (opOk_getDel_ok q a x hok₁) (by rw [hq₂, opNext_getDel q a x hr]), rfl⟩
  · have hr' : isOkAns r₂ = false := by simpa using hr
    have hq₂' : q₂ = q := by rw [hq₂, opNext_fail (Or.inl rfl) q a hr']
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    split
    · next e => exact ⟨q, getDel_step hf (opOk_getDel_err q a e) (opNext_fail (Or.inr rfl) q a rfl),
        hq₂'.symm⟩
    · exact ⟨q, getDel_step hf (opOk_none _ q a) (opNext_fail (Or.inr rfl) q a rfl), hq₂'.symm⟩

/-- **The program of `get-and-delete`** answers as the 0.3 theory allows, with the same state
as the 0.2 theory. -/
theorem wp_getDel {f : FnName} (hf : fieldsFns3.op f = some .getDel) (q : FSt) (a : List Val) :
    Wp (fieldsTh fieldsFns2) (getDelProg a)
      (fun x q' => ∃ qG', (fieldsTh fieldsFns3).step q (.imp f a x.2) = some qG' ∧ qG' = q') q := by
  intro r₁ q₁ hs₁
  have hs₁' : (if opOk .get q a r₁ then some (opNext .get q a r₁) else none) = some q₁ := by
    rw [← fieldsTh_step _ (op2_fn2 (o := .get) (by decide))]; exact hs₁
  have hok₁ : opOk .get q a r₁ = true := by
    by_contra hc; simp [hc] at hs₁'
  have hq₁ : q₁ = q := by simpa [hok₁, opNext_get] using hs₁'.symm
  beta_reduce
  split
  · next x => exact hq₁ ▸ wp_delK hf q a x hok₁
  · exact ⟨q, getDel_step hf (opOk_none _ q a) (opNext_fail (Or.inr rfl) q a rfl), hq₁.symm⟩

/-- The invariant of `fields3Over2`. -/
theorem fields3Over2_inv :
    WpInv fields3Over2 () (fieldsTh fieldsFns2) (fieldsTh fieldsFns3) (fun _ q2 q3 => q3 = q2) where
  init := rfl
  call := by
    intro _ q2 q3 q hJ
    by_cases hg : opD fieldsFns3 q.1.1 = .getDel
    · simp only [fields3Over2, hg, ↓reduceIte]
      have hf : fieldsFns3.op q.1.1 = some .getDel := hg ▸ opD_of q.1.2
      refine Wp.mono (fun x q' h => ?_) (wp_getDel hf q2 q.2)
      obtain ⟨qG', hs, rfl⟩ := h
      exact ⟨qG', hJ ▸ hs, rfl⟩
    · simp only [fields3Over2, hg, ↓reduceIte]
      intro r q2' hs
      exact ⟨q2', hJ ▸ fwd_step (opD_of q.1.2) (op2_fn2 hg) hs, rfl⟩

/-- **`fields` 0.3 over 0.2**: over every host of the 0.2 `fields` theory, the composite is a
model of the 0.3 one. -/
theorem fields3Over2_model {Y : Sig.{0}} {η : Host Y fieldsFns2.fns}
    (hη : (hostSat (fieldsTh fieldsFns2).Accepts).holds η) :
    (hostSat (fieldsTh fieldsFns3).Accepts).holds (link η (ofSBody fields3Over2 ())) :=
  link_model (ag_of_wpInv fields3Over2_inv) hη

end Silmaril.Wasi.Versions.Net
