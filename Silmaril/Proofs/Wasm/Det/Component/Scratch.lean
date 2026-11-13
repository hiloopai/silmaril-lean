module

public import Silmaril.Wasm.Det.Component.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# The scratch region and the Hoare-logic VC: proofs

* `ScratchEq m lo hi` is reflexive and a PER (`scratchEq_refl`, `isPER_scratchEq`);
* **the canonical ABI's own writes are confined**: writing bytes inside `[lo, hi)` of memory
  `m` keeps `ScratchEq m lo hi` (`memWrite_scratchEq`), through `writeBytes_size` and
  `writeBytes_get`;
* **the Hoare-logic VC**: two invocations without import calls whose every-run specifications
  `HWP … (RetOrTrap F₁)` and `HWP … (RetOrTrap F₂)` have `F₁ = F₂` agree on outputs
  (`obsAgree_of_hwp`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Component

/-! ## Bytes -/

theorem writeBytes_size (b : ByteArray) (p : Nat) (bs : List UInt8) :
    (writeBytes b p bs).size = b.size := by
  induction bs generalizing b p with
  | nil => rfl
  | cons x xs ih =>
    show (writeBytes (b.set! p x) (p + 1) xs).size = b.size
    rw [ih]
    show (b.data.set! p x).size = b.data.size
    simp only [Array.set!, Array.size_setIfInBounds]

theorem writeBytes_get (b : ByteArray) (p : Nat) (bs : List UInt8) (k : Nat)
    (hk : k < p ∨ p + bs.length ≤ k) : (writeBytes b p bs).data[k]? = b.data[k]? := by
  induction bs generalizing b p with
  | nil => rfl
  | cons x xs ih =>
    show (writeBytes (b.set! p x) (p + 1) xs).data[k]? = b.data[k]?
    have hk' : k < p + 1 ∨ p + 1 + xs.length ≤ k := by
      rcases hk with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by simp only [List.length_cons] at h; omega)
    have hne : p ≠ k := by
      rcases hk with h | h
      · omega
      · simp only [List.length_cons] at h; omega
    rw [ih _ _ hk']
    simp [ByteArray.set!, hne]

/-! ## The scratch region -/

theorem scratchEq_refl (m lo hi : Nat) (s : Store Nat) : ScratchEq m lo hi s s := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun mi₁ mi₂ h₁ h₂ => ?_⟩
  have he : mi₁ = mi₂ := Option.some.inj (h₁.symm.trans h₂)
  rw [he]
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem scratchEq_symm {m lo hi : Nat} {s₁ s₂ : Store Nat} (h : ScratchEq m lo hi s₁ s₂) :
    ScratchEq m lo hi s₂ s₁ := by
  obtain ⟨h₀, hl, hj, hm⟩ := h
  refine ⟨h₀.symm, hl.symm, fun j hj' => (hj j hj').symm, fun mi₁ mi₂ h₁ h₂ => ?_⟩
  obtain ⟨ht, hs, hb⟩ := hm mi₂ mi₁ h₂ h₁
  exact ⟨ht.symm, hs.symm, fun k hk => (hb k hk).symm⟩

theorem scratchEq_trans {m lo hi : Nat} {s₁ s₂ s₃ : Store Nat} (h₁₂ : ScratchEq m lo hi s₁ s₂)
    (h₂₃ : ScratchEq m lo hi s₂ s₃) : ScratchEq m lo hi s₁ s₃ := by
  obtain ⟨a₀, al, aj, am⟩ := h₁₂
  obtain ⟨b₀, bl, bj, bm⟩ := h₂₃
  refine ⟨a₀.trans b₀, al.trans bl, fun j hj => (aj j hj).trans (bj j hj), ?_⟩
  intro mi₁ mi₃ h₁ h₃
  have hlt : m < s₁.mems.length := (List.getElem?_eq_some_iff.mp h₁).1
  have hlt₂ : m < s₂.mems.length := al ▸ hlt
  have h₂ : s₂.mems[m]? = some s₂.mems[m] := List.getElem?_eq_getElem hlt₂
  obtain ⟨ta, sa, ba⟩ := am mi₁ _ h₁ h₂
  obtain ⟨tb, sb, bb⟩ := bm _ mi₃ h₂ h₃
  exact ⟨ta.trans tb, sa.trans sb, fun k hk => (ba k hk).trans (bb k hk)⟩

theorem isPER_scratchEq (m lo hi : Nat) : IsPER (ScratchEq m lo hi) where
  symm h := scratchEq_symm h
  trans h₁ h₂ := scratchEq_trans h₁ h₂

/-- **The canonical ABI's writes into the scratch region are confined.** -/
theorem memWrite_scratchEq {m lo hi p : Nat} {bs : List UInt8} {s t : Store Nat}
    (hp : lo ≤ p) (hq : p + bs.length ≤ hi) (h : memWrite s m p bs = some t) :
    ScratchEq m lo hi s t := by
  unfold memWrite at h
  rcases hmi : s.mems[m]? with _ | mi
  · rw [hmi] at h
    cases h
  · show ScratchEq m lo hi s t
    have hlt : m < s.mems.length := (List.getElem?_eq_some_iff.mp hmi).1
    have ht : t = { s with mems := s.mems.set m { mi with bytes := writeBytes mi.bytes p bs } } := by
      by_cases hc : p + bs.length ≤ mi.bytes.size
      · have h' : some { s with mems := s.mems.set m { mi with bytes := writeBytes mi.bytes p bs } } =
            some t := by simpa only [hmi, hc, ite_true] using h
        exact (Option.some.inj h').symm
      · have h' : (none : Option (Store Nat)) = some t := by simpa only [hmi, hc, ite_false] using h
        cases h'
    rw [ht]
    refine ⟨rfl, (List.length_set ..).symm, fun j hj => ?_, fun mi₁ mi₂ h₁ h₂ => ?_⟩
    · show s.mems[j]? = (s.mems.set m _)[j]?
      rw [List.getElem?_set_ne (Ne.symm hj)]
    · show mi₁.type = mi₂.type ∧ _
      have he₁ : mi₁ = mi := Option.some.inj (h₁.symm.trans hmi)
      have he₂ : mi₂ = { mi with bytes := writeBytes mi.bytes p bs } := by
        have h₂' : (s.mems.set m { mi with bytes := writeBytes mi.bytes p bs })[m]? =
            some { mi with bytes := writeBytes mi.bytes p bs } :=
          List.getElem?_set_self hlt
        exact Option.some.inj (h₂.symm.trans h₂')
      rw [he₁, he₂]
      exact ⟨rfl, (writeBytes_size _ _ _).symm, fun k hk =>
        (writeBytes_get _ _ _ k (by omega)).symm⟩

/-! ## The Hoare-logic VC -/

theorem trap_not_mem_vals {ws : List Val} : Admin.trap ∉ vals ws := by
  intro h
  obtain ⟨v, -, hv⟩ := List.mem_map.mp h
  have h' : some v = Admin.val? Admin.trap := by rw [← Admin.val?_toAdmin v, hv]
  simp [Admin.val?] at h'

theorem throwRef_not_mem_vals {ws : List Val} : Admin.plain .throwRef ∉ vals ws := by
  intro h
  obtain ⟨v, -, hv⟩ := List.mem_map.mp h
  have h' : some v = Admin.val? (.plain .throwRef) := by rw [← Admin.val?_toAdmin v, hv]
  simp [Admin.val?] at h'

theorem vals_inj {ws₁ ws₂ : List Val} (h : vals ws₁ = vals ws₂) : ws₁ = ws₂ := by
  have hi : Function.Injective Val.toAdmin := fun v w hvw => by
    have h' : Admin.val? v.toAdmin = Admin.val? w.toAdmin := by rw [hvw]
    simpa using h'
  exact (List.map_injective_iff.mpr hi) h

/-- A result whose code exits normally with `F` or traps, and is not a trap, is `values F`. -/
theorem result_of_exits {r : Result} {F : List Val} {o : Silmaril.Wasm.Logic.Core.Outcome}
    (hr : r ≠ .trap) (hx : Silmaril.Wasm.Logic.Hoare.Exits o r.toAdmin) (hQ : o = .normal F ∨ o = .trap) :
    r = .values F := by
  rcases hQ with rfl | rfl
  · have hx' : r.toAdmin = vals F := hx
    rcases r with ws | a | -
    · exact congrArg Result.values (vals_inj hx')
    · have hm : Admin.plain .throwRef ∈ vals F := by
        rw [← hx']
        simp [Result.toAdmin]
      exact absurd hm throwRef_not_mem_vals
    · exact absurd rfl hr
  · obtain ⟨vs, rest, hx'⟩ := hx
    have hm : Admin.trap ∈ r.toAdmin := by rw [hx']; simp
    rcases r with ws | a | -
    · exact absurd hm trap_not_mem_vals
    · simp [Result.toAdmin] at hm
    · exact absurd rfl hr

/-- The output of an invocation with a `RetOrTrap F` specification and no import calls. -/
theorem out_of_hwp {P : Profile} {s : Store Nat} {a : Nat} {vs : List Val} {F : List Val}
    (hnc : NoCalls P (invoke s a vs))
    (hH : Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost s {} (invoke s a vs).code (RetOrTrap F))
    {tr : List Call} {d : Config Nat} {o : Out} (hr : Runs P (invoke s a vs) tr d)
    (ho : OutAt d o) : o = .ret (.values F) := by
  cases hr with
  | call hs hd _ => rw [hnc _ hs] at hd; cases hd
  | stop hs =>
    show o = _
    cases ho with
    | call hd => rw [hnc _ hs] at hd; cases hd
    | @ret r hr' hc =>
      show Out.ret r = _
      have hns : ¬ ∃ e, Step P Det.noHost d e := fun ⟨_, he⟩ => Stop.no_step ⟨_, .ret hr' hc⟩ he
      rcases Silmaril.Wasm.Logic.Hoare.hwp_sound hH hs with hst | ⟨o', hx, hQ⟩
      · exact absurd hst hns
      · rw [hc] at hx
        rw [result_of_exits hr' hx hQ]

/-- **Output agreement from the Hoare logic**: two invocations without import calls whose
every-run specifications return the same values (or trap) agree on their outputs. -/
theorem obsAgree_of_hwp {P : Profile} {s₁ s₂ : Store Nat} {a : Nat} {vs : List Val}
    {F₁ F₂ : List Val} (hnc₁ : NoCalls P (invoke s₁ a vs)) (hnc₂ : NoCalls P (invoke s₂ a vs))
    (h₁ : Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost s₁ {} (invoke s₁ a vs).code (RetOrTrap F₁))
    (h₂ : Silmaril.Wasm.Logic.Hoare.HWP P Det.noHost s₂ {} (invoke s₂ a vs).code (RetOrTrap F₂))
    (hF : F₁ = F₂) : ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs) := by
  intro tr d₁ d₂ o₁ o₂ r₁ r₂ ho₁ ho₂
  rw [out_of_hwp hnc₁ h₁ r₁ ho₁, out_of_hwp hnc₂ h₂ r₂ ho₂, hF]

end Silmaril.Proofs.Wasm.Det.Component
