module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Rel

/-!
# The built-ins on bytes: facts used by the host-call runs

`bi_congr`: `bi` depends on the memory only below `MSZ` when its buffer lies there (`memOK`);
`bi_bytes`: it leaves bytes below `256`; `bi_shape`: `stream.read`/`stream.write` take three
arguments and give one result, the drops one argument and no result. `memOf_agree`,
`memR_enc`: the Core memory read as bytes, and written back (`encMem`), under `MemR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI M32 upd slice writeBytes byteOf u8v)
open Silmaril.Wasm.Component.Streams.Drop (dstep)

variable {H : Type} {ma : Nat}

theorem writeBytes_congr {m₁ m₂ : Nat → Nat} (hm : ∀ a, a < MSZ → m₁ a = m₂ a) (p : Nat)
    (bs : List Nat) : ∀ a, a < MSZ → writeBytes m₁ p bs a = writeBytes m₂ p bs a := by
  intro a ha
  simp only [writeBytes]
  split
  · rfl
  · exact hm a ha

theorem slice_congr {m₁ m₂ : Nat → Nat} (hm : ∀ a, a < MSZ → m₁ a = m₂ a) {p n : Nat}
    (hpn : p + n ≤ MSZ) : slice m₁ p n = slice m₂ p n := by
  simp only [slice]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hm _ (by omega)

section Cases

variable {q q' : HQ} {m m₁ m₂ m' m₁' : Nat → Nat} {res : List Nat} {hd p n : Nat}

theorem congr_read (hm : ∀ a, a < MSZ → m₁ a = m₂ a)
    (h : bi .streamRead [hd, p, n] q m₁ = some (q', m₁', res)) :
    ∃ m₂', bi .streamRead [hd, p, n] q m₂ = some (q', m₂', res) ∧ ∀ a, a < MSZ → m₁' a = m₂' a := by
  simp only [bi] at h ⊢
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, by simp only [hc, and_self, ↓reduceIte], writeBytes_congr hm p _⟩
    · cases h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, by simp only [hc, ↓reduceIte], hm⟩
    · cases h
  · cases h

theorem congr_write (hm : ∀ a, a < MSZ → m₁ a = m₂ a) (hok : memOK MSZ .streamWrite [hd, p, n] = true)
    (h : bi .streamWrite [hd, p, n] q m₁ = some (q', m₁', res)) :
    ∃ m₂', bi .streamWrite [hd, p, n] q m₂ = some (q', m₂', res) ∧ ∀ a, a < MSZ → m₁' a = m₂' a := by
  have hs : slice m₁ p n = slice m₂ p n := slice_congr hm (of_decide_eq_true hok)
  simp only [bi, hs] at h ⊢
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, by simp only [hc, ↓reduceIte], hm⟩
    · cases h
  · cases h

theorem congr_drop {b : BI} (hb : b = .dropR ∨ b = .dropW) (hm : ∀ a, a < MSZ → m₁ a = m₂ a)
    (h : bi b [hd] q m₁ = some (q', m₁', res)) :
    ∃ m₂', bi b [hd] q m₂ = some (q', m₂', res) ∧ ∀ a, a < MSZ → m₁' a = m₂' a := by
  rcases hb with rfl | rfl
  all_goals
    simp only [bi] at h ⊢
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨_, by simp only [hx, Option.map_some], hm⟩

end Cases

/-- **`bi` reads the memory only below `MSZ`.** -/
theorem bi_congr {b : BI} {as : List Nat} {q q' : HQ} {m₁ m₂ m₁' : Nat → Nat} {res : List Nat}
    (hm : ∀ a, a < MSZ → m₁ a = m₂ a) (hok : memOK MSZ b as = true)
    (h : bi b as q m₁ = some (q', m₁', res)) :
    ∃ m₂', bi b as q m₂ = some (q', m₂', res) ∧ ∀ a, a < MSZ → m₁' a = m₂' a := by
  unfold bi at h
  split at h
  · exact congr_read hm (by unfold bi; exact h)
  · exact congr_write hm hok (by unfold bi; exact h)
  · exact congr_drop (.inl rfl) hm (by unfold bi; exact h)
  · exact congr_drop (.inr rfl) hm (by unfold bi; exact h)
  · cases h

theorem byteOf_lt (v : Silmaril.Wasm.Component.Val) : byteOf v < 256 := by
  unfold byteOf
  split
  · rename_i x; exact x.isLt
  · decide

/-- What a successful built-in call gives: the arity of its arguments, the shape of its results,
and its memory (bytes written at one place, or unchanged). -/
def BiFacts (b : BI) (as : List Nat) (m m' : Nat → Nat) (res : List Nat) : Prop :=
  as.length = arity b ∧ ((∃ r, res = [r]) ∧ (b = .streamRead ∨ b = .streamWrite) ∨
    res = [] ∧ (b = .dropR ∨ b = .dropW)) ∧
  ((∃ (p : Nat) (xs : List Silmaril.Wasm.Component.Val), m' = writeBytes m p (xs.map byteOf)) ∨ m' = m)

section Facts

variable {q q' : HQ} {m m' : Nat → Nat} {res : List Nat} {hd p n : Nat}

theorem facts_read (h : bi .streamRead [hd, p, n] q m = some (q', m', res)) :
    BiFacts .streamRead [hd, p, n] m m' res := by
  simp only [bi] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨rfl, .inl ⟨⟨_, rfl⟩, .inl rfl⟩, .inl ⟨p, _, rfl⟩⟩
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨rfl, .inl ⟨⟨_, rfl⟩, .inl rfl⟩, .inr rfl⟩
    · cases h
  · cases h

theorem facts_write (h : bi .streamWrite [hd, p, n] q m = some (q', m', res)) :
    BiFacts .streamWrite [hd, p, n] m m' res := by
  simp only [bi] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨rfl, .inl ⟨⟨_, rfl⟩, .inr rfl⟩, .inr rfl⟩
    · cases h
  · cases h

theorem facts_drop {b : BI} (hb : b = .dropR ∨ b = .dropW) (h : bi b [hd] q m = some (q', m', res)) :
    BiFacts b [hd] m m' res := by
  rcases hb with rfl | rfl
  all_goals
    simp only [bi] at h
    obtain ⟨x, -, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact ⟨rfl, .inr ⟨rfl, by simp⟩, .inr rfl⟩

end Facts

/-- **What a successful built-in call gives.** -/
theorem bi_facts {b : BI} {as : List Nat} {q q' : HQ} {m m' : Nat → Nat} {res : List Nat}
    (h : bi b as q m = some (q', m', res)) : BiFacts b as m m' res := by
  unfold bi at h
  split at h
  · exact facts_read (by unfold bi; exact h)
  · exact facts_write (by unfold bi; exact h)
  · exact facts_drop (.inl rfl) (by unfold bi; exact h)
  · exact facts_drop (.inr rfl) (by unfold bi; exact h)
  · cases h

theorem writeBytes_bytes {m : Nat → Nat} (hm : ∀ a, a < MSZ → m a < 256) (p : Nat)
    (xs : List Silmaril.Wasm.Component.Val) : ∀ a, a < MSZ → writeBytes m p (xs.map byteOf) a < 256 := by
  intro a ha
  simp only [writeBytes]
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases xs[a - p]? with
    | none => decide
    | some v => exact byteOf_lt v
  · exact hm a ha

/-- **`bi` leaves bytes.** -/
theorem bi_bytes {b : BI} {as : List Nat} {q q' : HQ} {m m' : Nat → Nat} {res : List Nat}
    (hm : ∀ a, a < MSZ → m a < 256) (h : bi b as q m = some (q', m', res)) :
    ∀ a, a < MSZ → m' a < 256 := by
  rcases (bi_facts h).2.2 with ⟨p, xs, rfl⟩ | rfl
  · exact writeBytes_bytes hm p xs
  · exact hm

/-- **The shape of a built-in call.** -/
theorem bi_shape {b : BI} {as : List Nat} {q q' : HQ} {m m' : Nat → Nat} {res : List Nat}
    (h : bi b as q m = some (q', m', res)) :
    as.length = arity b ∧ ((∃ r, res = [r]) ∧ (b = .streamRead ∨ b = .streamWrite) ∨
      res = [] ∧ (b = .dropR ∨ b = .dropW)) :=
  ⟨(bi_facts h).1, (bi_facts h).2.1⟩

/-! ## Core memory as bytes -/

theorem memOf_agree {mi : MemInst} {m : Nat → Nat} (hs : mi.bytes.size = MSZ)
    (hb : ∀ a (h : a < mi.bytes.size), (mi.bytes[a]'h).toNat = m a) :
    ∀ a, a < MSZ → memOf mi a = m a := by
  intro a ha
  have ha' : a < mi.bytes.size := by omega
  simp only [memOf, ha', ↓reduceDIte]
  exact hb a ha'

theorem encMem_size (sz : Nat) (m : Nat → Nat) : (encMem sz m).size = sz := by
  simp [encMem, ByteArray.size]

theorem encMem_get (sz : Nat) (m : Nat → Nat) (a : Nat) (h : a < (encMem sz m).size) :
    ((encMem sz m)[a]'h).toNat = m a % 256 := by
  simp [encMem, ByteArray.getElem_eq_getElem_data]

/-- The memory written back: `MemR` for bytes `m'` that agree with `m₂` below `MSZ`. -/
theorem memR_enc {s : Store H} {F : Frame} {m m' m₂ : Nat → Nat} (h : MemR s F ma m)
    (hlt : ∀ a, a < MSZ → m' a < 256) (hag : ∀ a, a < MSZ → m' a = m₂ a) {mi : MemInst}
    (hmi : s.mems[ma]? = some mi) :
    MemR (s.setMem ma { mi with bytes := encMem mi.bytes.size m₂ }) F ma m' := by
  obtain ⟨mi', h0, h1, hs, -⟩ := h
  rw [hmi] at h1
  cases h1
  refine ⟨{ mi with bytes := encMem mi.bytes.size m₂ }, h0, ?_, ?_, fun a ha => ?_⟩
  · simp [Store.setMem, (List.getElem?_eq_some_iff.mp hmi).1]
  · show (encMem mi.bytes.size m₂).size = MSZ
    rw [encMem_size, hs]
  · have ha' : a < MSZ := by
      have : (encMem mi.bytes.size m₂).size = MSZ := by rw [encMem_size, hs]
      exact this ▸ ha
    show ((encMem mi.bytes.size m₂)[a]'ha).toNat = m' a
    rw [encMem_get, ← hag a ha']
    exact Nat.mod_eq_of_lt (hlt a ha')

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
