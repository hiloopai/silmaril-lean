module

public import Silmaril.X86.Loose.Decode.Defs

/-!
# Proofs: decode-table lookup and checks

The header is `Silmaril/X86/Loose/Decode/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Loose

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory ByteMemory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.RelIsa (Views)
open Silmaril.X86.Loose

variable {Φ σ : Type}

theorem find_some {D : DTable Φ} {bytes : List Byte} {e : DEntry Φ}
    (h : D.find bytes = some e) : e ∈ D ∧ e.bytes = bytes ∧ bytes ≠ [] := by
  unfold DTable.find at h
  split at h
  · cases h
  · rename_i hne
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h, hne⟩

theorem lookup_some {D : DTable Φ} {bytes : List Byte} {i : Φ} {l : Nat}
    (h : D.lookup bytes = some (i, l)) :
    ∃ e ∈ D, e.bytes = bytes ∧ e.form = i ∧ l = bytes.length ∧ bytes ≠ [] := by
  unfold DTable.lookup at h
  cases hf : D.find bytes with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    cases h
    obtain ⟨hm, hb, hne⟩ := find_some hf
    exact ⟨e, hm, hb, rfl, rfl, hne⟩

theorem find_isSome_of_mem {D : DTable Φ} {e : DEntry Φ} (hm : e ∈ D)
    (hne : e.bytes ≠ []) : (D.find e.bytes).isSome := by
  unfold DTable.find
  simp only [hne, ↓reduceIte]
  rw [List.find?_isSome]
  exact ⟨e, hm, by simp⟩

/-- `rip = base + o` for an offset inside a loaded image is `base.toNat + o` as a number. -/
theorem rip_toNat_of_loaded {m : Memory} {base : Word} {code : List Byte} {o l : Nat}
    (hL : Loaded m base code) (hfit : o + l ≤ code.length) (hpos : 0 < l) :
    (base + BitVec.ofNat 64 o).toNat = base.toNat + o := by
  have hw := hL.noWrap
  simp only [Silmaril.Process.addressLimit] at hw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- **An entry that is a non-empty slice of a loaded image is at its address.** -/
theorem atEntry_of_loaded {e : DEntry Φ} {c : State} {m : Memory} {base : Word}
    {code : List Byte} {o l : Nat} (hL : Loaded m base code)
    (hrip : c.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length) (hpos : 0 < l)
    (hb : e.bytes = (code.drop o).take l) : AtEntry e c m := by
  have hlen : e.bytes.length = l := by
    rw [hb, List.length_take, List.length_drop]; omega
  unfold AtEntry
  rw [hrip, rip_toNat_of_loaded hL hfit hpos, hlen, hb]
  exact hL.fetchBytes_sub hpos hfit

/-- A shorter backing read is a prefix of a longer one. -/
theorem readBacking_take (b : ByteMemory) : ∀ (n k a : Nat) (l : List Byte),
    Memory.readBacking b a (n + k) = some l → Memory.readBacking b a n = some (l.take n)
  | 0, _, _, _, _ => rfl
  | n + 1, k, a, l, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega] at h
    simp only [Memory.readBacking, Option.bind_eq_bind,
      Std.ExtHashMap.get?_eq_getElem?] at h ⊢
    cases hb : b[a]? with
    | none => simp [hb] at h
    | some x =>
      cases ht : Memory.readBacking b (a + 1) (n + k) with
      | none => simp [hb, ht] at h
      | some tl =>
        simp [hb, ht] at h
        subst h
        simp [readBacking_take b n k (a + 1) tl ht]

/-- A shorter fetch at the same address is a prefix of a longer one. -/
theorem fetchBytes_prefix {m : Memory} {a n k : Nat} {l l' : List Byte}
    (h : m.fetchBytes a n = some l) (h' : m.fetchBytes a (n + k) = some l') :
    l = l'.take n := by
  unfold Memory.fetchBytes Memory.readWith at h h'
  split at h
  · split at h'
    · have := readBacking_take m.bytes n k a l' h'
      rw [this] at h; exact (Option.some.inj h).symm
    · cases h'
  · cases h


/-- **In a prefix-free, functional table, at most one entry is at `rip`** (up to equal bytes
and form). -/
theorem atEntry_unique [DecidableEq Φ] {D : DTable Φ} (hp : D.prefixFree = true)
    (hf : D.functional = true) {e e' : DEntry Φ} (hm : e ∈ D) (hm' : e' ∈ D) {c : State}
    {m : Memory} (h : AtEntry e c m) (h' : AtEntry e' c m) :
    e.bytes = e'.bytes ∧ e.form = e'.form := by
  have hb : e.bytes = e'.bytes := by
    unfold DTable.prefixFree at hp
    rw [Bool.and_eq_true, List.all_eq_true] at hp
    replace hp := hp.2
    rw [List.all_eq_true] at hp
    have h1 := hp e hm; have h2 := hp e' hm'
    rw [List.all_eq_true] at h1 h2
    have h1 := h1 e' hm'; have h2 := h2 e hm
    unfold AtEntry at h h'
    rcases Nat.le_total e.bytes.length e'.bytes.length with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk] at h'
      have := fetchBytes_prefix h h'
      by_contra hne
      have hpre : e.bytes.isPrefixOf e'.bytes = true := by
        rw [List.isPrefixOf_iff_prefix, this]; exact List.take_prefix _ _
      simp [hne, hpre] at h1
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk] at h
      have := fetchBytes_prefix h' h
      by_contra hne
      have hpre : e'.bytes.isPrefixOf e.bytes = true := by
        rw [List.isPrefixOf_iff_prefix, this]; exact List.take_prefix _ _
      simp [Ne.symm hne, hpre] at h2
  refine ⟨hb, ?_⟩
  unfold DTable.functional at hf
  rw [List.all_eq_true] at hf
  have := hf e hm; rw [List.all_eq_true] at this
  have := this e' hm'
  by_contra hne
  simp [hb, hne] at this

/-- Every entry of a table that passes `prefixFree` is non-empty. -/
theorem bytes_ne_nil_of_prefixFree {D : DTable Φ} (hp : D.prefixFree = true)
    {e : DEntry Φ} (hm : e ∈ D) : e.bytes ≠ [] := by
  unfold DTable.prefixFree at hp
  rw [Bool.and_eq_true, List.all_eq_true] at hp
  simpa using hp.1 e hm

end Silmaril.Proofs.X86.Loose
