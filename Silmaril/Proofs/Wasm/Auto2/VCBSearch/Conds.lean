module

public import Silmaril.Proofs.Wasm.Auto2.VCBSearch.Tree
public import Silmaril.Wasm.Auto2.VCGen.Thms

/-!
# `btree_search` through the VC generator: the conditions

The conditions of `btree_search` against `searchSpecV` (partial correctness, 14 conditions) and
`searchSpecT` (total correctness, 16: the same and the ghost variant twice), and those of
`oba_get` against the `BA` contract `getBASpecV` (2 conditions). Each is a lemma over a node of the
tree for every `t, κ` with `IsBTree B t κ` (`node_facts`), closed with the facts of
`Silmaril.Proofs.Wasm.Auto2.VCBSearch.Tree`; the dispatch is the tactic `search_vc`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBSearch

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA OBAnd BA FindsAt Tree Repr Ordered Within InTree IsBTree page
  int32Max)

theorem ldW_wd (B : ByteArray) (a : Nat) : ldW 32 4 .unsigned B a = wd B a := by
  simp [ldW, rd, wd]

/-! ## Nodes -/

/-- The node at page `x`, for one `t, κ`. -/
theorem node_facts {B : ByteArray} {k x : BitVec 32} (hsub : SubTree B k x) {t : Nat}
    {κ : BitVec 32 → Prop} (hb : IsBTree B t κ) :
    ∃ l ks cs lo hi, Repr B x.toNat (.node l ks cs) ∧ Ordered lo hi (.node l ks cs) ∧
      Within lo hi k ∧ (κ k ↔ InTree k (.node l ks cs)) ∧ OBAnd B (page * x.toNat + 4) 8090 ks ∧
      (l = true ↔ wd B (page * x.toNat) ≠ 0) ∧ (l = true → cs = []) := by
  obtain ⟨T, lo, hi, hr, ho, hw, hk⟩ := hsub t κ hb
  obtain ⟨l, ks, cs, rfl, hks, hl, hleaf, -⟩ := repr_parts hr
  exact ⟨l, ks, cs, lo, hi, hr, ho, hw, hk, hks, hl, hleaf⟩

/-- The addresses of a node's page do not wrap. -/
theorem addrs {B : ByteArray} {x : BitVec 32} {ks : List (BitVec 32)}
    (h : OBAnd B (page * x.toNat + 4) 8090 ks) :
    (x * 65536#32).toNat = page * x.toNat ∧ (x * 65536#32 + 4#32).toNat = page * x.toNat + 4 ∧
      (x * 65536#32 + 32768#32).toNat = page * x.toNat + 32768 := by
  have hb := (page_bound h).1
  simp only [page, int32Max] at hb ⊢
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

/-- Some `t, κ` with `IsBTree`. -/
theorem ex7 {B : ByteArray} {k : BitVec 32} (h : searchFns.pr 7 B [k]) : ∃ t κ, IsBTree B t κ := h

theorem ex10 {B : ByteArray} {k : BitVec 32} (h : searchFns.pr 10 B [k]) :
    ∃ t κ, IsBTree B t κ := h.1

theorem sub8 {B : ByteArray} {k x : BitVec 32} (h : searchFns.pr 8 B [k, x]) : SubTree B k x := h

theorem sub11 {B : ByteArray} {k x : BitVec 32} (h : searchFns.pr 11 B [k, x]) : SubTree B k x :=
  h.1

/-! ## The root -/

theorem c_bound4 {B : ByteArray} (hb : ∃ t κ, IsBTree B t κ) : (4#32).toNat + 4 ≤ B.size := by
  obtain ⟨t, κ, -, -, -, T, d, hr, -⟩ := hb
  obtain ⟨l, ks, cs, rfl, hks, -⟩ := repr_parts hr
  have := (page_bound hks).2
  simp only [BitVec.toNat_ofNat]
  omega

theorem c_entry {B : ByteArray} {k : BitVec 32} :
    SubTree B k (ldW 32 4 .unsigned B ((4#32).toNat + 0)) := by
  intro t κ hb
  obtain ⟨-, -, -, T, d, hr, ho, -, hk⟩ := hb
  rw [ldW_wd]
  exact ⟨T, none, none, by simpa using hr, ho, ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩,
    (hk k).symm⟩

theorem c_entry8 {B : ByteArray} {k : BitVec 32} :
    searchFns.pr 8 B [k, ldW 32 4 .unsigned B ((4#32).toNat + 0)] := c_entry

theorem c_entry11 {B : ByteArray} {k : BitVec 32} (h : searchFns.pr 10 B [k]) :
    searchFns.pr 11 B [k, ldW 32 4 .unsigned B ((4#32).toNat + 0)] :=
  ⟨c_entry, by rw [ldW_wd]; simpa using h.2⟩

/-! ## The keys -/

theorem c_find_pre {B : ByteArray} {k x : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ) : searchFns.pr 4 B [x * 65536#32 + 4#32, k] := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨l, ks, cs, lo, hi, -, -, -, -, hks, -⟩ := node_facts hsub hb
  show ∃ n α, OBA B (x * 65536#32 + 4#32).toNat n α
  rw [(addrs hks).2.1]
  exact ⟨8090, ks, hks.1⟩

theorem c_keys_bound {B : ByteArray} {k x : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ) : (x * 65536#32 + 4#32).toNat + 4 ≤ B.size := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨l, ks, cs, lo, hi, -, -, -, -, hks, -⟩ := node_facts hsub hb
  rw [(addrs hks).2.1]
  have := (page_bound hks).2
  omega

theorem c_leaf_bound {B : ByteArray} {k x : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ) : (x * 65536#32).toNat + 4 ≤ B.size := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨l, ks, cs, lo, hi, -, -, -, -, hks, -⟩ := node_facts hsub hb
  rw [(addrs hks).1]
  have := (page_bound hks).2
  omega

/-- The length word of the keys is their number. -/
theorem keys_len {B : ByteArray} {x : BitVec 32} {ks : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks) :
    (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat = ks.length := by
  rw [Nat.add_zero, ldW_wd, (addrs hks).2.1]
  exact oba_len hks.1

theorem c_get_keys {B : ByteArray} {k x i : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ)
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat) :
    searchFns.pr 5 B [x * 65536#32 + 4#32, i] := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨l, ks, cs, lo, hi', -, -, -, -, hks, -⟩ := node_facts hsub hb
  show ∃ n α, BA B (x * 65536#32 + 4#32).toNat n α ∧ i.toNat < α.length
  rw [(addrs hks).2.1]
  exact ⟨8090, ks, hks.1.1, by rw [← keys_len hks]; exact hi⟩

/-- The found index of one node's keys. -/
theorem found {B : ByteArray} {k x i : BitVec 32} {ks : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks)
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i]) : FindsAt ks k i.toNat := by
  have h : ∀ n α, OBA B (x * 65536#32 + 4#32).toNat n α → FindsAt α k i.toNat := hfind
  rw [(addrs hks).2.1] at h
  exact h _ _ hks.1

/-- The key at the found index, as read by `oba_get`. -/
theorem got {B : ByteArray} {x i r : BitVec 32} {ks : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks)
    (hget : searchFns.pr 6 B [x * 65536#32 + 4#32, i, r])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat) :
    r = ks.getD i.toNat 0 := by
  have h : ∀ n α, BA B (x * 65536#32 + 4#32).toNat n α → i.toNat < α.length →
      r = α.getD i.toNat 0 := hget
  rw [(addrs hks).2.1] at h
  exact h _ _ hks.1.1 (by rw [← keys_len hks]; exact hi)

/-! ## Results -/

theorem c_ret1 {B : ByteArray} {k x i : BitVec 32} (hsub : SubTree B k x)
    (_hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget : searchFns.pr 6 B [x * 65536#32 + 4#32, i, k])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat) :
    searchFns.pr 9 B [k, 1#32] ∧ B = B := by
  refine ⟨fun t κ hb => ⟨fun _ => rfl, fun hn => absurd ?_ hn⟩, rfl⟩
  obtain ⟨l, ks, cs, lo, hi', -, -, -, hk, hks, -⟩ := node_facts hsub hb
  have hr := got hks hget hi
  have hlen := keys_len hks
  refine hk.mpr (.here ?_)
  rw [hr, getD_eq (by omega)]
  exact List.getElem_mem _

/-- The key is not among a node's keys on the paths that do not return `1`. -/
theorem not_found {B : ByteArray} {k x i : BitVec 32} {ks : List (BitVec 32)} {lo hi : Option (BitVec 32)}
    {l : Bool} {cs : List Tree} (hks : OBAnd B (page * x.toNat + 4) 8090 ks)
    (ho : Ordered lo hi (.node l ks cs))
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hne : i.toNat < ks.length → ks.getD i.toNat 0 ≠ k) : k ∉ ks := by
  cases ho with
  | mk hs _ _ _ => exact notin_keys hs (found hks hfind) hne

/-- `hne` on the path where the read key differs. -/
theorem hne_a {B : ByteArray} {k x i r : BitVec 32} {ks : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks)
    (hget : searchFns.pr 6 B [x * 65536#32 + 4#32, i, r])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hrk : ¬r = k) : i.toNat < ks.length → ks.getD i.toNat 0 ≠ k := by
  intro _ h
  exact hrk ((got hks hget hi).trans h)

/-- `hne` on the path where the index is past the keys. -/
theorem hne_b {B : ByteArray} {k x i : BitVec 32} {ks : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks)
    (hi : ¬i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat) :
    i.toNat < ks.length → ks.getD i.toNat 0 ≠ k := by
  intro h
  rw [keys_len hks] at hi
  exact absurd h hi

/-- **A leaf without the key**: the result `0`. -/
theorem ret0 {B : ByteArray} {k x i : BitVec 32} (hsub : SubTree B k x)
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hne : ∀ ks : List (BitVec 32), OBAnd B (page * x.toNat + 4) 8090 ks →
      i.toNat < ks.length → ks.getD i.toNat 0 ≠ k)
    (hleaf : ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 9 B [k, 0#32] ∧ B = B := by
  refine ⟨fun t κ hb => ⟨fun hk' => absurd ?_ (fun h => h), fun _ => rfl⟩, rfl⟩
  obtain ⟨l, ks, cs, lo, hi, -, ho, -, hk, hks, hl, hcs⟩ := node_facts hsub hb
  rw [Nat.add_zero, ldW_wd, (addrs hks).1] at hleaf
  obtain rfl := hl.mpr hleaf
  obtain rfl := hcs rfl
  have hn := not_found hks ho hfind (hne ks hks)
  exfalso
  cases hk.mp hk' with
  | here h => exact hn h
  | child h _ => simp at h

theorem c_ret0a {B : ByteArray} {k x i r : BitVec 32} (hsub : SubTree B k x)
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget : searchFns.pr 6 B [x * 65536#32 + 4#32, i, r])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hrk : ¬r = k) (hleaf : ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 9 B [k, 0#32] ∧ B = B :=
  ret0 hsub hfind (fun _ hks => hne_a hks hget hi hrk) hleaf

theorem c_ret0b {B : ByteArray} {k x i : BitVec 32} (hsub : SubTree B k x)
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hi : ¬i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hleaf : ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 9 B [k, 0#32] ∧ B = B :=
  ret0 hsub hfind (fun _ hks => hne_b hks hi) hleaf

/-! ## The descent -/

/-- The inner node's facts, for one `t, κ`. -/
theorem inner_facts {B : ByteArray} {k x : BitVec 32} (hsub : SubTree B k x) {t : Nat}
    {κ : BitVec 32 → Prop} (hb : IsBTree B t κ)
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    ∃ ks cs ps lo hi, Repr B x.toNat (.node false ks cs) ∧ Ordered lo hi (.node false ks cs) ∧
      Within lo hi k ∧ (κ k ↔ InTree k (.node false ks cs)) ∧
      OBAnd B (page * x.toNat + 4) 8090 ks ∧ BA B (page * x.toNat + 32768) 8091 ps ∧
      ps.length = cs.length ∧ wd B (page * x.toNat) = 0 := by
  obtain ⟨l, ks, cs, lo, hi, hr, ho, hw, hk, hks, hl, -⟩ := node_facts hsub hb
  rw [Nat.add_zero, ldW_wd, (addrs hks).1] at hleaf
  have hl' : l = false := by
    cases l
    · rfl
    · exact absurd (hl.mp rfl) hleaf
  subst hl'
  obtain ⟨-, -, -, -, -, -, -, hinner⟩ := repr_parts hr
  obtain ⟨l', ks', cs', he, -, -, -, hinner⟩ := repr_parts hr
  simp only [Tree.node.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨ps, hp, hpl, -⟩ := hinner rfl
  exact ⟨ks, cs, ps, lo, hi, hr, ho, hw, hk, hks, hp, hpl, by simpa using hleaf⟩

theorem get_ptrs {k i : BitVec 32} {ks ps : List (BitVec 32)} {cs : List Tree}
    {lo hi : Option (BitVec 32)}
    (ho : Ordered lo hi (.node false ks cs)) (hpl : ps.length = cs.length)
    (hf : FindsAt ks k i.toNat) : i.toNat < ps.length := by
  cases ho with
  | mk _ _ hlen _ =>
    have := hlen rfl
    have := hf.1
    omega

/-- The pointer read: the precondition of `oba_get` on the child pointers. -/
theorem ptr_pre {B : ByteArray} {k x i : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ) (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 5 B [x * 65536#32 + 32768#32, i] := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨ks, cs, ps, lo, hi, -, ho, -, -, hks, hp, hpl, -⟩ := inner_facts hsub hb hleaf
  show ∃ n α, BA B (x * 65536#32 + 32768#32).toNat n α ∧ i.toNat < α.length
  rw [(addrs hks).2.2]
  exact ⟨8091, ps, hp, get_ptrs ho hpl (found hks hfind)⟩

/-- The child page read by `oba_get`. -/
theorem got_ptr {B : ByteArray} {x i x' : BitVec 32} {ks ps : List (BitVec 32)}
    (hks : OBAnd B (page * x.toNat + 4) 8090 ks) (hp : BA B (page * x.toNat + 32768) 8091 ps)
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x']) (hi : i.toNat < ps.length) :
    x' = ps.getD i.toNat 0 := by
  have h : ∀ n α, BA B (x * 65536#32 + 32768#32).toNat n α → i.toNat < α.length →
      x' = α.getD i.toNat 0 := hget
  rw [(addrs hks).2.2] at h
  exact h _ _ hp hi

/-- **The descent keeps the invariant.** -/
theorem descend {B : ByteArray} {k x i x' : BitVec 32} (hsub : SubTree B k x)
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hne : ∀ ks : List (BitVec 32), OBAnd B (page * x.toNat + 4) 8090 ks →
      i.toNat < ks.length → ks.getD i.toNat 0 ≠ k)
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) : SubTree B k x' := by
  intro t κ hb
  obtain ⟨ks, cs, ps, lo, hi, hr, ho, hw, hk, hks, hp, hpl, -⟩ := inner_facts hsub hb hleaf
  have hf := found hks hfind
  have hip := get_ptrs ho hpl hf
  obtain ⟨hic, hiff⟩ := inTree_child hr ho hf (hne ks hks)
  obtain ⟨l', ks', cs', he, -, -, -, hinner⟩ := repr_parts hr
  simp only [Tree.node.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨ps', hp', -, hpr⟩ := hinner rfl
  obtain rfl : ps = ps' := ba_unique hp hp'
  have hx' := got_ptr hks hp hget hip
  rw [getD_eq hip] at hx'
  subst hx'
  cases ho with
  | mk hs hw' hlen hch =>
    exact ⟨cs[i.toNat], loOf lo ks i.toNat, hiOf hi ks i.toNat, hpr _ hip hic, hch _ hic,
      within_found hw hf (hne ks hks), hk.trans hiff⟩

/-- **The ghost height decreases** at the descent. -/
theorem descend_hgt {B : ByteArray} {k x i x' : BitVec 32} (hsub : SubTree B k x)
    (hb : ∃ t κ, IsBTree B t κ) (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    hgt B x'.toNat < hgt B x.toNat := by
  obtain ⟨t, κ, hb⟩ := hb
  obtain ⟨ks, cs, ps, lo, hi, hr, ho, -, -, hks, hp, hpl, hwd⟩ := inner_facts hsub hb hleaf
  have hip := get_ptrs ho hpl (found hks hfind)
  have hx' := got_ptr hks hp hget hip
  rw [getD_eq hip] at hx'
  subst hx'
  exact hgt_child hr hwd hp hip

theorem c_step8a {B : ByteArray} {k x i r x' : BitVec 32} (hsub : searchFns.pr 8 B [k, x])
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget₁ : searchFns.pr 6 B [x * 65536#32 + 4#32, i, r])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hrk : ¬r = k) (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 8 B [k, x'] ∧ B = B :=
  ⟨descend hsub hfind (fun _ hks => hne_a hks hget₁ hi hrk) hget hleaf, rfl⟩

theorem c_step8b {B : ByteArray} {k x i x' : BitVec 32} (hsub : searchFns.pr 8 B [k, x])
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hi : ¬i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 8 B [k, x'] ∧ B = B :=
  ⟨descend hsub hfind (fun _ hks => hne_b hks hi) hget hleaf, rfl⟩

theorem c_step11a {B : ByteArray} {k x i r x' : BitVec 32} (hsub : searchFns.pr 11 B [k, x])
    (hpre : searchFns.pr 10 B [k])
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget₁ : searchFns.pr 6 B [x * 65536#32 + 4#32, i, r])
    (hi : i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hrk : ¬r = k) (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 11 B [k, x'] ∧ B = B :=
  ⟨⟨descend hsub.1 hfind (fun _ hks => hne_a hks hget₁ hi hrk) hget hleaf,
    lt_trans (descend_hgt hsub.1 hpre.1 hfind hget hleaf) hsub.2⟩, rfl⟩

theorem c_step11b {B : ByteArray} {k x i x' : BitVec 32} (hsub : searchFns.pr 11 B [k, x])
    (hpre : searchFns.pr 10 B [k])
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hi : ¬i.toNat < (ldW 32 4 .unsigned B ((x * 65536#32 + 4#32).toNat + 0)).toNat)
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    searchFns.pr 11 B [k, x'] ∧ B = B :=
  ⟨⟨descend hsub.1 hfind (fun _ hks => hne_b hks hi) hget hleaf,
    lt_trans (descend_hgt hsub.1 hpre.1 hfind hget hleaf) hsub.2⟩, rfl⟩

theorem c_var {B : ByteArray} {k x i x' : BitVec 32} (hsub : searchFns.pr 11 B [k, x])
    (hpre : searchFns.pr 10 B [k])
    (hfind : searchFns.pr 3 B [x * 65536#32 + 4#32, k, i])
    (hget : searchFns.pr 6 B [x * 65536#32 + 32768#32, i, x'])
    (hleaf : ¬ldW 32 4 .unsigned B ((x * 65536#32).toNat + 0) ≠ 0) :
    (searchFns.mf 0 B x' 0#32).toNat < (searchFns.mf 0 B x 0#32).toNat := by
  have hd := descend_hgt hsub.1 hpre.1 hfind hget hleaf
  have hx := hsub.2
  show (BitVec.ofNat 32 (hgt B x'.toNat)).toNat < (BitVec.ofNat 32 (hgt B x.toNat)).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hx]
  exact hd

/-! ## `oba_get` on a bounded array -/

theorem g_bound {M0 : ByteArray} {x i : BitVec 32} (h : searchFns.pr 5 M0 [x, i]) :
    (x + i * 4#32).toNat + 8 ≤ M0.size := by
  obtain ⟨n, α, ⟨-, -, hn, hx, hb⟩, hi⟩ := h
  simp only [int32Max] at hx
  have : (x + i * 4#32).toNat = x.toNat + 4 * i.toNat := by bv_omega
  omega

theorem g_post {M0 : ByteArray} {x i : BitVec 32} (_h : searchFns.pr 5 M0 [x, i]) :
    searchFns.pr 6 M0 [x, i, ldW 32 4 .unsigned M0 ((x + i * 4#32).toNat + 4)] := by
  intro n α hba hi
  obtain ⟨-, hw, hn, hx, -⟩ := hba
  simp only [int32Max] at hx
  have ha : (x + i * 4#32).toNat = x.toNat + 4 * i.toNat := by bv_omega
  rw [ldW_wd, ha, show x.toNat + 4 * i.toNat + 4 = x.toNat + 4 + 4 * i.toNat by omega,
    ← getD_words hi, hw]

set_option maxRecDepth 100000 in
/-- **The conditions of `oba_get` against the `BA` contract.** -/
theorem getBA_vcs :
    AllValid searchFns (genFunc getBASpecV Silmaril.WasmSpec.BTree.getFunc searchFuel) := by
  vcgen4
  · exact fun h => g_bound h
  · exact fun h => g_post h

/-- Close one computed condition of `btree_search` (after `vcgen4`). -/
macro "search_vc" : tactic => `(tactic| (
  try simp only [and_imp]
  intros
  subst_vars
  try dsimp only [Silmaril.Wasm.IntType.width] at *
  first
  | with_reducible exact c_bound4 (ex7 ‹_›)
  | with_reducible exact c_bound4 (ex10 ‹_›)
  | with_reducible exact c_entry8
  | with_reducible exact c_entry11 ‹_›
  | with_reducible exact c_find_pre (sub8 ‹_›) (ex7 ‹_›)
  | with_reducible exact c_find_pre (sub11 ‹_›) (ex10 ‹_›)
  | with_reducible exact c_keys_bound (sub8 ‹_›) (ex7 ‹_›)
  | with_reducible exact c_keys_bound (sub11 ‹_›) (ex10 ‹_›)
  | with_reducible exact c_leaf_bound (sub8 ‹_›) (ex7 ‹_›)
  | with_reducible exact c_leaf_bound (sub11 ‹_›) (ex10 ‹_›)
  | with_reducible exact c_get_keys (sub8 ‹_›) (ex7 ‹_›) ‹_›
  | with_reducible exact c_get_keys (sub11 ‹_›) (ex10 ‹_›) ‹_›
  | with_reducible exact c_ret1 (sub8 ‹_›) ‹_› ‹_› ‹_›
  | with_reducible exact c_ret1 (sub11 ‹_›) ‹_› ‹_› ‹_›
  | with_reducible exact c_ret0a (sub8 ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_ret0a (sub11 ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_ret0b (sub8 ‹_›) ‹_› ‹_› ‹_›
  | with_reducible exact c_ret0b (sub11 ‹_›) ‹_› ‹_› ‹_›
  | with_reducible exact ptr_pre (sub8 ‹_›) (ex7 ‹_›) ‹_› ‹_›
  | with_reducible exact ptr_pre (sub11 ‹_›) (ex10 ‹_›) ‹_› ‹_›
  | with_reducible exact c_step8a ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_step8b ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_step11a ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_step11b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | with_reducible exact c_var ‹_› ‹_› ‹_› ‹_› ‹_›))

set_option maxRecDepth 100000 in
/-- **The 14 conditions of `btree_search`, partial correctness.** -/
theorem search_vcs :
    AllValid searchFns (genFunc searchSpecV Silmaril.WasmSpec.BTree.searchFunc searchFuel) := by
  vcgen4
  all_goals search_vc

set_option maxRecDepth 100000 in
/-- **The 16 conditions of `btree_search`, total correctness** (the ghost height decreases at
both descents). -/
theorem search_tvcs :
    AllValid searchFns (genFunc searchSpecT Silmaril.WasmSpec.BTree.searchFunc searchFuel) := by
  vcgen4
  all_goals search_vc

end Silmaril.Wasm.Auto2.VCBSearch
