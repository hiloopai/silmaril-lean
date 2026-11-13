module

public import Silmaril.Proofs.Wasi.Versions.Adapter.Inv
public import Silmaril.Wasi.Versions.P1.Theory.Thms

/-!
# Proofs: the preview1 theory at the adapter's answers, and the descriptor invariant

* `TB n a r`: the answer `r` of `n a` is well typed and within its bounds (`tb_err`, `tb_ok`).
* `FdInv s f`: the descriptors the preview1 theory knows to be open are open in the adapter's
  table, those it knows to be closed are closed, and the free list lists closed entries.
  `fdInv_init`, and its preservation by the table operations (`fdInv_withTable`,
  `fdInv_setD`, `fdInv_touch`, `fdInv_close`, `fdInv_open`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt fdStep fdOk typedOk boundsOk okAns errAns)

/-! ## Typing and bounds of answers -/

/-- The answer `r` of `n a` is well typed and within its bounds. -/
def TB (n : String) (a : List Val) (r : Option (List Val)) : Prop :=
  typedOk (.imp (P1.fn n) a r) = true ∧ boundsOk (.imp (P1.fn n) a r) = true

/-- A valid nonzero `errno`. -/
def ValidErr (e : Nat) : Prop := e ≠ 0 ∧ e < 77

theorem validErr_codeErrno (c : Val) : ValidErr (codeErrno c) := by
  unfold codeErrno
  split
  · rename_i k
    rw [List.getD_eq_getElem?_getD]
    rcases h : P1.Gen.errnoOfCode[k]? with _ | e
    · exact ⟨by decide, by decide⟩
    · have := P1.errnoOfCode_ok e (List.mem_of_getElem? h)
      exact ⟨this.1, P1.counts.2.1 ▸ this.2⟩
  · exact ⟨by decide, by decide⟩

/-- Error answers are well typed and within bounds (for every function but `proc_exit`). -/
theorem tb_err {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") {e : Nat}
    (he : ValidErr e) (a : List Val) : TB n a (errAns e) := by
  have h16 : (BitVec.ofNat 16 e).toNat = e := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := he.2; omega)
  refine ⟨?_, ?_⟩
  · simp only [typedOk, P1.fn, P1.module, hn, and_self, ite_true, P1.ansOk, hx, ite_false,
      errAns, errV, P1.isErrno, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    refine .inl ⟨fun h => he.1 ?_, ?_⟩
    · rw [← h16, h]; rfl
    · rw [h16, P1.counts.2.1]; exact he.2
  · simp only [boundsOk, errAns, errV]
    split_ifs <;> rfl

/-- An `ok` answer of the payload type of `n`, outside the three bounded functions. -/
theorem tb_ok {n : String} (hn : n ∈ P1.fnNames) (hx : n ≠ "proc_exit") {v : Option Val}
    (hv : P1.okShape n v = true) (hb : n ≠ "fd_write" ∧ n ≠ "fd_read" ∧ n ≠ "random_get")
    (a : List Val) : TB n a (okAns v) := by
  refine ⟨?_, ?_⟩
  · simp only [typedOk, P1.fn, P1.module, hn, and_self, ite_true, P1.ansOk, hx, ite_false,
      okAns, okV, P1.isErrno, hv, Bool.or_true]
  · have h1 : P1.fn n ≠ P1.fn "fd_write" := fun h => hb.1 (congrArg FnName.fn h)
    have h2 : P1.fn n ≠ P1.fn "fd_read" := fun h => hb.2.1 (congrArg FnName.fn h)
    have h3 : P1.fn n ≠ P1.fn "random_get" := fun h => hb.2.2 (congrArg FnName.fn h)
    simp only [boundsOk, h1, h2, h3, ite_false]

/-! ## The descriptor invariant -/

/-- An open descriptor of the table. -/
def isOpenD : Desc → Bool
  | .closed => false
  | _ => true

/-- `x` is open in the adapter's state (before the table exists: `0`, `1`, `2`). -/
def IsOpen (s : ASt) (x : BitVec 32) : Prop :=
  match s.table with
  | none => x.toNat < 3
  | some t => isOpenD (getD t x) = true

/-- **The descriptor invariant.** -/
structure FdInv (s : ASt) (f : FdSt) : Prop where
  /-- Known-open descriptors are open. -/
  live : ∀ x ∈ f.live, IsOpen s x
  /-- Known-closed descriptors are closed. -/
  dead : ∀ x ∈ f.dead, ¬ IsOpen s x
  /-- Before the table exists, nothing is closed. -/
  pre : s.table = none → f.dead = [] ∧ s.free = []
  /-- The free list lists distinct closed entries, and the table has at most 128 entries. -/
  free : ∀ t, s.table = some t →
    (∀ y ∈ s.free, y < t.length ∧ isOpenD (t.getD y .closed) = false) ∧ s.free.Nodup ∧
      t.length ≤ maxDescriptors

/-- Initially. -/
theorem fdInv_init : FdInv ASt.init P1.fds.init := by
  refine ⟨?_, fun _ h => absurd h List.not_mem_nil, fun _ => ⟨rfl, rfl⟩, fun _ h => by cases h⟩
  intro x hx
  simp only [P1.fds, List.mem_cons, List.not_mem_nil, or_false] at hx
  show x.toNat < 3
  rcases hx with rfl | rfl | rfl <;> decide

/-! ## Table lemmas -/

theorem getD_set_ne {t : List Desc} {i j : Nat} {d : Desc} (h : j ≠ i) :
    (t.set i d).getD j .closed = t.getD j .closed := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h, ite_false]

theorem getD_set_self {t : List Desc} {i : Nat} {d : Desc} (h : i < t.length) :
    (t.set i d).getD i .closed = d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem lt_of_isOpenD {t : List Desc} {i : Nat} (h : isOpenD (t.getD i .closed) = true) :
    i < t.length := by
  by_contra hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  cases h

theorem isOpen_some {s : ASt} {t : List Desc} (ht : s.table = some t) (x : BitVec 32) :
    IsOpen s x ↔ isOpenD (getD t x) = true := by
  unfold IsOpen; rw [ht]

/-- An open descriptor is not known closed. -/
theorem FdInv.not_dead {s : ASt} {f : FdSt} (h : FdInv s f) {fd : BitVec 32} (ho : IsOpen s fd) :
    fd ∉ f.dead := fun hd => h.dead fd hd ho

/-- A successful operation on `fd` marks it open. -/
def touch (f : FdSt) (fd : BitVec 32) : FdSt := if fd ∈ f.live then f else ⟨fd :: f.live, f.dead⟩

theorem fdInv_touch {s : ASt} {f : FdSt} (h : FdInv s f) {fd : BitVec 32} (ho : IsOpen s fd) :
    FdInv s (touch f fd) := by
  unfold touch
  split_ifs
  · exact h
  · refine ⟨fun x hx => ?_, h.dead, h.pre, h.free⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ho
    · exact h.live x hx

theorem touch_dead (f : FdSt) (fd : BitVec 32) : (touch f fd).dead = f.dead := by
  unfold touch; split_ifs <;> rfl

/-- Replacing an open entry by an open one keeps the invariant. -/
theorem fdInv_setD {s : ASt} {f : FdSt} (h : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {fd : BitVec 32} (ho : isOpenD (getD t fd) = true) {d : Desc} (hd : isOpenD d = true) :
    FdInv (setD s t fd d) f := by
  have hlt : fd.toNat < t.length := lt_of_isOpenD ho
  have hiff : ∀ x, IsOpen (setD s t fd d) x ↔ IsOpen s x := by
    intro x
    rw [isOpen_some ht]
    show isOpenD ((t.set fd.toNat d).getD x.toNat .closed) = true ↔
      isOpenD (t.getD x.toNat .closed) = true
    by_cases hx : x.toNat = fd.toNat
    · rw [hx, getD_set_self hlt]; exact ⟨fun _ => ho, fun _ => hd⟩
    · rw [getD_set_ne hx]
  refine ⟨fun x hx => (hiff x).2 (h.live x hx), fun x hx hx' => h.dead x hx ((hiff x).1 hx'),
    fun hn => absurd hn (by simp [setD]), fun t' ht' => ?_⟩
  simp only [setD, Option.some.injEq] at ht'
  subst ht'
  obtain ⟨hfree, hnd, hlen⟩ := h.free t ht
  refine ⟨fun y hy => ?_, hnd, by simpa [setD] using hlen⟩
  obtain ⟨hy1, hy2⟩ := hfree y hy
  have hne : y ≠ fd.toNat := fun he => by
    rw [he] at hy2; exact absurd ho (by simpa [getD] using hy2)
  exact ⟨by simpa using hy1, by rw [getD_set_ne hne]; exact hy2⟩

theorem toNat_ofNat_of_lt {x : Nat} (hx : x < maxDescriptors) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold maxDescriptors at hx; omega)

theorem getD_append_ne {t : List Desc} {y : Nat} {d : Desc} (hy : y ≠ t.length) :
    (t ++ [d]).getD y .closed = t.getD y .closed := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_eq_none (show t.length ≤ y by omega)]
    simp only [List.getElem?_singleton, show y - t.length ≠ 0 by omega, ite_false]

/-- The table created at the first use satisfies the invariant. -/
theorem fdInv_withTable {s : ASt} {f : FdSt} (h : FdInv s f) (hs : s.table = none)
    {i o e : BitVec 32} {l : List Desc} (hl : l.length ≤ maxPreopens) :
    FdInv ⟨some ([.stdin i, .stdout o, .stderr e] ++ l), s.free⟩ f := by
  obtain ⟨hd, hf⟩ := h.pre hs
  refine ⟨fun x hx => ?_, fun x hx => (by rw [hd] at hx; exact absurd hx List.not_mem_nil),
    (fun hn => nomatch hn), fun t ht => ?_⟩
  · have h3 : x.toNat < 3 := by
      have := h.live x hx; unfold IsOpen at this; rw [hs] at this; exact this
    show isOpenD (getD _ x) = true
    unfold getD
    rcases (by omega : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2) with h0 | h0 | h0 <;>
      simp [h0, isOpenD]
  · simp only [Option.some.injEq] at ht
    subst ht
    rw [hf]
    refine ⟨fun y hy => absurd hy List.not_mem_nil, List.nodup_nil, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil, maxDescriptors]
    unfold maxPreopens at hl; omega

/-- After closing `fd`, the other entries are unchanged. -/
theorem isOpen_close {t : List Desc} {fd x : BitVec 32} (hx : x ≠ fd) :
    isOpenD ((t.set fd.toNat .closed).getD x.toNat .closed) = isOpenD (t.getD x.toNat .closed) := by
  have hxn : x.toNat ≠ fd.toNat := fun he => hx (BitVec.eq_of_toNat_eq he)
  rw [getD_set_ne hxn]

/-- The free list after closing `fd`. -/
theorem free_close {s : ASt} {f : FdSt} (h : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {fd : BitVec 32} (ho : isOpenD (getD t fd) = true) :
    (∀ y ∈ fd.toNat :: s.free, y < (t.set fd.toNat .closed).length ∧
      isOpenD ((t.set fd.toNat .closed).getD y .closed) = false) ∧
      (fd.toNat :: s.free).Nodup ∧ (t.set fd.toNat .closed).length ≤ maxDescriptors := by
  have hlt : fd.toNat < t.length := lt_of_isOpenD ho
  obtain ⟨hfree, hnd, hlen⟩ := h.free t ht
  have hnot : fd.toNat ∉ s.free := fun hm => by
    have hc : isOpenD (t.getD fd.toNat .closed) = false := (hfree _ hm).2
    exact absurd ho (by simp only [getD, hc]; decide)
  refine ⟨fun y hy => ?_, List.nodup_cons.2 ⟨hnot, hnd⟩, by simpa using hlen⟩
  rcases List.mem_cons.1 hy with rfl | hy
  · exact ⟨by simpa using hlt, by rw [getD_set_self hlt]; rfl⟩
  · obtain ⟨hy1, hy2⟩ := hfree y hy
    have hyn : y ≠ fd.toNat := fun he => hnot (he ▸ hy)
    exact ⟨by simpa using hy1, by rw [getD_set_ne hyn]; exact hy2⟩

/-- **Closing** an open descriptor. -/
theorem fdInv_close {s : ASt} {f : FdSt} (h : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {fd : BitVec 32} (ho : isOpenD (getD t fd) = true) :
    FdInv ⟨some (t.set fd.toNat .closed), fd.toNat :: s.free⟩
      ⟨(touch f fd).live.filter (· != fd), fd :: (touch f fd).dead⟩ := by
  have hlt : fd.toNat < t.length := lt_of_isOpenD ho
  have h1 : FdInv s (touch f fd) := fdInv_touch h ((isOpen_some ht fd).2 ho)
  refine ⟨fun x hx => ?_, fun x hx => ?_, (fun hn => nomatch hn), fun t' ht' => ?_⟩
  · obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
    have hne : x ≠ fd := by simpa using hx2
    show isOpenD ((t.set fd.toNat .closed).getD x.toNat .closed) = true
    rw [isOpen_close hne]; exact (isOpen_some ht x).1 (h1.live x hx1)
  · show ¬ isOpenD ((t.set fd.toNat .closed).getD x.toNat .closed) = true
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [getD_set_self hlt]; decide
    · have hxd : ¬ IsOpen s x := h1.dead x hx
      have hne : x ≠ fd := fun he => hxd (he ▸ (isOpen_some ht fd).2 ho)
      rw [isOpen_close hne]; exact fun hxo => hxd ((isOpen_some ht x).2 hxo)
  · have ht'' : t' = t.set fd.toNat .closed := (Option.some.inj ht').symm
    exact ht'' ▸ free_close h ht ho

/-- The new entry of `openDesc`: closed before, `d` after, every other entry unchanged, and the
free list and size bound kept. -/
def OpenSpec (t : List Desc) (d : Desc) (s' : ASt) (x : Nat) : Prop :=
  ∃ t', s'.table = some t' ∧ x < maxDescriptors ∧ isOpenD (t.getD x .closed) = false ∧
    t'.getD x .closed = d ∧ (∀ y, y ≠ x → t'.getD y .closed = t.getD y .closed) ∧
    (∀ y ∈ s'.free, y < t'.length ∧ isOpenD (t'.getD y .closed) = false) ∧ s'.free.Nodup ∧
    t'.length ≤ maxDescriptors

/-- `openDesc` from the free list. -/
theorem openSpec_free {s : ASt} {t : List Desc} (hfree : ∀ y ∈ s.free, y < t.length ∧
      isOpenD (t.getD y .closed) = false) (hnd : s.free.Nodup) (hlen : t.length ≤ maxDescriptors)
    {y : Nat} {rest : List Nat} (hfr : s.free = y :: rest) (d : Desc) :
    OpenSpec t d ⟨some (t.set y d), rest⟩ y := by
  have hy := hfree y (by rw [hfr]; exact List.mem_cons_self)
  have hnd2 : (y :: rest).Nodup := hfr ▸ hnd
  refine ⟨_, rfl, by omega, hy.2, getD_set_self hy.1, fun z hz => getD_set_ne hz,
    fun z hz => ?_, (List.nodup_cons.1 hnd2).2, by simpa using hlen⟩
  have hzy : z ≠ y := fun he => (List.nodup_cons.1 hnd2).1 (he ▸ hz)
  obtain ⟨hz1, hz2⟩ := hfree z (by rw [hfr]; exact List.mem_cons_of_mem _ hz)
  exact ⟨by simpa using hz1, by rw [getD_set_ne hzy]; exact hz2⟩

/-- `openDesc` at the end of the table. -/
theorem openSpec_push {t : List Desc} (hl : t.length < maxDescriptors) (d : Desc) :
    OpenSpec t d ⟨some (t ++ [d]), []⟩ t.length := by
  refine ⟨_, rfl, hl, ?_, ?_, fun z hz => getD_append_ne hz, fun z hz => absurd hz
    List.not_mem_nil, List.nodup_nil, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · simp [List.getD_eq_getElem?_getD]
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem openSpec {s : ASt} {f : FdSt} (h : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {d : Desc} {s' : ASt} {x : Nat} (hopen : openDesc s t d = some (s', x)) :
    OpenSpec t d s' x := by
  obtain ⟨hfree, hnd, hlen⟩ := h.free t ht
  unfold openDesc at hopen
  split at hopen
  · next y rest hfr =>
    have he : (s', x) = (⟨some (t.set y d), rest⟩, y) := (Option.some.inj hopen).symm
    rw [Prod.mk.injEq] at he
    exact he.1 ▸ he.2 ▸ openSpec_free hfree hnd hlen hfr d
  · split_ifs at hopen with hl
    have he : (s', x) = (⟨some (t ++ [d]), []⟩, t.length) := (Option.some.inj hopen).symm
    rw [Prod.mk.injEq] at he
    exact he.1 ▸ he.2 ▸ openSpec_push hl d

/-- **Opening** a descriptor (`Descriptors::open`): it was not open, and the invariant holds
with it marked open. -/
theorem fdInv_open {s : ASt} {f : FdSt} (h : FdInv s f) {t : List Desc} (ht : s.table = some t)
    {dirfd : BitVec 32} (hdir : isOpenD (getD t dirfd) = true) {d : Desc}
    (hd : isOpenD d = true) {s' : ASt} {x : Nat} (hopen : openDesc s t d = some (s', x)) :
    BitVec.ofNat 32 x ∉ (touch f dirfd).live ∧
      FdInv s' ⟨BitVec.ofNat 32 x :: (touch f dirfd).live,
        (touch f dirfd).dead.filter (· != BitVec.ofNat 32 x)⟩ := by
  have h1 := fdInv_touch h ((isOpen_some ht dirfd).2 hdir)
  obtain ⟨t', hs', hxlt, hclosed, hnew, hother, hfree', hnd', hlen'⟩ := openSpec h ht hopen
  have hxn : (BitVec.ofNat 32 x).toNat = x := toNat_ofNat_of_lt hxlt
  have hne : ∀ z, IsOpen s z → z.toNat ≠ x := fun z hz he => by
    have hzo : isOpenD (t.getD z.toNat .closed) = true := (isOpen_some ht z).1 hz
    rw [he, hclosed] at hzo; cases hzo
  have hiff : ∀ z, z.toNat ≠ x → (IsOpen s' z ↔ IsOpen s z) := fun z hz => by
    rw [isOpen_some hs', isOpen_some ht]
    show isOpenD (t'.getD z.toNat .closed) = true ↔ isOpenD (t.getD z.toNat .closed) = true
    rw [hother _ hz]
  refine ⟨fun hm => hne _ (h1.live _ hm) hxn, fun z hz => ?_, fun z hz => ?_,
    fun hn => absurd (hs'.symm.trans hn) (by simp), fun t'' ht'' => ?_⟩
  · rcases List.mem_cons.1 hz with rfl | hz
    · rw [isOpen_some hs']; show isOpenD (t'.getD _ .closed) = true; rw [hxn, hnew]; exact hd
    · exact (hiff z (hne z (h1.live z hz))).2 (h1.live z hz)
  · obtain ⟨hz1, hz2⟩ := List.mem_filter.1 hz
    have hzx : z.toNat ≠ x := fun he => by
      have hzeq : z = BitVec.ofNat 32 x := BitVec.eq_of_toNat_eq (he.trans hxn.symm)
      simp [hzeq] at hz2
    exact fun hzo => h1.dead z hz1 ((hiff z hzx).1 hzo)
  · have htt : t'' = t' := Option.some.inj (ht''.symm.trans hs')
    exact htt ▸ ⟨hfree', hnd', hlen'⟩

end Silmaril.Wasi.Versions.Adapter
