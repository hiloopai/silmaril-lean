module

public import Silmaril.X86.Concurrency.Cir.Rc.Defs
public import Silmaril.X86.Concurrency.Cir.Rc.Tv.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Client
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Uniq
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Run
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Na

/-!
# Reference counting on CIR: the Arc specification and its clients

PROVED (standard axioms; proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Rc/`).

## The Arc specification (RustBelt style), under every frame invariant `J`

* `rc_inc_spec` (**clone duplicates a token**): `{tok l j ∗ blank l k} rc_inc {tok l j ∗ tok l k}`;
* `rc_inc_uniq_spec` (**the first clone shares the object**, after `Arc::new`):
  `{uniq l P ∗ blank l j ∗ blank l k} rc_inc {tok l j ∗ tok l k}`;
* `rc_drop_spec` (**drop consumes one**; **the last drop regains full ownership**): from
  `tok l k` and a frame, `rc_drop` either ends on the slot's blank (not the last reference) or
  runs the cold path on the blank, the count cell `l ↦ 0` and the payload `P`, with no token of
  the object left in the frame;
* `rc_drop_keep`: while another token is held, the drop is not the last and the cold path does
  not run;
* `rc_load_spec`: a token gives atomic read access to a payload cell whose value `P` fixes;
* counting laws: `tok_excl` (a slot's token is exclusive), `tok_live` (a token keeps the count
  positive and the payload in the invariant), `two_toks` (two tokens: count at least `2`).

## The binary

* `drop_binary_spec`: the CIR program that the pinned `rc_drop` bytes validate into
  (`Tv.drop_refines`) meets `rc_drop_spec` (its address is `[rdi]`, its scratch register
  `r11`).

## The `Drop2` client, for every allocator

* `drop2_certified`: the CSL certificate (`GInv`) of the start, for **every** `A : Alloc` whose
  heaps are away from the client's cells;
* `drop2_buffered` (**the last drop frees safely**): every finished, drained state of the TSO and
  XL store-buffer machines has `42` in both output cells: the payload was read while shared, and
  only after both threads were done with it was it overwritten and freed;
* `drop2_no_race` (**concurrent drops are race-free**): no SC-reachable state has a race; in
  particular the last dropper's non-atomic write of the payload never races with the other
  thread's read;
* `drop2_leak`: the same for the leaking allocator `leakAlloc` (the hypotheses are satisfiable).

## The ghost cells are erasable

The ledger's ghost cells (at addresses `≥ 2^64`) sit in the start's memory, since `GInv` asks
owned heaps to be contained in memory. `oreach_mono` (the store-buffer machines are monotone
in memory) transfers the client results to the physical start `Rc.startPhys` (memory
restricted below `2^64`): `drop2_phys` (TSO/XL, `42` in both outputs) and `drop2_no_race_phys`.
`drop2_finishes` is an explicit TSO run from the physical start (leaking allocator) to a
finished, drained state, so the conclusions of `drop2_phys`/`drop2_buffered` are not vacuous.

## Plain payload reads

`drop2Na` proves `Task.drop2Na` (outputs `42` with an `na` payload load, on TSO and XL): the
store-buffer machines ignore a load's mode, so each run of the `na` variant is a run of `Drop2`
with the same memory and buffers. What stays open is the *CSL* treatment of `na` sharing
(a certificate and `no_race` for the `na` variant); `Race` counts two `na` reads as a race,
so that needs fractional permissions and a changed `Race`, not just a proof.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## The Arc specification -/

/-- **Clone duplicates a token.** -/
theorem rc_inc_spec {P J : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hh : (tok l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P ∗ J) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.rc_inc_spec ha hh

/-- **Drop consumes one token; the last drop regains full ownership.** -/
theorem rc_drop_spec {P J : HProp} {Q : Regs → HProp} {l k : Nat} {d : Reg} {a : Expr}
    {slow : Stmt} {rs : Regs} {T : Heap} (ha : (a.eval rs).toNat = l) (hk : k < M)
    (dT : Heap.Disjoint T (Heap.single (gA l k) 0))
    (hslow : ∀ rs' hP, rs' d = 1 → P hP → (∀ j < M, j ≠ k → T (gA l j) = none) →
      Heap.Disjoint (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP) →
      Heap.Disjoint (Heap.single l 0) hP →
      Csl.Safe (rcInv l P ∗ J) Q slow rs'
        (Heap.union (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP)))
    (hfast : ∀ rs', Q rs' (Heap.union T (Heap.single (gB l k) 0))) :
    Csl.Safe (rcInv l P ∗ J) Q (rcDrop d a slow) rs (Heap.union T (Heap.single (gA l k) 0)) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.rc_drop_spec ha hk dT hslow hfast

/-- **The first clone shares a uniquely owned object** (`Arc::new`, then `clone`): the count,
the payload and two slots move into the invariant at the locked add. -/
theorem rc_inc_uniq_spec {P J : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hjk : j ≠ k) (hh : (uniq l P ∗ blank l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P ∗ J) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.rc_inc_uniq_spec ha hjk hh

/-- **Not the last reference** while another token is held. -/
theorem rc_drop_keep {P J : HProp} {Q : Regs → HProp} {l j k : Nat} {d : Reg} {a : Expr}
    {slow : Stmt} {rs : Regs} {T : Heap} (ha : (a.eval rs).toNat = l) (hk : k < M) (hj : j < M)
    (hjk : j ≠ k) (hTj : T (gA l j) = some 0) (dT : Heap.Disjoint T (Heap.single (gA l k) 0))
    (hfast : ∀ rs', Q rs' (Heap.union T (Heap.single (gB l k) 0))) :
    Csl.Safe (rcInv l P ∗ J) Q (rcDrop d a slow) rs (Heap.union T (Heap.single (gA l k) 0)) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.rc_drop_keep ha hk hj hjk hTj dT hfast

/-- **A token gives atomic read access to the payload.** -/
theorem rc_load_spec {P J : HProp} {Q : Regs → HProp} {l k c v0 : Nat} {d : Reg} {m : Mode}
    {sz : Nat} {fl : Flav} {a : Expr} {rs : Regs} {h : Heap} (hm : m ≠ .na)
    (hc : (a.eval rs).toNat = c) (hl : l < gbase) (hk : k < M) (hT : (h (gA l k)).isSome)
    (hPc : ∀ hP, P hP → hP c = some v0) (hq : Q (rs.set d (BitVec.ofNat 64 v0)) h) :
    Csl.Safe (rcInv l P ∗ J) Q (.load d m sz fl a) rs h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.rc_load_spec hm hc hl hk hT hPc hq

/-- `isLast` (the zero flag of `lock sub [a], 1`) holds exactly on an old count of `1`. -/
theorem isLast_iff {rs : Regs} {d : Reg} {old : Nat} (hd : rs d = BitVec.ofNat 64 old)
    (hlt : old < 2 ^ 32) : truthy ((isLast d).eval rs) = true ↔ old = 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.isLast_iff hd hlt

/-! ## Counting laws -/

theorem tok_excl (l k : Nat) (h : Heap) : ¬ (tok l k ∗ tok l k) h :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.tok_excl l k h

theorem tok_live {P : HProp} {l : Nat} {h : Heap} (hl : l < gbase) (H : (rcInv l P ∗ Tok l) h) :
    ∃ c, 1 ≤ c ∧ h l = some c :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.tok_live hl H

theorem two_toks {P : HProp} {l j k : Nat} {h : Heap} (hl : l < gbase) (hjk : j ≠ k)
    (H : (rcInv l P ∗ tok l j ∗ tok l k) h) : ∃ c, 2 ≤ c ∧ h l = some c :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.two_toks hl hjk H

/-! ## From the binary -/

/-- **The validated `rc_drop` meets the drop spec**: the CIR program of the pinned bytes
(`Tv.drop_refines`), at `rdi = l`, is safe from a token under every frame invariant, with the
cold path on the last reference. -/
theorem drop_binary_spec {P J : HProp} {Q : Regs → HProp} {l k : Nat} {slow : Stmt} {rs : Regs}
    {T : Heap} (hl : (rs .rdi).toNat = l) (hk : k < M)
    (dT : Heap.Disjoint T (Heap.single (gA l k) 0))
    (hslow : ∀ rs' hP, rs' Tv.scratch = 1 → P hP → (∀ j < M, j ≠ k → T (gA l j) = none) →
      Heap.Disjoint (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP) →
      Heap.Disjoint (Heap.single l 0) hP →
      Csl.Safe (rcInv l P ∗ J) Q slow rs'
        (Heap.union (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP)))
    (hfast : ∀ rs', Q rs' (Heap.union T (Heap.single (gB l k) 0))) :
    Csl.Safe (rcInv l P ∗ J) Q (Tv.dropCert.body slow) rs (Heap.union T (Heap.single (gA l k) 0))
    := by
  rw [(Tv.bodies slow).2.1]
  refine rc_drop_spec ?_ hk dT hslow hfast
  simp [Tv.atRdi, Expr.eval, BinOp.eval, hl]

/-! ## The `Drop2` client -/

/-- **The CSL certificate of `Drop2`**, for every allocator. -/
theorem drop2_certified (A : Alloc) {hmm hblk : Heap} (haw : Drop2.AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk Drop2.l hblk) :
    GInv (Drop2.inv A) Drop2.post 2 (Drop2.start A hmm hblk) Drop2.own (Drop2.ownI hmm hblk) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.drop2_certified A haw hm hb

/-- **The last drop frees safely**, under TSO and XL: every finished, drained state holds `42`
in both output cells. -/
theorem drop2_buffered (A : Alloc) {hmm hblk : Heap} (haw : Drop2.AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk Drop2.l hblk) {Mo : OModel} {C : OCfg}
    (h : OReach Mo 2 (Drop2.start A hmm hblk).toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : ∀ t < 2, C.mem (Drop2.out t) = some 42 := by
  obtain ⟨hs', hI', hq, -, -, -, hle, -⟩ := csl_buffered (drop2_certified A haw hm hb) h hd hfin
  intro t ht
  exact hle t _ _ (Silmaril.Proofs.X86.Concurrency.Cir.Rc.post_out ht (hq t ht))

/-- **Concurrent drops are race-free**: no SC-reachable state of `Drop2` has a race. -/
theorem drop2_no_race (A : Alloc) {hmm hblk : Heap} (haw : Drop2.AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk Drop2.l hblk) {C : Cfg}
    (h : ScReach 2 (Drop2.start A hmm hblk) C) : ¬ Race 2 C :=
  no_race (drop2_certified A haw hm hb) h

/-- **The hypotheses are satisfiable**: with the leaking allocator and empty allocator heaps,
every finished, drained TSO/XL state of `Drop2` has `42` in both output cells. -/
theorem drop2_leak {Mo : OModel} {C : OCfg}
    (h : OReach Mo 2 (Drop2.start leakAlloc Heap.empty Heap.empty).toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : ∀ t < 2, C.mem (Drop2.out t) = some 42 :=
  drop2_buffered leakAlloc ⟨fun _ => Or.inl rfl, fun x hx => by simp [Heap.empty] at hx⟩
    trivial rfl h hd hfin

/-! ## Without the ghost cells -/

/-- **The store-buffer machines are monotone in memory**: a run from `C.mem` is a run, with
the same threads and buffers, from every extension of it, and the extension is kept. -/
theorem oreach_mono {Mo : OModel} {N : Nat} {C C' : OCfg} (hr : OReach Mo N C C') {m : Heap}
    (hle : Heap.Le C.mem m) :
    ∃ m', OReach Mo N ⟨C.ts, m, C.buf⟩ ⟨C'.ts, m', C'.buf⟩ ∧ Heap.Le C'.mem m' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.oreach_mono hr hle

/-- `Drop2` from the physical memory (no ghost cell): the start's memory below `2^64`. -/
abbrev startPhys (A : Alloc) (hmm hblk : Heap) : Cfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.startPhys A hmm hblk

theorem startPhys_mem (A : Alloc) (hmm hblk : Heap) (x : Nat) :
    (startPhys A hmm hblk).mem x = if x < gbase then (Drop2.start A hmm hblk).mem x else none :=
  rfl

/-- **The last drop frees safely, without ghost cells**, on TSO and XL. -/
theorem drop2_phys (A : Alloc) {hmm hblk : Heap} (haw : Drop2.AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk Drop2.l hblk) {Mo : OModel} {C : OCfg}
    (h : OReach Mo 2 (startPhys A hmm hblk).toO C) (hd : C.Drained)
    (hfin : ∀ t < 2, (C.ts t).1 = .skip) : ∀ t < 2, C.mem (Drop2.out t) = some 42 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.drop2_phys A haw hm hb h hd hfin

/-- **Concurrent drops are race-free, without ghost cells.** -/
theorem drop2_no_race_phys (A : Alloc) {hmm hblk : Heap} (haw : Drop2.AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk Drop2.l hblk) {C : Cfg}
    (h : ScReach 2 (startPhys A hmm hblk) C) : ¬ Race 2 C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.drop2_no_race_phys A haw hm hb h

/-- **`Task.drop2Na` holds**: plain (`na`) payload reads change no TSO/XL outcome of
`Drop2`. -/
theorem drop2Na : Task.drop2Na :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.drop2Na

/-- **`Drop2` finishes** (non-vacuity): an explicit TSO run from the physical start with the
leaking allocator to a finished, drained state. -/
theorem drop2_finishes : ∃ C : OCfg,
    OReach .tso 2 (startPhys leakAlloc Heap.empty Heap.empty).toO C ∧ C.Drained ∧
      (∀ t < 2, (C.ts t).1 = .skip) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.drop2_finishes

end Silmaril.X86.Concurrency.Cir.Rc
