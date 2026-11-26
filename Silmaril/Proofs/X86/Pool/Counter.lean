module

public import Silmaril.Proofs.X86.Pool.Example

/-!
# Proofs: `Task.drfTso` as first stated is false

The first statement of `Task.drfTso` was frozen with a footprint condition (`InFootprint`) that
puts the `k` fetched bytes in the owned and read-only fragments, but an `EvMachine`'s `fetch` is an
arbitrary function of the whole memory. A fetch can therefore read a byte another thread owns and
writes: a data race that no access list shows. `FetchStable` is therefore added to `LSafeEv`;
this file is the counterexample to the statement without it.

* `LSafeEvK`, `OwnershipSafeEvK`, `TaskFetch`: the definitions and statement, verbatim except for
  the names (`LSafeEv` without the `FetchStable` conjunct).
* `M`: a two-instruction machine. `st a` stores the byte `1` at `a` (one `store` event,
  access-local); `set v` writes `v` to `rax` (no event). Its fetch decodes the byte at `17`
  (thread A) as `set (byte 101 is 1)` and the byte at `33` (thread B) as `set (byte 100 is 1)`.
* `poolC`: thread A runs `st 100; set _` from `16`, thread B runs `st 101; set _` from `32`
  (store buffering through the fetch). A owns `rip`, `rax` and byte `100`, B the same with
  byte `101`, and the four code bytes are the read-only context. `ownK` proves the
  hypothesis: the fetched byte is code, and the store writes the owned byte.
* `tso_run`: under TSO both stores are buffered, both `set`s read `0`, then both buffers
  flush: a drained state with `rax = 0` in both threads.
* `sc_inv`: in every SC run, if both threads have finished and A's `rax` is `0`, then B's is
  `1` (whoever runs `set` second sees the other's store).
* `not_taskK : ¬ TaskFetch`.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Pool.Counter

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory Region Permissions)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin readSet writeSet)
open Silmaril.X86.Pool
open Silmaril.Proofs.X86.Pool

/-! ## The first statement -/

/-- The first `LSafeEv`: `LSafeEv` without `FetchStable`. -/
def LSafeEvK (M : EvMachine) (Fin : State → Prop) (Q : SProp) (r : Frag) :
    Nat → State → Frag → Prop
  | 0, _, _ => True
  | n + 1, c, h => ∀ mem : Memory, Le (union h r) (toFrag ⟨c, mem⟩) →
      (Fin c ∧ Q h) ∨
      (¬ Fin c ∧ ∃ i k m', M.fetch mem c.rip.toNat = some (i, k) ∧
        InFootprint h r c.rip.toNat k (M.accesses i c k) ∧
        M.step ⟨c, mem⟩ = some m' ∧ ChangesWithin h ⟨c, mem⟩ m' ∧
        LSafeEvK M Fin Q r n m'.core (reval h (toFrag m')))

/-- The first `OwnershipSafeEv`, over `LSafeEvK`. -/
def OwnershipSafeEvK {Tid : Type} [DecidableEq Tid] (M : EvMachine) (Fin : Tid → State → Prop)
    (p : Pool Tid) : Prop :=
  ∃ (σ : Tid → Frag) (r : Frag) (Q : Tid → SProp),
    SharedOnly r ∧
    (∀ t, p.threads t = none → σ t = Frag.empty) ∧
    (∀ t t', t ≠ t' → PFrag.Disjoint (embed t (σ t)) (embed t' (σ t'))) ∧
    (∀ t, PFrag.Disjoint (embed t (σ t)) (embedS r)) ∧
    (∀ t, PFrag.Le (embed t (σ t)) (poolFrag p)) ∧
    PFrag.Le (embedS r) (poolFrag p) ∧
    ∀ t c, p.threads t = some c → ∀ n, LSafeEvK M (Fin t) (Q t) r n c (σ t)

/-- **`Task.drfTso` as first stated.** -/
def TaskFetch : Prop :=
  ∀ {Tid : Type} [DecidableEq Tid] (M : EvMachine) (Fin : Tid → State → Prop) (p₀ : Pool Tid),
    OwnershipSafeEvK M Fin p₀ →
    ∀ p, TsoReach M Fin (TPool.ofPool p₀) p → Drained p → SCReach M.step Fin p₀ (forget p)

/-! ## The machine -/

/-- Two instructions: store the byte `1`, or set `rax`. -/
inductive Op where
  | st (a : Nat)
  | set (v : Bool)

/-- The fetch: the instruction at `17` (resp. `33`) depends on byte `101` (resp. `100`). -/
def fetchC (mem : Memory) (pc : Nat) : Option (Op × Nat) :=
  if pc = 16 then some (.st 100, 1)
  else if pc = 17 then some (.set (decide (mem.bytes[101]? = some 1)), 1)
  else if pc = 32 then some (.st 101, 1)
  else if pc = 33 then some (.set (decide (mem.bytes[100]? = some 1)), 1)
  else none

def execC : Op → State → Memory → Nat → Silmaril.X86.Ext.Result
  | .st a, s, mem, _ =>
    match mem.writeBytes a [1] with
    | some m => .ok { s with rip := s.rip + 1 } m
    | none => .dataFault
  | .set v, s, mem, _ => .ok { s.write .rax (if v then 1 else 0) with rip := s.rip + 1 } mem

def accC : Op → State → Nat → List Silmaril.X86.MemEvent.Event
  | .st a, _, _ => [⟨.store, a, 1, false⟩]
  | .set _, _, _ => []

theorem writeSet_st {a x : Nat} {s : State} {n : Nat} (h : writeSet (accC (.st a) s n) x) :
    x = a := by
  obtain ⟨e, he, -, h1, h2⟩ := h
  simp only [accC, List.mem_singleton] at he
  subst he
  simp only at h1 h2
  omega

theorem install1 (b : Silmaril.Process.ByteMemory) (a x : Nat) :
    (Memory.install b a [1])[x]? = if x = a then some 1 else b[x]? := by
  simp only [Memory.install, Std.ExtHashMap.getElem?_insert]
  by_cases h : x = a
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **`execC` is access-local** for `accC`. -/
theorem localC (i : Op) (s : State) (n : Nat) :
    Silmaril.X86.MemEvent.Local Silmaril.X86.MemEvent.extView
      (fun mem => execC i s mem n) (accC i s n) := by
  constructor
  intro m m' hag
  cases i with
  | set v =>
    simp only [execC, Silmaril.X86.MemEvent.extView, Silmaril.X86.MemEvent.Rel]
    refine ⟨trivial, Silmaril.X86.MemEvent.Patched.none (fun a ⟨e, he, _⟩ => ?_)⟩
    simp [accC] at he
  | st a =>
    have hreg := hag.1
    have hcs : m'.checkSpan .write a ([1] : List Byte).length =
        m.checkSpan .write a ([1] : List Byte).length := by
      simp [Memory.checkSpan, Memory.permits, hreg]
    have hW : ∀ x, ¬ writeSet (accC (.st a) s n) x → x ≠ a := fun x hx e => hx (by
      subst e; exact ⟨_, List.mem_singleton_self _, rfl, by simp, by simp⟩)
    cases hc : m.checkSpan .write a ([1] : List Byte).length with
    | false =>
      simp only [execC, Memory.writeBytes]
      rw [hcs, hc]
      exact rfl
    | true =>
      simp only [execC, Memory.writeBytes]
      rw [hcs, hc]
      simp only [ite_true, Silmaril.X86.MemEvent.extView, Silmaril.X86.MemEvent.Rel]
      refine ⟨trivial, ⟨rfl, rfl, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩⟩
      · rw [writeSet_st hx, install1, install1]; simp
      · rw [install1]; simp [hW x hx]
      · rw [install1]; simp [hW x hx]
      · rw [writeSet_st hx]
        refine ⟨?_, by rw [install1]; simp⟩
        have := (Memory.checkSpan_iff _ _ _ _).mp hc
        simpa using this.2.2 0 (by simp)

/-- The machine. -/
def M : EvMachine := ⟨Op, fetchC, execC, accC, localC⟩

/-! ## The pool -/

def rwx : Permissions := ⟨true, true, true⟩
def memC : Memory := ⟨[Example.allRegion], ∅⟩
def start (t : Bool) : Word := if t then 16 else 32
def cell (t : Bool) : Nat := if t then 100 else 101
def coreC (t : Bool) : State := ⟨fun _ => 0, start t, ⟨none, none, none, none, none, none⟩, 0⟩
def poolC : Pool Bool := ⟨fun t => some (coreC t), memC⟩
def finC (t : Bool) (c : State) : Prop := c.rip = start t + 2

/-- Thread `t` owns `rip`, `rax` and its byte. -/
def σC (t : Bool) : Frag := fun l =>
  match l with
  | .rip => some (.word (start t))
  | .reg .rax => some (.word 0)
  | .mem a => if a = cell t then some (.cell ⟨none, rwx⟩) else none
  | _ => none

/-- The four code bytes, read-only. -/
def rC : Frag := fun l =>
  match l with
  | .mem a => if a = 16 ∨ a = 17 ∨ a = 32 ∨ a = 33 then some (.cell ⟨none, rwx⟩) else none
  | _ => none

theorem permsAt_all (mem : Memory) (hr : mem.regions = [Example.allRegion]) (a : Nat)
    (ha : a < 2 ^ 64) : permsAt mem a = rwx := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, hr, Example.allRegion, Region.Contains, Permissions.allows,
    this, rwx]

/-! ## The hypothesis holds -/

section Safe
variable (t : Bool)

theorem stage2 : ∀ n (c : State) (h : Frag), c.rip = start t + 2 →
    LSafeEvK M (finC t) (fun _ => True) rC n c h
  | 0, _, _, _ => trivial
  | _ + 1, _, _, hc => fun _ _ => .inl ⟨hc, trivial⟩

theorem fin_ne (k : Nat) (hk : k < 2) : ¬ (start t + BitVec.ofNat 64 k = start t + 2) := by
  intro e
  have := congrArg BitVec.toNat e
  cases t <;> simp [start] at this <;> omega

theorem stage1 : ∀ n (c : State) (h : Frag), c.rip = start t + 1 → (h .rip).isSome →
    (h (.reg .rax)).isSome → LSafeEvK M (finC t) (fun _ => True) rC n c h
  | 0, _, _, _, _, _ => trivial
  | n + 1, c, h, hc, hrip, hrax => fun mem hle => by
    right
    have hpc : c.rip.toNat = (if t then 17 else 33) := by rw [hc]; cases t <;> rfl
    let v : Bool := if t then decide (mem.bytes[101]? = some 1)
      else decide (mem.bytes[100]? = some 1)
    have hf : M.fetch mem c.rip.toNat = some (.set v, 1) := by
      show fetchC mem c.rip.toNat = _
      rw [hpc]; cases t <;> simp [fetchC, v] <;> rfl
    let c' : State := { c.write .rax (if v then 1 else 0) with rip := c.rip + 1 }
    refine ⟨fun e => fin_ne t 1 (by omega) (hc ▸ e), .set v, 1, ⟨c', mem⟩, hf, ⟨fun j hj => ?_,
      fun a ha => ?_, fun a ha => ?_⟩, ?_, ?_, ?_⟩
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [hpc]
      apply Example.union_isSome_right
      cases t <;> simp [rC]
    · obtain ⟨e, he, -⟩ := ha; simp [M, accC] at he
    · obtain ⟨e, he, -⟩ := ha; simp [M, accC] at he
    · show (fetchC mem c.rip.toNat).bind _ = _
      rw [show fetchC mem c.rip.toNat = some (.set v, 1) from hf]
      rfl
    · intro l hl
      cases l with
      | reg q =>
        by_cases hq : q = .rax
        · subst hq; rw [hl] at hrax; cases hrax
        · simp [toFrag, c', hq]
      | rip => rw [hl] at hrip; cases hrip
      | flags => rfl
      | mem a => rfl
      | regions => rfl
    · refine stage2 t n _ _ ?_
      show c.rip + 1 = _
      rw [hc, BitVec.add_assoc]; rfl

theorem stage0 : ∀ n (c : State) (h : Frag), c.rip = start t → (h .rip).isSome →
    (h (.reg .rax)).isSome → h (.mem (cell t)) = some (.cell ⟨none, rwx⟩) →
    LSafeEvK M (finC t) (fun _ => True) rC n c h
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, c, h, hc, hrip, hrax, hcell => fun mem hle => by
    right
    have hpc : c.rip.toNat = (if t then 16 else 32) := by rw [hc]; cases t <;> rfl
    have hf : M.fetch mem c.rip.toNat = some (.st (cell t), 1) := by
      show fetchC mem c.rip.toNat = _
      rw [hpc]; cases t <;> simp [fetchC, cell] <;> rfl
    have hct : cell t < 2 ^ 64 := by cases t <;> simp [cell]
    have hperm : permsAt mem (cell t) = rwx := by
      have := hle (.mem (cell t)) (.cell ⟨none, rwx⟩) (by simp [union, hcell])
      simp only [toFrag, Option.some.injEq, Val.cell.injEq, Cell.mk.injEq] at this
      exact this.2
    have hcs : mem.checkSpan .write (cell t) ([1] : List Byte).length = true := by
      rw [Memory.checkSpan_iff]
      refine ⟨hct, by cases t <;> simp [cell, Silmaril.Process.addressLimit], fun o ho => ?_⟩
      have ho0 : o = 0 := by simpa using ho
      subst ho0
      have := congrArg Permissions.write hperm
      simpa [permsAt, rwx] using this
    let mem₁ : Memory := { mem with bytes := Memory.install mem.bytes (cell t) [1] }
    have hx : execC (.st (cell t)) c mem 1 = .ok { c with rip := c.rip + 1 } mem₁ := by
      simp only [execC, Memory.writeBytes, hcs, ite_true]; rfl
    refine ⟨fun e => by rw [finC, hc] at e; exact absurd e (by cases t <;> decide), .st (cell t), 1,
      ⟨{ c with rip := c.rip + 1 }, mem₁⟩, hf, ⟨fun j hj => ?_, fun a ha => ?_, fun a ha => ?_⟩,
      ?_, ?_, ?_⟩
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [hpc]
      apply Example.union_isSome_right
      cases t <;> simp [rC]
    · obtain ⟨e, he, hr, -⟩ := ha
      simp only [M, accC, List.mem_singleton] at he
      subst he; cases hr
    · have := writeSet_st (s := c) (n := 1) ha
      subst this
      rw [hcell]; rfl
    · simp only [EvMachine.step, hf, Option.bind_some]
      show Silmaril.X86.Open.ofResult (execC (.st (cell t)) c mem 1) = _
      rw [hx]; rfl
    · intro l hl
      cases l with
      | reg q => rfl
      | rip => rw [hl] at hrip; cases hrip
      | flags => rfl
      | mem a =>
        have ha : a ≠ cell t := by rintro rfl; rw [hl] at hcell; cases hcell
        simp only [toFrag, mem₁]
        rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?, install1]
        simp [ha, permsAt, Memory.permits]
      | regions => rfl
    · refine stage1 t n _ _ ?_ ?_ ?_
      · show c.rip + 1 = _; rw [hc]
      · simp [Frag.reval, hrip, toFrag]
      · simp [Frag.reval, hrax, toFrag]

end Safe

theorem embed_cell {t : Bool} {a : Nat} (v : Val) (h : embed (Tid := Bool) t (σC t)
    (.shared (.mem a)) = some v) : a = cell t := by
  simp only [embed, Loc.isLocal, Bool.false_eq_true, ite_false, σC] at h
  split at h
  · assumption
  · cases h

/-- **The hypothesis holds of the pool.** -/
theorem ownK : OwnershipSafeEvK M finC poolC := by
  refine ⟨σC, rC, fun _ _ => True, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    cases l <;> simp_all [rC, Loc.isLocal]
  · intro t ht; simp [poolC] at ht
  · intro t t' htt L
    cases L with
    | «local» u l =>
      by_cases hu : u = t
      · subst hu; right; simp [embed, htt]
      · left; simp [embed, hu]
    | shared l =>
      cases l with
      | mem a =>
        by_cases ha : a = cell t
        · right
          simp only [embed, Loc.isLocal, Bool.false_eq_true, ite_false, σC]
          have : a ≠ cell t' := by
            subst ha; cases t <;> cases t' <;> simp_all [cell]
          simp [this]
        · left; simp [embed, Loc.isLocal, σC, ha]
      | _ => left; simp [embed, Loc.isLocal, σC]
  · intro t L
    cases L with
    | «local» u l => right; rfl
    | shared l =>
      cases l with
      | mem a =>
        by_cases ha : a = cell t
        · right
          subst ha
          simp only [embedS, Loc.isLocal, Bool.false_eq_true, ite_false, rC]
          cases t <;> simp [cell]
        · left; simp [embed, Loc.isLocal, σC, ha]
      | _ => left; simp [embed, Loc.isLocal, σC]
  · intro t L v hv
    cases L with
    | «local» u l =>
      simp only [embed] at hv
      split at hv
      · rename_i hul
        obtain ⟨rfl, hl⟩ := hul
        cases l with
        | rip => simp only [σC] at hv; cases hv; simp [poolFrag, poolC, coreC, localFrag]
        | reg q =>
          cases q <;> simp only [σC] at hv <;> try cases hv
          simp [poolFrag, poolC, coreC, localFrag, State.read]
        | flags => simp [σC] at hv
        | mem a => cases hl
        | regions => cases hl
      · cases hv
    | shared l =>
      cases l with
      | mem a =>
        have := embed_cell v hv
        subst this
        simp only [embed, Loc.isLocal, Bool.false_eq_true, ite_false, σC, ite_true] at hv
        cases hv
        simp only [poolFrag, poolC, sharedFrag, memC]
        rw [permsAt_all _ rfl _ (by cases t <;> simp [cell])]
        simp
      | _ => simp [embed, Loc.isLocal, σC] at hv
  · intro L v hv
    cases L with
    | «local» u l => simp [embedS] at hv
    | shared l =>
      cases l with
      | mem a =>
        simp only [embedS, Loc.isLocal, Bool.false_eq_true, ite_false, rC] at hv
        split at hv
        · rename_i ha
          cases hv
          simp only [poolFrag, poolC, sharedFrag, memC]
          rw [permsAt_all _ rfl _ (by omega)]
          simp
        · cases hv
      | _ => simp [embedS, Loc.isLocal, rC] at hv
  · intro t c ht n
    simp only [poolC, Option.some.injEq] at ht
    subst ht
    exact stage0 t n _ _ rfl rfl rfl (by simp [σC])

/-! ## The TSO run -/

def cA1 : State := { coreC true with rip := (coreC true).rip + 1 }
def cB1 : State := { coreC false with rip := (coreC false).rip + 1 }
def cA2 : State := { cA1.write .rax (if false then 1 else 0) with rip := cA1.rip + 1 }
def cB2 : State := { cB1.write .rax (if false then 1 else 0) with rip := cB1.rip + 1 }
def vA : Memory := { memC with bytes := Memory.install memC.bytes 100 [1] }
def vB : Memory := { memC with bytes := Memory.install memC.bytes 101 [1] }

theorem cs (a : Nat) (ha : a < 2 ^ 64) : memC.checkSpan .write a ([1] : List Byte).length = true := by
  rw [Memory.checkSpan_iff]
  refine ⟨ha, by simp [Silmaril.Process.addressLimit]; omega, fun o ho => ?_⟩
  have := permsAt_all memC rfl (a + o) (by simp at ho; omega)
  have := congrArg Permissions.write this
  simpa [permsAt, rwx] using this

theorem readSpan1 (a : Nat) (b : Silmaril.Process.ByteMemory) :
    readSpan { memC with bytes := Memory.install b a [1] } a 1 = [1] := by
  simp only [readSpan, List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
    Std.ExtHashMap.get?_eq_getElem?, install1, ite_true, Option.getD_some]

/-- **Both threads finish with `rax = 0`** in a drained state the TSO pool reaches. -/
theorem tso_run : ∃ p, TsoReach M finC (TPool.ofPool poolC) p ∧ Drained p ∧
    (∃ cA cB, p.threads true = some cA ∧ p.threads false = some cB ∧ cA.rip = 18 ∧
      cB.rip = 34 ∧ cA.read .rax = 0 ∧ cB.read .rax = 0) := by
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.single (.inl ⟨true,
      TsoStep.buffered (c := coreC true) (c' := cA1) (i := Op.st 100) (n := 1) (view' := vA)
        ?a1 ?a2 ?a3 ?a4 ?a5⟩))
      (.inl ⟨false, TsoStep.buffered (c := coreC false) (c' := cB1) (i := Op.st 101) (n := 1)
        (view' := vB) ?b1 ?b2 ?b3 ?b4 ?b5⟩))
      (.inl ⟨true, TsoStep.buffered (c := cA1) (c' := cA2) (i := Op.set false) (n := 1)
        (view' := overlay memC [(100, readSpan vA 100 1)])
        ?c1 ?c2 ?c3 ?c4 ?c5⟩))
      (.inl ⟨false, TsoStep.buffered (c := cB1) (c' := cB2) (i := Op.set false) (n := 1)
        (view' := overlay memC [(101, readSpan vB 101 1)])
        ?d1 ?d2 ?d3 ?d4 ?d5⟩))
      (.inr (TsoFlush.head (t := true) (a := 100) (bs := [1]) (rest := []) ?e1)))
      (.inr (TsoFlush.head (t := false) (a := 101) (bs := [1]) (rest := []) ?f1)), ?g, ?h⟩
  case a1 => rfl
  case a2 => show ¬ ((16 : Word) = 16 + 2); decide
  case a3 => rfl
  case a4 => rfl
  case a5 =>
    show execC (Op.st 100) (coreC true) memC 1 = _
    simp only [execC, Memory.writeBytes, cs 100 (by simp), ite_true]; rfl
  case b1 => rfl
  case b2 => show ¬ ((32 : Word) = 32 + 2); decide
  case b3 => rfl
  case b4 => rfl
  case b5 =>
    show execC (Op.st 101) (coreC false) memC 1 = _
    simp only [execC, Memory.writeBytes, cs 101 (by simp), ite_true]; rfl
  case c1 => rfl
  case c2 => show ¬ ((16 : Word) + 1 = 16 + 2); decide
  case c3 =>
    show fetchC (overlay memC [(100, readSpan vA 100 1)]) 17 = _
    simp only [fetchC, overlay, foldl_install_getElem?, readSpan1, vA]
    simp [Silmaril.X86.MemoryModel.Tso.readBufByte, Silmaril.X86.MemoryModel.Tso.entryByte, memC]
    rfl
  case c4 => rfl
  case c5 => rfl
  case d1 => rfl
  case d2 => show ¬ ((32 : Word) + 1 = 32 + 2); decide
  case d3 =>
    show fetchC (overlay memC [(101, readSpan vB 101 1)]) 33 = _
    simp only [fetchC, overlay, foldl_install_getElem?, readSpan1, vB]
    simp [Silmaril.X86.MemoryModel.Tso.readBufByte, Silmaril.X86.MemoryModel.Tso.entryByte, memC]
    rfl
  case d4 => rfl
  case d5 => rfl
  case e1 =>
    show [(100, readSpan vA 100 1)] ++ [] = _
    rw [vA, readSpan1]; rfl
  case f1 =>
    show [(101, readSpan vB 101 1)] ++ [] = _
    rw [vB, readSpan1]; rfl
  case g => intro t; cases t <;> rfl
  case h =>
    refine ⟨cA2, cB2, rfl, rfl, by decide, by decide, ?_, ?_⟩ <;>
      simp [cA2, cB2, State.read_write_same]

/-! ## No SC run reaches it -/

/-- The SC invariant: positions, the stored bytes, and the store-buffering exclusion. -/
def J (q : Pool Bool) : Prop :=
  ∃ cA cB, q.threads true = some cA ∧ q.threads false = some cB ∧
    (cA.rip = 16 ∨ cA.rip = 17 ∨ cA.rip = 18) ∧ (cB.rip = 32 ∨ cB.rip = 33 ∨ cB.rip = 34) ∧
    (q.memory.bytes[100]? = some 1 ↔ cA.rip ≠ 16) ∧ (q.memory.bytes[101]? = some 1 ↔ cB.rip ≠ 32) ∧
    (cA.rip = 18 → cB.rip = 34 → cA.read .rax = 0 → cB.read .rax = 1) ∧
    (cB.rip = 34 → cA.rip = 18 → cB.read .rax = 0 → cA.read .rax = 1)

/-- The step of `M` from a store. -/
theorem step_st {c : State} {mem : Memory} {m' : MState} {pc a : Nat}
    (hpc : c.rip.toNat = pc) (hf : fetchC mem pc = some (.st a, 1))
    (hs : M.step ⟨c, mem⟩ = some m') :
    m' = ⟨{ c with rip := c.rip + 1 }, { mem with bytes := Memory.install mem.bytes a [1] }⟩ := by
  simp only [EvMachine.step, hpc] at hs
  rw [show M.fetch mem pc = some (.st a, 1) from hf] at hs
  simp only [Option.bind_some] at hs
  change Silmaril.X86.Open.ofResult (execC (.st a) c mem 1) = _ at hs
  by_cases hc : mem.checkSpan .write a ([1] : List Byte).length = true
  · simp only [execC, Memory.writeBytes, hc, ite_true, Silmaril.X86.Open.ofResult,
      Option.some.injEq] at hs
    exact hs.symm
  · simp only [Bool.not_eq_true] at hc
    simp only [execC, Memory.writeBytes, hc, Bool.false_eq_true, ite_false,
      Silmaril.X86.Open.ofResult] at hs
    cases hs

/-- The step of `M` from a `set`. -/
theorem step_set {c : State} {mem : Memory} {m' : MState} {pc : Nat} {v : Bool}
    (hpc : c.rip.toNat = pc) (hf : fetchC mem pc = some (.set v, 1))
    (hs : M.step ⟨c, mem⟩ = some m') :
    m' = ⟨{ c.write .rax (if v then 1 else 0) with rip := c.rip + 1 }, mem⟩ := by
  simp only [EvMachine.step, hpc] at hs
  rw [show M.fetch mem pc = some (.set v, 1) from hf] at hs
  simp only [Option.bind_some] at hs
  change Silmaril.X86.Open.ofResult (execC (.set v) c mem 1) = _ at hs
  simp only [execC, Silmaril.X86.Open.ofResult, Option.some.injEq] at hs
  exact hs.symm

theorem rax_set (c : State) (v : Bool) :
    ({ c.write .rax (if v then 1 else 0) with rip := c.rip + 1 } : State).read .rax =
      if v then 1 else 0 := by
  simp [State.read_write_same]

theorem w_ne {x y : Word} (h : x ≠ y := by decide) : x ≠ y := h

/-- **The invariant is preserved by every SC step.** -/
theorem J_step {q q' : Pool Bool} {t : Bool} (hJ : J q) (hs : SCStepF M.step finC q t q') :
    J q' := by
  obtain ⟨cA, cB, hA, hB, rA, rB, i100, i101, jA, jB⟩ := hJ
  obtain ⟨⟨c, ht, hnf⟩, hst⟩ := hs
  cases hst with
  | go ht' hs' =>
    rename_i c₁ m'
    rw [ht] at ht'; cases ht'
    cases t with
    | true =>
      rw [hA] at ht; cases ht
      rcases rA with h16 | h17 | h18
      · have e := step_st (a := 100) (by rw [h16]) (by simp [fetchC]) hs'
        subst e
        have r' : cA.rip + 1 = 17 := by rw [h16]; decide
        refine ⟨{ cA with rip := cA.rip + 1 }, cB, by simp, by simp [hB], .inr (.inl r'), rB, ?_,
          ?_, ?_, ?_⟩
        · simp only [install1, ite_true, r']; simp
        · simp only [install1, show (101 : Nat) ≠ 100 by omega, ite_false]; exact i101
        · intro h; exact absurd (r'.symm.trans h) (by decide)
        · intro _ h; exact absurd (r'.symm.trans h) (by decide)
      · have e := step_set (v := decide (q.memory.bytes[101]? = some 1)) (by rw [h17])
          (by simp [fetchC]) hs'
        subst e
        have r' : cA.rip + 1 = 18 := by rw [h17]; decide
        have hv : cB.rip = 34 → decide (q.memory.bytes[101]? = some 1) = true := by
          intro h; simp only [decide_eq_true_eq]; exact i101.mpr (by rw [h]; decide)
        refine ⟨{ cA.write .rax (if decide (q.memory.bytes[101]? = some 1) then 1 else 0) with
          rip := cA.rip + 1 }, cB, by simp, by simp [hB], .inr (.inr r'), rB, ?_, i101, ?_, ?_⟩
        · show _ ↔ cA.rip + 1 ≠ 16
          rw [r']; exact ⟨fun _ => by decide, fun _ => i100.mpr (by rw [h17]; decide)⟩
        · intro _ h hz
          rw [rax_set, hv h] at hz; exact absurd hz (by decide)
        · intro h _ _
          rw [rax_set, hv h]; rfl
      · exact absurd (show finC true cA by unfold finC; rw [h18]; rfl) hnf
    | false =>
      rw [hB] at ht; cases ht
      rcases rB with h32 | h33 | h34
      · have e := step_st (a := 101) (by rw [h32]) (by simp [fetchC]) hs'
        subst e
        have r' : cB.rip + 1 = 33 := by rw [h32]; decide
        refine ⟨cA, { cB with rip := cB.rip + 1 }, by simp [hA], by simp, rA, .inr (.inl r'), ?_,
          ?_, ?_, ?_⟩
        · simp only [install1, show (100 : Nat) ≠ 101 by omega, ite_false]; exact i100
        · simp only [install1, ite_true, r']; simp
        · intro _ h; exact absurd (r'.symm.trans h) (by decide)
        · intro h; exact absurd (r'.symm.trans h) (by decide)
      · have e := step_set (v := decide (q.memory.bytes[100]? = some 1)) (by rw [h33])
          (by simp [fetchC]) hs'
        subst e
        have r' : cB.rip + 1 = 34 := by rw [h33]; decide
        have hv : cA.rip = 18 → decide (q.memory.bytes[100]? = some 1) = true := by
          intro h; simp only [decide_eq_true_eq]; exact i100.mpr (by rw [h]; decide)
        refine ⟨cA, { cB.write .rax (if decide (q.memory.bytes[100]? = some 1) then 1 else 0) with
          rip := cB.rip + 1 }, by simp [hA], by simp, rA, .inr (.inr r'), i100, ?_, ?_, ?_⟩
        · show _ ↔ cB.rip + 1 ≠ 32
          rw [r']; exact ⟨fun _ => by decide, fun _ => i101.mpr (by rw [h33]; decide)⟩
        · intro h _ _
          rw [rax_set, hv h]; rfl
        · intro _ h hz
          rw [rax_set, hv h] at hz; exact absurd hz (by decide)
      · exact absurd (show finC false cB by unfold finC; rw [h34]; rfl) hnf

theorem J_init : J poolC := by
  refine ⟨coreC true, coreC false, rfl, rfl, .inl rfl, .inl rfl, ?_, ?_, ?_, ?_⟩
  · simp [poolC, memC, coreC, start]
  · simp [poolC, memC, coreC, start]
  · intro h; exact absurd h (by decide)
  · intro h; exact absurd h (by decide)

theorem J_reach {q : Pool Bool} (hr : SCReach M.step finC poolC q) : J q := by
  induction hr with
  | refl => exact J_init
  | tail _ hst ih => obtain ⟨t, hst⟩ := hst; exact J_step ih hst

/-- **The first `Task.drfTso` is false.** -/
theorem not_taskK : ¬ TaskFetch := by
  intro h
  obtain ⟨p, hr, hd, cA, cB, hA, hB, rA, rB, xA, xB⟩ := tso_run
  obtain ⟨cA', cB', hA', hB', -, -, -, -, jA, -⟩ := J_reach (h M finC poolC ownK p hr hd)
  simp only [forget] at hA' hB'
  rw [hA] at hA'; rw [hB] at hB'
  cases hA'; cases hB'
  have := jA rA rB xA
  rw [xB] at this
  exact absurd this (by decide)

end Silmaril.Proofs.X86.Pool.Counter
