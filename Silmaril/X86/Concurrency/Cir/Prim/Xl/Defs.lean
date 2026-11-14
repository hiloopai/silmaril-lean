module

public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Defs

/-!
# The synchronisation primitives on every buffered model: statements

The four synchronisation primitive goals of
`Prim/Tasks/Defs.lean` are stated and proved there on the CIR-native TSO machine. Here each is
restated for **every** buffered model `M : Csl.OModel` (`.tso` or `.xl`; these are the
operational models below XL, and TSO's runs are XL's, `Csl.tso_reach_xl`). All four are PROVED
in `Prim/Xl/Thms.lean`.

The only new hypothesis is tameness of the client code that the Task leaves open: the
critical sections `cs t` of the two locks must pass the syntactic check `Stmt.wbStores` (every
`store` write-back). The locks', seqlock's and ring's own code pass it (`Prim.Xl` checks it once
for every loop bound), and so do the seqlock's and ring's client glue, so `seqlockXl` and
`spscFifoXl` have exactly the hypotheses of `Task.seqlockTso` and `Task.spscFifoTso`.

Why the hypothesis on `cs`: the unlocks are plain-`mov` releases. On XL a write-back store can
leave the buffer before an earlier `nt`/`str` store (`Csl.Ent.passes`), so a weak store in a
critical section could become visible after the unlock. The proofs do not need anything
weaker than "no weak store at all", and none is attempted.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Clients

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim

/-- **The spinlock (`mov` unlock) is a lock on every buffered model** (PROVED,
`Prim.Clients.spinMutexXl_holds`): `Task.spinMutexTso` for `OStep M` with `M = .tso` or `.xl`,
for critical sections whose stores are write-back. -/
def spinMutexXl : Prop :=
  ∀ (N L l : Nat) (R : Csl.HProp) (hR0 : Csl.Heap) (cs : Nat → Stmt), l < 2 ^ 64 →
    hR0 l = none → R hR0 → (∀ t, .rdi ∉ (cs t).writes) → (∀ t, (cs t).wbStores = true) →
    (∀ t rs h, R h → Csl.Safe (fun h => h = Csl.Heap.empty) (fun _ h' => R h') (cs t) rs h) →
    ∀ (M : Csl.OModel) (C : Csl.OCfg), Csl.OReach M N
      (lockCfg (SpinLock.cert.body L) (SpinUnlock.cert.body L) N l cs (heapOf [(l, 0)] hR0)).toO C →
      C.Drained → (∀ t < N, (C.ts t).1 = .skip) →
      C.mem l = some 0 ∧ ∃ hR, R hR ∧ Csl.Heap.Le hR C.mem

/-- **The ticket lock is a lock on every buffered model** (PROVED,
`Prim.Clients.ticketMutexXl_holds`): `Task.ticketMutexTso` for every `M`, for critical
sections whose stores are write-back. -/
def ticketMutexXl : Prop :=
  ∀ (N L l : Nat) (R : Csl.HProp) (hR0 : Csl.Heap) (cs : Nat → Stmt), N < 2 ^ 32 →
    l + 8 < 2 ^ 64 → hR0 l = none → hR0 (l + 4) = none → R hR0 → (∀ t, .rdi ∉ (cs t).writes) →
    (∀ t, (cs t).wbStores = true) →
    (∀ t rs h, R h → Csl.Safe (fun h => h = Csl.Heap.empty) (fun _ h' => R h') (cs t) rs h) →
    ∀ (M : Csl.OModel) (C : Csl.OCfg), Csl.OReach M N
      (lockCfg (TicketLock.cert.body L) (TicketUnlock.cert.body L) N l cs
        (heapOf [(l, 0), (l + 4, 0)] hR0)).toO C →
      C.Drained → (∀ t < N, (C.ts t).1 = .skip) →
      C.mem l = some N ∧ C.mem (l + 4) = some N ∧ ∃ hR, R hR ∧ Csl.Heap.Le hR C.mem

/-- **The seqlock on every buffered model** (PROVED, `Prim.Clients.seqlockXl_holds`):
`Task.seqlockTso` for every `M`, with the same hypotheses. -/
def seqlockXl : Prop :=
  ∀ (L s : Nat) (ws : List (Nat × Nat)) (outs : List Nat), s + 12 < 2 ^ 64 →
    (∀ p ∈ ws, p.1 < 2 ^ 32 ∧ p.2 < 2 ^ 32) → ws.length < 2 ^ 31 →
    (∀ o ∈ outs, o + 8 ≤ 2 ^ 64 ∧ (o + 8 ≤ s ∨ s + 12 ≤ o)) →
    outs.Pairwise (fun o o' => o + 8 ≤ o' ∨ o' + 8 ≤ o) →
    let writer : Stmt := Tv.chain (ws.map fun p => Tv.chain [.assign .rsi (.lit p.1),
      .assign .rdx (.lit p.2), SeqWrite.cert.body L])
    let N := outs.length + 1
    let C0 : Csl.Cfg := ⟨fun t =>
      if t = 0 then (writer, regs [(.rdi, s)])
      else if t < N then (SeqRead.cert.body L, regs [(.rdi, s), (.rsi, outs.getD (t - 1) 0)])
      else (.skip, Regs.zero),
      heapOf ([(s, 0), (s + 4, 0), (s + 8, 0)] ++ outs.flatMap fun o => [(o, 0), (o + 4, 0)])
        Csl.Heap.empty⟩
    ∀ (M : Csl.OModel) (C : Csl.OCfg), Csl.OReach M N C0.toO C → C.Drained →
      (∀ t < N, (C.ts t).1 = .skip) →
      ∀ o ∈ outs, ∃ p ∈ (0, 0) :: ws, C.mem o = some p.1 ∧ C.mem (o + 4) = some p.2

/-- **The SPSC ring on every buffered model** (PROVED, `Prim.Clients.spscFifoXl_holds`):
`Task.spscFifoTso` for every `M`, with the same hypotheses. -/
def spscFifoXl : Prop :=
  ∀ (L q out res k : Nat) (vs : List Nat), q + 16 < 2 ^ 64 → out + 4 * k < 2 ^ 64 →
    res + 4 * vs.length < 2 ^ 64 →
    (out + 4 * k ≤ q ∨ q + 16 ≤ out) → (res + 4 * vs.length ≤ q ∨ q + 16 ≤ res) →
    (res + 4 * vs.length ≤ out ∨ out + 4 * k ≤ res) →
    (∀ v ∈ vs, 0 < v ∧ v < 2 ^ 32) →
    let prod : Stmt := Tv.chain ((List.range vs.length).map fun j =>
      Tv.chain [.assign .rsi (.lit (vs.getD j 0)), SpscPush.cert.body L,
        .store .na 4 .wb (.lit (res + 4 * j)) (.reg .rax)])
    let cons : Stmt := Tv.chain ((List.range k).map fun i =>
      Tv.chain [.assign .rsi (.lit (out + 4 * i)), SpscPop.cert.body L])
    let C0 : Csl.Cfg := ⟨fun t =>
      if t = 0 then (prod, regs [(.rdi, q)]) else if t = 1 then (cons, regs [(.rdi, q)])
      else (.skip, Regs.zero),
      heapOf ([(q, 0), (q + 4, 0), (q + 8, 0), (q + 12, 0)] ++
        ((List.range k).map fun i => (out + 4 * i, 0)) ++
        (List.range vs.length).map fun j => (res + 4 * j, 0)) Csl.Heap.empty⟩
    ∀ (M : Csl.OModel) (C : Csl.OCfg), Csl.OReach M 2 C0.toO C → C.Drained →
      (∀ t < 2, (C.ts t).1 = .skip) →
      let got := ((List.range k).map fun i => (C.mem (out + 4 * i)).getD 0).filter (· != 0)
      let pushed := ((List.range vs.length).filter fun j => C.mem (res + 4 * j) == some 1).map
        fun j => vs.getD j 0
      let h := (C.mem q).getD 0
      let n := ((C.mem (q + 4)).getD 0 + 2 ^ 32 - h) % 2 ^ 32
      let rem := (List.range n).map fun j => (C.mem (q + 8 + 4 * ((h + j) % 2))).getD 0
      got ++ rem = pushed

end Silmaril.X86.Concurrency.Cir.Prim.Clients
