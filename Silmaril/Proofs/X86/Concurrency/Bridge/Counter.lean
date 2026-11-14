module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Litmus.Extract.Thms

/-!
# The unrestricted `Task.piecesComplete` is false

`piecesCompleteUnrestricted_false`: the original statement of
`Bridge.Task.piecesComplete` (without `run ≠ [] ∨ th.code.length < 2 ^ 64`) fails for the thread
`th (2 ^ 64)`: `2 ^ 64` one-byte `nop`s (`0x90`) at address `0`, cut into `2 ^ 64` pieces
`pad 1` (`c (2 ^ 64)`).

* `stvRun_pads`: the checker accepts it (`pwalk_pads`: every piece is one `nop` of length 1);
* `pexplore_some`: the pieces' exploration succeeds for every spin bound, with fuel 1;
* the end `0 + 2 ^ 64` wraps to `0` = the initial `rip`, so the empty run is a `DomRun`;
* `pexplore_steps`: every trace of the pieces executes the first `nop`, so none is empty.

Everything is generic in the number of pieces `M` and only specialized to `2 ^ 64` at the end, so
no list of `2 ^ 64` elements is ever evaluated.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.Counter

open Silmaril.X86 (State Word Byte)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym DomRun Trace explore consStep)
open Silmaril.X86.Concurrency.Cir.Tv (XThread SThread SCert SPiece stvRun pexplore fetchAt padOk pwalk catTr)
open Silmaril.X86.Concurrency.Bridge (whole PiecesCompleteUnrestricted)


/-- The one-byte `nop`. -/
def nopB : Byte := 144#8

theorem ifp {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]


theorem decode_nop : Atomic9.decode [nopB] = some (.open9 (.ext8 (.base (.nop 0))), 1) := by decide

theorem padOk_nop (t : XThread) (h : t.code = [nopB]) : padOk t = true := by
  obtain ⟨b, c, r, i⟩ := t; simp only at h; subst h; rfl

theorem fetch_nop {t : XThread} {s : State} (h : t.code = [nopB]) (hr : s.rip = t.base) :
    t.fetch s = some (.open9 (.ext8 (.base (.nop 0))), 1) := by
  simp [Silmaril.X86.Litmus.Thread.fetch, h, hr, Silmaril.X86.maxInstrLength, decode_nop]

theorem stepSym_nop {t : XThread} {dom : List Nat} {s : State} {k : Fin 15} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.nop k))), n)) :
    stepSym t dom s = some [([], { s with rip := s.rip + BitVec.ofNat 64 n })] := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire]

theorem explore_nop {t : XThread} {dom : List Nat} {s : State} (f : Nat) (h : t.code = [nopB])
    (hr : s.rip = t.base) :
    explore t dom (f + 1) s = some [⟨[⟨[], { s with rip := s.rip + 1 }⟩], { s with rip := s.rip + 1 }⟩] := by
  have hne : s.rip ≠ t.endRip := by
    simp [Silmaril.X86.Litmus.Thread.endRip, h, hr]
  rw [explore, ite_eq_right_of_eq_false _ _ (eq_false hne), stepSym_nop (fetch_nop h hr)]
  cases f with
  | zero => simp [explore, Silmaril.X86.Litmus.Thread.endRip, h, hr, consStep]
  | succ f => simp [explore, Silmaril.X86.Litmus.Thread.endRip, h, hr, consStep]

variable (M : Nat)
/-- `M` one-byte `nop`s at address `0`. -/
def th : SThread := ⟨0, List.replicate M nopB, [], Silmaril.X86.Litmus.initCore 0 []⟩
/-- `M` pieces `pad 1`. -/
def c : SCert := ⟨[], List.replicate M (.pad 1)⟩

theorem th_code : (th M).code = List.replicate M nopB := rfl

theorem sub_code {o : Nat} (ho : o < M) : ((th M).sub o (o + 1)).code = [nopB] := by
  show ((List.replicate M nopB).drop o).take (o + 1 - o) = _
  rw [List.drop_replicate, List.take_replicate]
  have : min (o + 1 - o) (M - o) = 1 := by omega
  rw [this]; rfl

theorem pwalk_pads : ∀ (k o : Nat) (K Z : List Silmaril.X86.Reg), o + k = M →
    pwalk (th M) o (List.replicate k (.pad 1)) K Z = some K := by
  intro k
  induction k with
  | zero => intro o K Z h; simp only [List.replicate, pwalk, th_code, List.length_replicate]; exact ifp (by omega)
  | succ k ih =>
    intro o K Z h
    rw [List.replicate_succ, pwalk]
    have ho : o < M := by omega
    have hc := sub_code M ho
    simp only [SPiece.len, th_code, List.length_replicate, hc]
    rw [ifp ⟨by omega, by decide⟩]
    simp only [padOk_nop _ hc, ite_true]
    exact ih (o + 1) K [] (by omega)


theorem sub_base (o : Nat) : ((th M).sub o (o + 1)).base = BitVec.ofNat 64 o := by
  simp [Silmaril.X86.Concurrency.Cir.Tv.SThread.sub, th]

/-- One step of the pads: the first piece's explore is one `nop`. -/
theorem pexplore_cons {dom : List Nat} {f n o k : Nat} {s : State} (ho : o < M)
    (hr : s.rip = BitVec.ofNat 64 o) :
    pexplore (th M) dom (f + 1) n o (List.replicate (k + 1) (.pad 1)) s =
      (pexplore (th M) dom (f + 1) n (o + 1) (List.replicate k (.pad 1))
        { s with rip := BitVec.ofNat 64 (o + 1) }).map
        (List.map (catTr ⟨[⟨[], { s with rip := s.rip + 1 }⟩], { s with rip := s.rip + 1 }⟩)) := by
  rw [List.replicate_succ, pexplore]
  simp only [SPiece.len]
  rw [explore_nop f (sub_code M ho) (by rw [sub_base, hr])]
  simp [th]
  cases pexplore (th M) dom (f + 1) n (o + 1) (List.replicate k (.pad 1))
    { s with rip := BitVec.ofNat 64 (o + 1) } <;> simp

theorem pexplore_some {dom : List Nat} {f n : Nat} : ∀ (k o : Nat) (s : State), o + k = M →
    s.rip = BitVec.ofNat 64 o →
    (pexplore (th M) dom (f + 1) n o (List.replicate k (.pad 1)) s).isSome = true := by
  intro k
  induction k with
  | zero => intro o s _ _; rfl
  | succ k ih =>
    intro o s h hr
    rw [pexplore_cons M (by omega) hr]
    have := ih (o + 1) { s with rip := BitVec.ofNat 64 (o + 1) } (by omega) rfl
    revert this
    cases pexplore (th M) dom (f + 1) n (o + 1) (List.replicate k (.pad 1))
      { s with rip := BitVec.ofNat 64 (o + 1) } <;> simp

theorem pexplore_steps {dom : List Nat} {f n k : Nat} {s : State} (hM : 0 < M)
    (hr : s.rip = 0) {trs : List Trace}
    (hx : pexplore (th M) dom (f + 1) n 0 (List.replicate (k + 1) (.pad 1)) s = some trs) :
    ∀ tr ∈ trs, tr.steps ≠ [] := by
  rw [pexplore_cons M hM (by rw [hr]; rfl)] at hx
  intro tr htr
  revert hx
  cases pexplore (th M) dom (f + 1) n (0 + 1) (List.replicate k (.pad 1))
    { s with rip := BitVec.ofNat 64 (0 + 1) } with
  | none => simp
  | some l =>
    intro hx
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    obtain ⟨tr', _, rfl⟩ := List.mem_map.1 htr
    simp [catTr]


theorem stvRun_pads : stvRun (th M) (c M) = some [] := by
  have hi : ((th M).init.rip = (th M).base ∧ (Silmaril.X86.Concurrency.Cir.Tv.allRegs.all fun r =>
      (th M).init.read r == (⟨(c M).pro, []⟩ : Silmaril.X86.Concurrency.Cir.Tv.Cert).proRegs r)) := by
    constructor
    · rfl
    · show (Silmaril.X86.Concurrency.Cir.Tv.allRegs.all fun r =>
        (Silmaril.X86.Litmus.initCore 0 []).read r ==
          (⟨[], []⟩ : Silmaril.X86.Concurrency.Cir.Tv.Cert).proRegs r) = true
      decide
  unfold stvRun
  rw [ifp hi]
  exact pwalk_pads M M 0 _ _ (by omega)

/-- **The unrestricted `Task.piecesComplete` is false**: `2 ^ 64` one-byte `nop`s. -/
theorem piecesCompleteUnrestricted_false : ¬ PiecesCompleteUnrestricted := by
  intro H
  have hdone : DomRun (whole (th (2 ^ 64))) [] (th (2 ^ 64)).init [] (th (2 ^ 64)).init := by
    apply DomRun.done
    show (0 : Word) = 0 + BitVec.ofNat 64 (List.replicate (2 ^ 64) nopB).length
    rw [List.length_replicate]; decide
  obtain ⟨n, trs, hx, tr, htr, hm⟩ := H (th (2 ^ 64)) (c (2 ^ 64)) [] (stvRun_pads _) [] 1
    (fun n => pexplore_some (f := 0) _ _ 0 _ (by omega) rfl) [] _ hdone
  have h0 : tr.steps = [] := List.forall₂_nil_right_iff.1 hm.2
  have hk : (2 : Nat) ^ 64 = (2 ^ 64 - 1) + 1 := by omega
  have hx' : pexplore (th (2 ^ 64)) [] (0 + 1) n 0 (List.replicate ((2 ^ 64 - 1) + 1) (.pad 1))
      (th (2 ^ 64)).init = some trs := by
    rw [← hk]; exact hx
  exact pexplore_steps _ (by omega) rfl hx' tr htr h0

end Silmaril.Proofs.X86.Concurrency.Bridge.Counter
