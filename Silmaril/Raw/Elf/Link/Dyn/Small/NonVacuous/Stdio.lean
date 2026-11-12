module

public import Silmaril.Elf.Link.Dyn.Stdio.Contracts
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # The stdio contracts are satisfiable from every state

`stdioNamed_total`: for every name and every state, the named stdio contracts allow some
outcome. This is what makes a `Must` over a world with these contracts say something about
real runs (`proc_progress` needs it), and it checks that the trusted contracts do not assume
the impossible of glibc: under each precondition there is a state with the promised
postcondition (`scanf`: the two `int`s stored, `rax = 2`; `printf`: the text appended).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small.NonVacuous

open Silmaril.X86 (Word Byte Reg State)
open Silmaril.Process (Memory Access ByteMemory)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Stdio

/-- The core a library call returns with: `rip` at the return address, `rsp` popped, `rax`. -/
def retCore (s : PState) (rax : Word) : State :=
  { ((s.m.core.write .rsp (s.m.core.read .rsp + 8#64)).write .rax rax) with
    rip := retOf s.m.core s.m.memory }

/-- The state a library call returns to, with memory bytes `bytes` and library state `g`. -/
def retTo (s : PState) (rax : Word) (bytes : ByteMemory) (g : Ghost) : PState :=
  ⟨⟨retCore s rax, ⟨s.m.memory.regions, bytes⟩⟩, g⟩

theorem retCore_read (s : PState) (rax : Word) (r : Reg) :
    (retCore s rax).read r =
      if r = .rax then rax else if r = .rsp then s.m.core.read .rsp + 8#64 else s.m.core.read r := by
  unfold retCore
  rw [State.read_mk_regs, State.read_write, State.read_write]

theorem retTo_abi (s : PState) (rax : Word) (bytes : ByteMemory) (g : Ghost) :
    AbiReturn s.m.core s.m.memory (retTo s rax bytes g).m.core := by
  refine ⟨rfl, by simp [retTo, retCore_read], fun r hr => ?_⟩
  rw [Silmaril.X86.sysv64_calleeSaved] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [retTo, retCore_read]

theorem retTo_fs (s : PState) (rax : Word) (bytes : ByteMemory) (g : Ghost) :
    (retTo s rax bytes g).m.core.fsBase = s.m.core.fsBase := rfl

theorem retTo_permits (s : PState) (rax : Word) (bytes : ByteMemory) (g : Ghost) (acc : Access)
    (a : Nat) : (retTo s rax bytes g).m.memory.permits acc a = s.m.memory.permits acc a := rfl

theorem retTo_keeps {s : PState} {rax : Word} {bytes : ByteMemory} {g : Ghost} {P : Nat → Prop}
    (h : ∀ a, P a → bytes.get? a = s.m.memory.bytes.get? a) :
    Keeps P s.m.memory (retTo s rax bytes g).m.memory :=
  fun a ha => ⟨h a ha, fun _ => rfl⟩

/-! ## `printf` -/

theorem printf_total (fr vr : Reg) (kept : Nat → Prop) (rel : Bool) (s : PState) :
    ∃ r, printfStepWith fr vr kept rel s r := by
  refine ⟨.ok (retTo s 0 s.m.memory.bytes
    { s.g with out := s.g.out ++ decStr (low32 (s.m.core.read vr)).toInt ++ [10], done := none }),
    fun _ => ⟨_, rfl, ?_⟩⟩
  exact ⟨⟨retTo_abi _ _ _ _, rfl, retTo_keeps (fun _ _ => rfl), fun _ h => h.elim,
    retTo_keeps (fun _ _ => rfl), fun _ _ _ _ => rfl⟩, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-! ## `scanf` -/

theorem le32_length (x : Int) : (le32 x).length = 4 := rfl

/-- The bytes after storing `x` at `p` and `y` at `q`. -/
def store2 (m : ByteMemory) (p q : Nat) (x y : Int) : ByteMemory :=
  Memory.install (Memory.install m p (le32 x)) q (le32 y)

theorem store2_outside {m : ByteMemory} {p q a : Nat} {x y : Int} (hp : a < p ∨ p + 4 ≤ a)
    (hq : a < q ∨ q + 4 ≤ a) : (store2 m p q x y).get? a = m.get? a := by
  unfold store2
  rw [Memory.install_outside _ _ _ _ (by rw [le32_length]; exact hq),
    Memory.install_outside _ _ _ _ (by rw [le32_length]; exact hp)]

theorem store2_q {m : ByteMemory} {p q k : Nat} {x y : Int} (hk : k < 4) :
    (store2 m p q x y).get? (q + k) = (le32 y)[k]? := by
  unfold store2
  rw [Memory.install_get _ _ _ _ (by rw [le32_length]; exact hk), List.getElem?_eq_getElem]

theorem store2_p {m : ByteMemory} {p q k : Nat} {x y : Int} (hk : k < 4)
    (hd : p + 4 ≤ q ∨ q + 4 ≤ p) : (store2 m p q x y).get? (p + k) = (le32 x)[k]? := by
  unfold store2
  rw [Memory.install_outside _ _ _ _ (by rw [le32_length]; omega),
    Memory.install_get _ _ _ _ (by rw [le32_length]; exact hk), List.getElem?_eq_getElem]

theorem le32_get? {x : Int} {k : Nat} (hk : k < 4) : ((le32 x)[k]?).isSome := by
  simp [le32_length, hk]

theorem store2_read {mem : Memory} {bytes : ByteMemory} {a : Nat} {l : List Byte}
    (hl : l.length = 4) (hp : mem.Permitted .read a 4)
    (hb : ∀ k < 4, bytes.get? (a + k) = l[k]?) :
    (Memory.mk mem.regions bytes).readBytes a 4 = some l := by
  rw [Memory.Permitted, Memory.checkSpan_iff] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have := readWith_of_points (mem := Memory.mk mem.regions bytes) (acc := .read) (l := l) (a := a)
    (by rw [hl]; exact h2) h1 (fun k hk => ⟨by rw [hl] at hk; exact h3 k hk, by
      rw [hl] at hk; rw [hb k hk, List.getElem?_eq_getElem]⟩)
  rw [hl] at this
  exact this

theorem scanf_total (kept : Nat → Prop) (s : PState) : ∃ r, scanfStep kept s r := by
  by_cases hpre : AbiEntry s.m.core s.m.memory ∧ CStr s.m.memory (s.m.core.read .rdi) fmtDD ∧
      s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 4 ∧
      s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 4 ∧
      s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 4 ∧
      s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 4 ∧
      ((s.m.core.read .rsi).toNat + 4 ≤ (s.m.core.read .rdx).toNat ∨
        (s.m.core.read .rdx).toNat + 4 ≤ (s.m.core.read .rsi).toNat)
  swap
  · exact ⟨.stop, fun h => absurd h hpre⟩
  obtain ⟨-, -, -, -, hrp, hrq, hd⟩ := hpre
  -- the frame of a store of `x`, `y`
  have frame : ∀ (x y : Int) (rax : Word) (g : Ghost),
      StdioFrame kept s (retTo s rax (store2 s.m.memory.bytes (s.m.core.read .rsi).toNat
        (s.m.core.read .rdx).toNat x y) g)
        (fun a => In4 (s.m.core.read .rsi) a ∨ In4 (s.m.core.read .rdx) a) := by
    intro x y rax g
    have hout : ∀ a, ¬ (In4 (s.m.core.read .rsi) a ∨ In4 (s.m.core.read .rdx) a) →
        (store2 s.m.memory.bytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat x y).get? a =
          s.m.memory.bytes.get? a := by
      intro a h
      simp only [In4, not_or, not_and, Nat.not_lt] at h
      exact store2_outside (by omega) (by omega)
    refine ⟨retTo_abi _ _ _ _, rfl, retTo_keeps fun a h => hout a h.2, fun a h => ⟨?_, fun _ => rfl⟩,
      retTo_keeps fun a h => hout a h.2, fun _ _ _ _ => rfl⟩
    show (store2 _ _ _ x y).get? a |>.isSome
    rcases h with h | h <;> simp only [In4] at h
    · rw [show a = (s.m.core.read .rsi).toNat + (a - (s.m.core.read .rsi).toNat) by omega,
        store2_p (by omega) hd]
      exact le32_get? (by omega)
    · rw [show a = (s.m.core.read .rdx).toNat + (a - (s.m.core.read .rdx).toNat) by omega, store2_q (by omega)]
      exact le32_get? (by omega)
  cases hsc : scanDD s.g.inp with
  | ub =>
    refine ⟨.ok (retTo s 0 s.m.memory.bytes s.g), fun _ => ⟨_, rfl, ?_⟩⟩
    simp only [hsc]
  | fail =>
    refine ⟨.ok (retTo s 0 (store2 s.m.memory.bytes (s.m.core.read .rsi).toNat
      (s.m.core.read .rdx).toNat 0 0) { s.g with done := none }), fun _ => ⟨_, rfl, ?_⟩⟩
    simp only [hsc]
    refine ⟨frame 0 0 0 _, ?_, rfl, rfl, rfl, rfl⟩
    simp [retTo, retCore_read, low32]
  | ok a b rest =>
    refine ⟨.ok (retTo s 2 (store2 s.m.memory.bytes (s.m.core.read .rsi).toNat
      (s.m.core.read .rdx).toNat a b) { s.g with inp := rest }), fun _ => ⟨_, rfl, ?_⟩⟩
    simp only [hsc]
    refine ⟨frame a b 2 _, by simp [retTo, retCore_read, low32], rfl, ?_, ?_⟩
    · exact store2_read (le32_length a) hrp fun k hk => store2_p hk hd
    · exact store2_read (le32_length b) hrq fun k hk => store2_q hk

/-- **The named stdio contracts always allow an outcome.** -/
theorem stdioNamed_total (kept : Nat → Prop) (rel : Bool) :
    ∀ n s, ∃ r, stdioNamed kept rel n s r := by
  intro n s
  unfold stdioNamed
  split_ifs
  · exact scanf_total kept s
  · exact printf_total .rdi .rsi kept rel s
  · exact printf_total .rsi .rdx kept rel s
  · exact ⟨.stop, trivial⟩
  · exact ⟨.stop, rfl⟩

end Silmaril.Elf.Link.Dyn.Small.NonVacuous
