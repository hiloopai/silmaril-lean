module

public import Silmaril.X86.Decompile.Region

/-!
# Static control-flow successors

`Decoded.edges` lists, for one decoded instruction, every place control can go
after it. The model has no indirect jump: the only instructions that write RIP
with anything other than the fall-through address are `jmp`, `jmp8`, `jcc`,
`jcc8`, `call` and `ret`, and of those only `ret` has a target the bytes do not
name. So the list is complete, and `Decoded.edges_sound` proves it: every
successor RIP that `Ext.exec` can produce is an edge target, unless the
instruction was `ret`.

## Matching the semantics exactly

`Ext.exec` computes `next = s.rip + BitVec.ofNat 64 i.length` and a relative
target as `next + rel.signExtend 64`, both in `BitVec 64`, so both wrap at
`2^64`. `Decoded.next` and `Decoded.relTarget` reproduce that arithmetic and
then take `toNat`; they are *not* `d.addr + d.size` and `d.addr + d.size + rel`
as integers. For a region that ends below `2^64` the two agree
(`next_eq_of_lt`), which is what the examples use, but the soundness theorem
holds without that side condition.

## The shape of the soundness statement

Two shapes were available: a four-way disjunction naming each edge kind, and a
predicate `Decoded.NextRip` saying "some edge admits this successor". The
second is used here. It is the weaker-looking but more usable form: the
checker's obligations are all of the form "every edge target satisfies P", so
callers want "the successor is *some* edge target", and the edge kind is
recovered by `cases` on the edge when it is wanted. `Edge.ret` and `Edge.halt`
admit no successor: `ud2` does not retire at all, and the target of a `ret` is
a stack value, not a static datum.
-/

@[expose] public section

namespace Silmaril.X86.Decompile

open Silmaril.X86 (State Word)
open Silmaril.Process (Memory)

/-! ## Edges -/

/-- Where control can go after one instruction. -/
inductive Edge where
  /-- To the next instruction in address order. -/
  | fallthrough (target : Nat)
  /-- To the target of an unconditional jump. -/
  | jump (target : Nat)
  /-- To the target of a conditional jump, when it is taken. -/
  | branch (target : Nat)
  /-- To the target of a call. -/
  | call (target : Nat)
  /-- To the address on top of the stack, which the bytes do not name. -/
  | ret
  /-- Nowhere: the instruction traps. -/
  | halt
  deriving DecidableEq, Repr

/-- The address of the next instruction, as the machine computes it: the sum of
address and size taken modulo `2^64`. -/
def Decoded.next (d : Decoded) : Nat := (BitVec.ofNat 64 (d.addr + d.size)).toNat

/-- The target of a RIP-relative displacement, as the machine computes it: the
address of the next instruction plus the sign-extended displacement, modulo
`2^64`. -/
def Decoded.relTarget (d : Decoded) (rel : BitVec 64) : Nat :=
  (BitVec.ofNat 64 (d.addr + d.size) + rel).toNat

/-- Below `2^64` the next address is the plain sum. -/
theorem Decoded.next_eq_of_lt {d : Decoded} (h : d.addr + d.size < 2 ^ 64) :
    d.next = d.addr + d.size := by
  simp only [Decoded.next, BitVec.toNat_ofNat]
  omega

/-- Where control can go after this instruction. -/
def Decoded.edges (d : Decoded) : List Edge :=
  match d.instr with
  | .jmp rel => [.jump (d.relTarget (rel.signExtend 64))]
  | .jmp8 rel => [.jump (d.relTarget (rel.signExtend 64))]
  | .jcc _ rel => [.branch (d.relTarget (rel.signExtend 64)), .fallthrough d.next]
  | .jcc8 _ rel => [.branch (d.relTarget (rel.signExtend 64)), .fallthrough d.next]
  | .call rel => [.call (d.relTarget (rel.signExtend 64)), .fallthrough d.next]
  | .ret => [.ret]
  | .ud2 => [.halt]
  | _ => [.fallthrough d.next]

/-- The successor RIP an edge admits. `ret` and `halt` admit none: `ud2` does
not retire, and the target of a `ret` is not a static datum. -/
def Edge.Target : Edge → Nat → Prop
  | .fallthrough t, a => a = t
  | .jump t, a => a = t
  | .branch t, a => a = t
  | .call t, a => a = t
  | .ret, _ => False
  | .halt, _ => False

instance (e : Edge) (a : Nat) : Decidable (e.Target a) := by
  cases e <;> unfold Edge.Target <;> infer_instance

/-- `a` is a statically admitted successor RIP of `d`. -/
def Decoded.NextRip (d : Decoded) (a : Nat) : Prop := ∃ e ∈ d.edges, e.Target a

instance (d : Decoded) (a : Nat) : Decidable (d.NextRip a) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Classifying instructions -/

/-- The instructions whose `Ext.exec` ends in `Ext.retire`: everything other
than `jmp`, `jmp8`, `jcc`, `jcc8`, `call`, `ret` and `ud2`. -/
def retiring : Ext.Instr → Bool
  | .jmp _ | .jmp8 _ | .jcc _ _ | .jcc8 _ _ | .call _ | .ret | .ud2 => false
  | _ => true

/-- `call` and `ret`: the instructions that leave a function in the ordinary
calling convention. -/
def interprocedural : Ext.Instr → Bool
  | .call _ | .ret => true
  | _ => false

/-- The multi-byte NOP paddings, which is what an assembler puts between
functions. -/
def isNop : Ext.Instr → Bool
  | .nop _ => true
  | _ => false

/-! ## Soundness -/

/-- Whatever `Ext.retire` is given, a retirement sets RIP to the address it was
told to. -/
theorem rip_of_retire {next : Word} {o : Option (State × Memory)} {core' : State}
    {memory' : Memory} (h : Ext.retire next o = .ok core' memory') : core'.rip = next := by
  unfold Ext.retire at h
  split at h
  · cases h; rfl
  · cases h

/-- An instruction that is not a jump, a call, a `ret` or `ud2` retires to the
following address. -/
theorem exec_retire_rip {i : Ext.Instr} (hi : retiring i = true) {s core' : State}
    {memory memory' : Memory} (h : Ext.exec i s memory = .ok core' memory') :
    core'.rip = s.rip + BitVec.ofNat 64 i.length := by
  unfold Ext.exec at h
  split at h <;>
    first
      | exact Bool.noConfusion hi
      | repeat' (first | exact rip_of_retire h | cases h | split at h | simp_all)

/-- A retiring instruction has exactly one edge, to the following address. -/
theorem Decoded.edges_of_retiring {d : Decoded} (h : retiring d.instr = true) :
    d.edges = [Edge.fallthrough d.next] := by
  obtain ⟨addr, instr, size⟩ := d
  cases instr <;> first | rfl | exact Bool.noConfusion h

/-- `Edge.ret` is listed exactly for `ret`. -/
theorem Decoded.mem_edges_ret_iff {d : Decoded} : Edge.ret ∈ d.edges ↔ d.instr = .ret := by
  obtain ⟨addr, instr, size⟩ := d
  cases instr <;> simp [Decoded.edges]

/-- The address after the instruction, in the form `Ext.exec` produces it. -/
theorem rip_add_length {d : Decoded} {s : State} (hrip : s.rip.toNat = d.addr)
    (hlen : d.size = (Ext.encode d.instr).length) :
    s.rip + BitVec.ofNat 64 d.instr.length = BitVec.ofNat 64 (d.addr + d.size) := by
  have hL : d.instr.length = d.size := by rw [Ext.Instr.length, ← hlen]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hrip, hL]
  omega

/-- A retiring instruction goes to its fall-through address. -/
theorem Decoded.next_of_retiring {d : Decoded} {s core' : State} {memory memory' : Memory}
    (hi : retiring d.instr = true) (hrip : s.rip.toNat = d.addr)
    (hlen : d.size = (Ext.encode d.instr).length)
    (h : Ext.exec d.instr s memory = .ok core' memory') : core'.rip.toNat = d.next := by
  rw [exec_retire_rip hi h, rip_add_length hrip hlen, Decoded.next]

/-! ### The control-flow instructions, one by one

Each is `rfl`: `Ext.exec` applied to a literal constructor reduces to the
result below. Having them as equations keeps `edges_sound` free of `split`s
over the forty-constructor `match`. -/

/-- `jmp rel32` goes to the next address plus the sign-extended displacement. -/
theorem exec_jmp (rel : BitVec 32) (s : State) (memory : Memory) :
    Ext.exec (.jmp rel) s memory =
      (let next := s.rip + BitVec.ofNat 64 (Ext.Instr.jmp rel).length
       .ok { s with rip := next + rel.signExtend 64 } memory) := rfl

/-- `jmp rel8` goes to the next address plus the sign-extended displacement. -/
theorem exec_jmp8 (rel : BitVec 8) (s : State) (memory : Memory) :
    Ext.exec (.jmp8 rel) s memory =
      (let next := s.rip + BitVec.ofNat 64 (Ext.Instr.jmp8 rel).length
       .ok { s with rip := next + rel.signExtend 64 } memory) := rfl

/-- `jcc rel32` goes to the displacement when taken and to the next address
when not; an undefined condition is not a retirement. -/
theorem exec_jcc (c : Ext.Cond) (rel : BitVec 32) (s : State) (memory : Memory) :
    Ext.exec (.jcc c rel) s memory =
      (let next := s.rip + BitVec.ofNat 64 (Ext.Instr.jcc c rel).length
       match c.eval s.flags with
       | none => .undefinedCondition c
       | some true => .ok { s with rip := next + rel.signExtend 64 } memory
       | some false => .ok { s with rip := next } memory) := rfl

/-- `jcc rel8`, as `exec_jcc`. -/
theorem exec_jcc8 (c : Ext.Cond) (rel : BitVec 8) (s : State) (memory : Memory) :
    Ext.exec (.jcc8 c rel) s memory =
      (let next := s.rip + BitVec.ofNat 64 (Ext.Instr.jcc8 c rel).length
       match c.eval s.flags with
       | none => .undefinedCondition c
       | some true => .ok { s with rip := next + rel.signExtend 64 } memory
       | some false => .ok { s with rip := next } memory) := rfl

/-- `call rel32` pushes the return address and goes to the displacement. -/
theorem exec_call (rel : BitVec 32) (s : State) (memory : Memory) :
    Ext.exec (.call rel) s memory =
      (let next := s.rip + BitVec.ofNat 64 (Ext.Instr.call rel).length
       match X86.pushWord s memory next with
       | none => .dataFault
       | some (t, m) => .ok { t with rip := next + rel.signExtend 64 } m) := rfl

/-- `ud2` traps and never retires. -/
theorem exec_ud2 (s : State) (memory : Memory) : Ext.exec .ud2 s memory = .trap := rfl

/-- **Every successor RIP the semantics can produce is listed by `edges`.**
The one exception is `ret`, whose target is the value on top of the stack. -/
theorem Decoded.edges_sound {d : Decoded} {s core' : State} {memory memory' : Memory}
    (hrip : s.rip.toNat = d.addr) (hlen : d.size = (Ext.encode d.instr).length)
    (h : Ext.exec d.instr s memory = .ok core' memory') :
    d.NextRip core'.rip.toNat ∨ Edge.ret ∈ d.edges := by
  by_cases hr : retiring d.instr = true
  · exact Or.inl ⟨.fallthrough d.next, by rw [edges_of_retiring hr]; exact List.Mem.head _,
      Decoded.next_of_retiring hr hrip hlen h⟩
  · have hadd := rip_add_length hrip hlen
    obtain ⟨addr, instr, size⟩ := d
    dsimp only at hr hadd h ⊢
    cases instr
    case jmp rel =>
      rw [exec_jmp] at h
      cases h
      refine Or.inl ⟨.jump _, List.Mem.head _, ?_⟩
      show (s.rip + BitVec.ofNat 64 (Ext.Instr.jmp rel).length + rel.signExtend 64).toNat = _
      rw [hadd]
      rfl
    case jmp8 rel =>
      rw [exec_jmp8] at h
      cases h
      refine Or.inl ⟨.jump _, List.Mem.head _, ?_⟩
      show (s.rip + BitVec.ofNat 64 (Ext.Instr.jmp8 rel).length + rel.signExtend 64).toNat = _
      rw [hadd]
      rfl
    case jcc c rel =>
      rw [exec_jcc] at h
      cases hv : Ext.Cond.eval s.flags c with
      | none => simp only [hv] at h; cases h
      | some v =>
        simp only [hv] at h
        cases v
        · cases h
          refine Or.inl ⟨.fallthrough _, List.Mem.tail _ (List.Mem.head _), ?_⟩
          show (s.rip + BitVec.ofNat 64 (Ext.Instr.jcc c rel).length).toNat = _
          rw [hadd]
          rfl
        · cases h
          refine Or.inl ⟨.branch _, List.Mem.head _, ?_⟩
          show (s.rip + BitVec.ofNat 64 (Ext.Instr.jcc c rel).length + rel.signExtend 64).toNat = _
          rw [hadd]
          rfl
    case jcc8 c rel =>
      rw [exec_jcc8] at h
      cases hv : Ext.Cond.eval s.flags c with
      | none => simp only [hv] at h; cases h
      | some v =>
        simp only [hv] at h
        cases v
        · cases h
          refine Or.inl ⟨.fallthrough _, List.Mem.tail _ (List.Mem.head _), ?_⟩
          show (s.rip + BitVec.ofNat 64 (Ext.Instr.jcc8 c rel).length).toNat = _
          rw [hadd]
          rfl
        · cases h
          refine Or.inl ⟨.branch _, List.Mem.head _, ?_⟩
          show (s.rip + BitVec.ofNat 64 (Ext.Instr.jcc8 c rel).length +
            rel.signExtend 64).toNat = _
          rw [hadd]
          rfl
    case call rel =>
      rw [exec_call] at h
      cases hp : X86.pushWord s memory (s.rip + BitVec.ofNat 64 (Ext.Instr.call rel).length) with
      | none => simp only [hp] at h; cases h
      | some r =>
        obtain ⟨t, m⟩ := r
        simp only [hp] at h
        cases h
        refine Or.inl ⟨.call _, List.Mem.head _, ?_⟩
        show (s.rip + BitVec.ofNat 64 (Ext.Instr.call rel).length + rel.signExtend 64).toNat = _
        rw [hadd]
        rfl
    case ret => exact Or.inr (List.Mem.head _)
    case ud2 => rw [exec_ud2] at h; cases h
    all_goals exact absurd rfl hr

end Silmaril.X86.Decompile
