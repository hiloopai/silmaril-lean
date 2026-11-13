module

public import Silmaril.Proofs.Wasm.Models.FXAsyncPC.Lock

/-!
# Relating the asyncify machine to its first-order version

* `RCode B c c'`: target code `c` is a suffix of a body `B fn` at position `pc` and `c'` is its
  annotation, or `c` is the handler-call check `chk :: d` that replaced an `rchk` at `pc` and `c'`
  is that check with the odd index `2 * pc + 1`;
* `RFr`: frames with related code and equal operands;
* `RRec`: a saved frame and a record that dispatches (`disp`) to related code, with equal
  operands;
* `RCfg`: pointwise related heaps and stacks, and the mode register and registers holding the
  mode, as `Mode` holds them.

The lemmas: the shape of related code (`rcode_nil`, `rcode_cons`), and the records saved at
each resume point (`rrec_even`, `rrec_odd`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncPC

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC

variable {V : Type} (B : Nat → Option (List (TIns V)))

/-- Related code. -/
def RCode (c : List (TIns V)) (c' : List (AIns V)) : Prop :=
  ∃ fn body pc, B fn = some body ∧
    ((body.drop pc = c ∧ c' = ann fn pc c) ∨
     (∃ hs d, body.drop pc = .rchk hs :: d ∧ c = .chk :: d ∧
        c' = .chk fn (2 * pc + 1) :: ann fn (pc + 1) d))

/-- Related running frames. -/
def RFr (fr : TFrame V) (a : AFrame V) : Prop := RCode B fr.code a.code ∧ fr.ops = a.ops

/-- A saved frame and a record. -/
def RRec (fr : TFrame V) (q : Rec V) : Prop :=
  fr.ops = q.ops ∧ ∃ c', disp B q.fn q.r = some c' ∧ RCode B fr.code c'

/-- The mode and the registers. -/
def RMode : Mode V → FCfg V → Prop
  | .normal, y => y.mode = 0
  | .unwind t p buf, y => y.mode = 1 ∧ y.tag = t ∧ y.pay = p ∧ List.Forall₂ (RRec B) buf y.buf
  | .rewind pend args, y => y.mode = 2 ∧ y.pay = args ∧ List.Forall₂ (RRec B) pend y.buf

/-- Related configurations. -/
def RCfg (x : TCfg V) (y : FCfg V) : Prop :=
  List.Forall₂ (Option.Rel (List.Forall₂ (RRec B))) x.heap y.heap ∧
    List.Forall₂ (RFr B) x.stack y.stack ∧ RMode B x.mode y

variable {B}

theorem drop_succ_of_cons {body c : List (TIns V)} {pc : Nat} {i : TIns V}
    (h : body.drop pc = i :: c) : body.drop (pc + 1) = c := by
  have := congrArg List.tail h
  simpa only [List.tail_drop, List.tail_cons] using this

theorem rcode_entry {fn : Nat} {body : List (TIns V)} (h : B fn = some body) :
    RCode B body (ann fn 0 body) :=
  ⟨fn, body, 0, h, .inl ⟨rfl, rfl⟩⟩

theorem rcode_nil {c' : List (AIns V)} (h : RCode B [] c') : c' = [] := by
  obtain ⟨fn, body, pc, -, ⟨-, rfl⟩ | ⟨hs, d, -, hc, -⟩⟩ := h
  · rfl
  · cases hc

theorem rcode_suffix {fn pc : Nat} {body c : List (TIns V)} (h : B fn = some body)
    (hd : body.drop pc = c) : RCode B c (ann fn pc c) :=
  ⟨fn, body, pc, h, .inl ⟨hd, rfl⟩⟩

/-- **The shape of related code.** -/
theorem rcode_cons {i : TIns V} {c : List (TIns V)} {c' : List (AIns V)}
    (h : RCode B (i :: c) c') :
    ∃ fn body pc, B fn = some body ∧ body.drop (pc + 1) = c ∧
      ((body.drop pc = i :: c ∧ c' = annI fn pc i :: ann fn (pc + 1) c) ∨
       (∃ hs, body.drop pc = .rchk hs :: c ∧ i = .chk ∧
          c' = .chk fn (2 * pc + 1) :: ann fn (pc + 1) c)) := by
  obtain ⟨fn, body, pc, hb, ⟨hd, rfl⟩ | ⟨hs, d, hd, hc, rfl⟩⟩ := h
  · exact ⟨fn, body, pc, hb, drop_succ_of_cons hd, .inl ⟨hd, rfl⟩⟩
  · cases hc
    exact ⟨fn, body, pc, hb, drop_succ_of_cons hd, .inr ⟨hs, hd, rfl, rfl⟩⟩

theorem two_mul_mod (pc : Nat) : 2 * pc % 2 = 0 := by omega
theorem two_mul_div (pc : Nat) : 2 * pc / 2 = pc := by omega
theorem two_mul_succ_mod (pc : Nat) : (2 * pc + 1) % 2 = 1 := by omega
theorem two_mul_succ_div (pc : Nat) : (2 * pc + 1) / 2 = pc := by omega

theorem disp_even {fn pc : Nat} {body : List (TIns V)} (h : B fn = some body) :
    disp B fn (2 * pc) = some (ann fn pc (body.drop pc)) := by
  simp only [disp, h, two_mul_mod, two_mul_div, ite_true]

/-- The record saved at an even resume point. -/
theorem rrec_even {fn pc : Nat} {body : List (TIns V)} (h : B fn = some body)
    (o : List (SV V)) : RRec B ⟨body.drop pc, o⟩ ⟨fn, 2 * pc, o⟩ :=
  ⟨rfl, _, disp_even h, fn, body, pc, h, .inl ⟨rfl, rfl⟩⟩

/-- The record saved at the handler-call check after an `rchk`. -/
theorem rrec_odd {fn pc : Nat} {body d : List (TIns V)} {hs : List Clause}
    (h : B fn = some body) (hd : body.drop pc = .rchk hs :: d) (o : List (SV V)) :
    RRec B ⟨.chk :: d, o⟩ ⟨fn, 2 * pc + 1, o⟩ := by
  refine ⟨rfl, .chk fn (2 * pc + 1) :: ann fn (pc + 1) d, ?_,
    fn, body, pc, h, .inr ⟨hs, d, hd, rfl, rfl⟩⟩
  simp only [disp, h, two_mul_succ_mod, two_mul_succ_div, hd]
  rfl

end Silmaril.Proofs.Wasm.Models.FXAsyncPC
