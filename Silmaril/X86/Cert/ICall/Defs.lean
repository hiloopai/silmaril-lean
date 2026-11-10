module

public import Silmaril.X86.Cert.Seg9.Thms
public import Silmaril.X86.Ext.Store
public import Silmaril.X86.Link.Env.Defs

/-!
# Indirect-call blocks for the generic certificate: definitions

`BlockKind.call K` (`Cert/Thms.lean`) names its callee in the block data. An indirect call
`call *%r` / `call *d(%base)` / `call *x(%rip)` reaches whatever function the operand holds,
so the callee cannot be in the block. The block kind of `Cert/ICall/Thms.lean` asks instead,
at the callee's entry state, for a function pointer `Link.Env.FnPtr (logic I) J Γ rip T` into a
code environment `Γ`, and for the entry obligations of the requirement `T`.

* `Cert.ICall.Req σ`: what a caller may ask of a callee: a `FnContract.Spec` and a run predicate
  `P` (as in `BlockKind.Callee`, without the proof). `Req.Valid I r`: `r.spec.TotalIn I r.P`.
  `Req.Sub r t`: `r` refines `t` (`Spec.Sub`, and a smaller run predicate under `t`'s entry).
* `Cert.ICall.logic I : Link.Contract.Logic (Req σ)`: the certificate logic as a unit-contract
  logic. `Safe n a r ctx := 0 < n → r.Valid I` (no step index, address or image dependence: a
  certificate-level callee proof is already a total run proof), `Sub := Req.Sub`.
* `Cert.ICall.Post J Γ T R Q m1`: what the call instruction's block must establish at the callee
  entry `m1`: `FnPtr (logic I) J Γ (rip m1) T`, the System V entry obligations, `T`'s
  precondition, `T`'s run predicate inside `R`, and every `T`-result in `Q`.
* `Cert.ICall.single a`: the singleton environment at the address `a`.
* `Cert.Kinds.insn9Check`, `Cert.Kinds.insn9WP`: the check and the WP of a one-instruction block
  on the open machine over `Ext9` (`Open9.decode` at the offset; `Ext9.exec` succeeds into `Q`).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86.SegVC (Isa)
open FnContract (AbiEntry Spec runsIn_mono)
open Silmaril.X86.Link.Env (Env FnPtr)

namespace Cert.ICall

variable {σ : Type}

/-- **What a caller asks of a callee**: a function spec and a run predicate for the callee's
run (`P m1 m`: the run from the entry `m1` takes steps only from states `m` with `P m1 m`). -/
structure Req (σ : Type) where
  spec : Spec σ
  P : σ → σ → Prop

/-- A requirement is met: the spec holds, with every step inside `P`. -/
def Req.Valid (I : Isa σ) (r : Req σ) : Prop := r.spec.TotalIn I r.P

/-- `r` refines `t`: `r`'s spec refines `t`'s, and under `t`'s precondition, `r`'s run
predicate is inside `t`'s. -/
structure Req.Sub (r t : Req σ) : Prop where
  spec : r.spec.Sub t.spec
  run : ∀ s m, t.spec.entry s → r.P s m → t.P s m

variable {I : Isa σ}

/-- A result of a refining spec is a result of the refined one (under its precondition). -/
theorem result_of_sub {S T : Spec σ} (h : S.Sub T) {s t : σ} (he : T.entry s)
    (res : S.Result I s t) : T.Result I s t :=
  ⟨res.silent, res.abi, res.frame.mono (fun a ha => h.footprint s a he ha), h.post s t he res.post⟩

/-- Validity is monotone along refinement. -/
theorem Req.Valid.sub {r t : Req σ} (hv : r.Valid I) (h : r.Sub t) : t.Valid I := by
  intro s hl ha he
  obtain ⟨u, hr, res⟩ := hv s hl ha (h.spec.entry s he)
  exact ⟨u, runsIn_mono (fun m hm => h.run s m he hm) hr, result_of_sub h.spec he res⟩

/-- **The certificate logic as a unit-contract logic.** A callee is safe (for any positive
index) when its requirement is valid; refinement is `Req.Sub`. -/
def logic (I : Isa σ) : Silmaril.X86.Link.Contract.Logic (Req σ) where
  Safe n _ r _ := 0 < n → r.Valid I
  zero _ _ _ h := absurd h (Nat.lt_irrefl 0)
  mono h _ := h (Nat.succ_pos _)
  frame _ h := h
  Sub := Req.Sub
  sub hs h hn := (h hn).sub hs

/-- The requirement of a callee (forgetting its proof). -/
def Req.ofCallee (c : BlockKind.Callee I) : Req σ := ⟨c.contract.toSpec, c.P⟩

/-- A valid requirement as a callee. -/
def Req.callee (r : Req σ) (h : r.Valid I) : BlockKind.Callee I :=
  ⟨⟨r.spec, h.total⟩, r.P, h⟩

/-- **What the call instruction's block establishes at the callee entry `m1`**: the address
reached is a function pointer of `Γ` for `T`, the System V entry obligations, `T`'s
precondition, `T`'s run inside `R`, and every `T`-result in `Q`. -/
def Post {Code : Type} (J : Env Code → Code → Req σ) (Γ : Env Code) (T : Req σ)
    (R Q : σ → Prop) (m1 : σ) : Prop :=
  FnPtr (logic I) J Γ (I.core m1).rip T ∧ AbiEntry (I.core m1) (I.mem m1) ∧ T.spec.entry m1 ∧
    (∀ m, T.P m1 m → R m) ∧ ∀ t, T.spec.Result I m1 t → Q t

/-- The singleton environment: one callee at one address. -/
def single (a : Nat) : Env Unit := fun a' _ => a' = a

end Cert.ICall

namespace Cert.Kinds

/-- The check of a one-instruction block: `Open9.decode` reads `b` at `o`, inside the code. -/
def insn9Check (code : List Byte) (o : Nat) (b : Ext9.Instr × Nat) : Bool :=
  decide (Open9.decode ((code.drop o).take b.2) = some b) && decide (o + b.2 ≤ code.length)

/-- The WP of a one-instruction block: the instruction executes into `Q`. -/
def insn9WP (b : Ext9.Instr × Nat) (s : MState) (Q : MState → Prop) : Prop :=
  ∃ c mem, Ext9.exec b.1 s.core s.memory b.2 = .ok c mem ∧ Q ⟨c, mem⟩

end Cert.Kinds

end Silmaril.X86
