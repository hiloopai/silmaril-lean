module

public import Silmaril.Proofs.Wasm.Logic.Instr.Memory

/-!
# Instruction rules: tables and indirect calls

Rules for every table instruction of Core 3.0, over any table of the module and
any address type, in both readings (`Wp m`) and every profile: `table.get`,
`table.set` (each in bounds and out of bounds), `table.size`, `table.grow`
(both outcomes, no progress premise), `table.fill`, `table.copy` (both
directions) and `table.init` one step at a time (trap, zero, successor),
`elem.drop`; and the unfolding rules of `call_indirect` and
`return_call_indirect` (`table.get`, `ref.cast` to the non-null type, then
`call_ref`/`return_call_ref`).

A Silmaril addition; the step rules are silmaril-lean's
`Silmaril/Wasm/Execution/Core/Step/Table.lean` and the `call_indirect` rules of
`Silmaril.Wasm.Execution.Core.Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
variable {x : TableIdx} {a : AddrType} {i : BitVec a.intType.width} {ta : Nat} {ti : TableInst}

/-- `famOf` of a concrete instruction. -/
local macro "fam_ok" : term => `(by simp [famOf])

/-- Close a `Det.Head` case whose instruction is not the one at hand. -/
local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

/-! ## Get, set, size -/

/-- **`table.get`**, in bounds. -/
theorem Wp.tableGet {r : Ref} (ht : s.table? f x = some (ta, ti)) (hr : ti.refs[i.toNat]? = some r)
    (h : Wp m P host s f (vals (us ++ [.ref r]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.tableGet x) :: rest) Q :=
  Wp.detVals (res := [.ref r]) fam_ok (by trivial) (.table (.getVal ht hr)) h

/-- **`table.get`**, out of bounds: traps. -/
theorem Wp.tableGet_oob (ht : s.table? f x = some (ta, ti)) (hb : ti.refs.length ≤ i.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i]) ++ .plain (.tableGet x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.table (.getOob ht hb)) hq

/-- **`table.set`**, in bounds. -/
theorem Wp.tableSet {r : Ref} (ht : s.table? f x = some (ta, ti)) (hb : i.toNat < ti.refs.length)
    (h : Wp m P host (s.setTable ta { ti with refs := ti.refs.set i.toNat r }) f
      (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .ref r]) ++ .plain (.tableSet x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.table (.setVal ht hb)) (by simpa using h)

/-- **`table.set`**, out of bounds: traps. -/
theorem Wp.tableSet_oob {r : Ref} (ht : s.table? f x = some (ta, ti))
    (hb : ti.refs.length ≤ i.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .ref r]) ++ .plain (.tableSet x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.table (.setOob (r := r) ht hb)) hq

/-- **`table.size`.** -/
theorem Wp.tableSize (ht : s.table? f x = some (ta, ti))
    (h : Wp m P host s f (vals (us ++ [addrVal ti.type.address (BitVec.ofNat _ ti.refs.length)]) ++
      rest) Q) :
    Wp m P host s f (vals us ++ .plain (.tableSize x) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (rest := rest)
    (res := [addrVal ti.type.address (BitVec.ofNat _ ti.refs.length)]) fam_ok (by trivial)
    (.table (.size ht)) h

/-! ## Growth -/

theorem args_of_last {args : List Val} {e e' : Admin} {l : List Admin}
    (h : vals args ++ [e] = l ++ [e']) : vals args = l ∧ e = e' := by
  have h₁ := List.append_inj' h rfl
  exact ⟨h₁.1, List.singleton_inj.mp h₁.2⟩

theorem table_tableGrow {args : List Val} {c₀ : Config H}
    (h : TableStep P ⟨s, f, vals args ++ [.plain (.tableGrow x)]⟩ c₀) :
    ∃ (a : AddrType) (n : BitVec a.intType.width) (r : Ref) (ta : Nat) (ti : TableInst),
      args = [.ref r, addrVal a n] ∧ s.table? f x = some (ta, ti) ∧
      ((∃ ti', ti.grow? n.toNat r = some ti' ∧ P.growMaySucceed .table ta ti.refs.length n.toNat ∧
          c₀ = ⟨s.setTable ta ti', f, [aconst a (BitVec.ofNat _ ti.refs.length)]⟩) ∨
        ((P.growMayFail .table ta ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none) ∧
          c₀ = ⟨s, f, [aconst a (BitVec.allOnes _)]⟩)) := by
  generalize hl : vals args ++ [.plain (.tableGrow x)] = l at h
  cases h
  case growSucceed x' a' n' r' ta' ti' ti'' hg hp ht =>
    obtain ⟨hv, hx⟩ := args_of_last (l := [.ref r', aconst a' n']) hl
    obtain rfl : x' = x := by simpa using hx.symm
    have hargs : args = [.ref r', addrVal a' n'] := SingleThreaded.Det.vals_inj.mp hv
    exact ⟨a', n', r', ta', ti', hargs, ht, .inl ⟨ti'', hg, hp, rfl⟩⟩
  case growFail x' a' n' r' ta' ti' hp ht =>
    obtain ⟨hv, hx⟩ := args_of_last (l := [.ref r', aconst a' n']) hl
    obtain rfl : x' = x := by simpa using hx.symm
    have hargs : args = [.ref r', addrVal a' n'] := SingleThreaded.Det.vals_inj.mp hv
    exact ⟨a', n', r', ta', ti', hargs, ht, .inr ⟨hp, rfl⟩⟩
  all_goals
    have h₂ := congrArg List.getLast? hl
    simp [vals, Val.toAdmin] at h₂

/-- **`table.grow`**, in every profile: both outcomes the profile allows must be
covered. -/
theorem Wp.tableGrow {n : BitVec a.intType.width} {r : Ref} (ht : s.table? f x = some (ta, ti))
    (hsucc : ∀ ti', ti.grow? n.toNat r = some ti' →
      P.growMaySucceed .table ta ti.refs.length n.toNat →
      Wp m P host (s.setTable ta ti') f
        (vals (us ++ [addrVal a (BitVec.ofNat _ ti.refs.length)]) ++ rest) Q)
    (hfail : P.growMayFail .table ta ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none →
      Wp m P host s f (vals (us ++ [addrVal a (BitVec.allOnes _)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref r, addrVal a n]) ++ .plain (.tableGrow x) :: rest) Q := by
  have hp : ∃ c₀, Head P s f [.ref r, addrVal a n] (.plain (.tableGrow x)) c₀ := by
    rcases grow_progress P .table ta ti.refs.length n.toNat (ti.grow? n.toNat r) with
      ⟨ti', hg, hs⟩ | hf
    · exact ⟨_, .table (.growSucceed ht hg hs)⟩
    · exact ⟨_, .table (.growFail ht hf)⟩
  refine Wp.fam fam_ok hp fun c₀ hh => ?_
  obtain ⟨a', n', r', ta', ti', hargs, ht', hres⟩ := table_tableGrow (hh.fam_inv fam_ok)
  have hargs' : Val.ref r = .ref r' ∧ addrVal a n = addrVal a' n' := by simpa using hargs
  obtain ⟨hr, hn⟩ := hargs'
  obtain rfl : r' = r := by injection hr with h; exact h.symm
  obtain ⟨rfl, hn'⟩ := addr_arg_inj hn.symm
  obtain rfl := eq_of_heq hn'
  obtain ⟨rfl, rfl⟩ : ta' = ta ∧ ti' = ti := by simpa [ht] using ht'.symm
  rcases hres with ⟨ti'', hg, hs, rfl⟩ | ⟨hf, rfl⟩
  · simpa using hsucc ti'' hg hs
  · simpa using hfail hf

/-! ## Bulk table operations, one step at a time -/

section Bulk

variable {v : Val} {n : BitVec a.intType.width}

/-- **`table.fill`** out of bounds: traps. -/
theorem Wp.tableFill_oob (ht : s.table? f x = some (ta, ti))
    (hb : ti.refs.length < i.toNat + n.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a n]) ++ .plain (.tableFill x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.table (.fillOob ht hb)) hq

/-- **`table.fill`** of zero entries (in bounds). -/
theorem Wp.tableFill_zero (ht : s.table? f x = some (ta, ti)) (hb : i.toNat ≤ ti.refs.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a 0]) ++ .plain (.tableFill x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.table (.fillZero ht hb)) (by simpa using h)

/-- **`table.fill`** of `n ≠ 0` entries (in bounds): set one entry, fill the rest. -/
theorem Wp.tableFill_succ (ht : s.table? f x = some (ta, ti))
    (hb : i.toNat + n.toNat ≤ ti.refs.length) (hn : n ≠ 0)
    (h : Wp m P host s f (vals (us ++ [addrVal a i, v]) ++ .plain (.tableSet x) ::
      (vals [addrVal a (i + 1), v, addrVal a (n - 1)] ++ .plain (.tableFill x) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, v, addrVal a n]) ++ .plain (.tableFill x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.table (.fillSucc ht hb hn)) (by simpa using h)

variable {x₁ x₂ : TableIdx} {a₁ a₂ a' : AddrType} {i₁ : BitVec a₁.intType.width}
  {i₂ : BitVec a₂.intType.width} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TableInst}

/-- **`table.copy`** out of bounds: traps. -/
theorem Wp.tableCopy_oob {n : BitVec a'.intType.width} (h₁ : s.table? f x₁ = some (ta₁, ti₁))
    (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : ti₁.refs.length < i₁.toNat + n.toNat ∨ ti₂.refs.length < i₂.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.tableCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.table (.copyOob h₁ h₂ hb)) hq

/-- **`table.copy`** of zero entries (in bounds). -/
theorem Wp.tableCopy_zero (h₁ : s.table? f x₁ = some (ta₁, ti₁))
    (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : i₁.toNat ≤ ti₁.refs.length ∧ i₂.toNat ≤ ti₂.refs.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' 0]) ++
      .plain (.tableCopy x₁ x₂) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.table (.copyZero h₁ h₂ hb)) (by simpa using h)

/-- **`table.copy`** forwards: copy the first entry, then the rest. -/
theorem Wp.tableCopy_le {n : BitVec a'.intType.width} (h₁ : s.table? f x₁ = some (ta₁, ti₁))
    (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hn : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (h : Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂]) ++ .plain (.tableGet x₂) ::
      .plain (.tableSet x₁) :: (vals [addrVal a₁ (i₁ + 1), addrVal a₂ (i₂ + 1), addrVal a' (n - 1)] ++
        .plain (.tableCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.tableCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.table (.copyLe h₁ h₂ hb hn hle)) (by simpa using h)

/-- **`table.copy`** backwards: copy the last entry, then the rest. -/
theorem Wp.tableCopy_gt {n : BitVec a'.intType.width} (h₁ : s.table? f x₁ = some (ta₁, ti₁))
    (h₂ : s.table? f x₂ = some (ta₂, ti₂))
    (hb : i₁.toNat + n.toNat ≤ ti₁.refs.length ∧ i₂.toNat + n.toNat ≤ ti₂.refs.length)
    (hn : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (h : Wp m P host s f (vals (us ++ [addrVal a₁ (i₁ + BitVec.ofNat _ n.toNat - 1),
        addrVal a₂ (i₂ + BitVec.ofNat _ n.toNat - 1)]) ++ .plain (.tableGet x₂) ::
      .plain (.tableSet x₁) :: (vals [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' (n - 1)] ++
        .plain (.tableCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a₁ i₁, addrVal a₂ i₂, addrVal a' n]) ++
      .plain (.tableCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.table (.copyGt h₁ h₂ hb hn hgt)) (by simpa using h)

variable {y : ElemIdx} {ea : Nat} {ei : ElemInst} {j : BitVec 32}

/-- **`table.init`** out of bounds: traps. -/
theorem Wp.tableInit_oob {n : BitVec 32} (ht : s.table? f x = some (ta, ti))
    (he : s.elem? f y = some (ea, ei))
    (hb : ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 n]) ++
      .plain (.tableInit x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.table (.initOob ht he hb)) hq

/-- **`table.init`** of zero entries (in bounds). -/
theorem Wp.tableInit_zero (ht : s.table? f x = some (ta, ti)) (he : s.elem? f y = some (ea, ei))
    (hb : i.toNat ≤ ti.refs.length ∧ j.toNat ≤ ei.refs.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 0]) ++
      .plain (.tableInit x y) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.table (.initZero ht he hb)) (by simpa using h)

/-- **`table.init`** of `n ≠ 0` entries (in bounds): set the first entry, then
initialise the rest. -/
theorem Wp.tableInit_succ {n : BitVec 32} {r : Ref} (ht : s.table? f x = some (ta, ti))
    (he : s.elem? f y = some (ea, ei))
    (hb : i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length) (hn : n ≠ 0)
    (hr : ei.refs[j.toNat]? = some r)
    (h : Wp m P host s f (vals (us ++ [addrVal a i, .ref r]) ++ .plain (.tableSet x) ::
      (vals [addrVal a (i + 1), .i32 (j + 1), .i32 (n - 1)] ++ .plain (.tableInit x y) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [addrVal a i, .i32 j, .i32 n]) ++
      .plain (.tableInit x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.table (.initSucc ht he hb hn hr)) (by simpa using h)

/-- **`elem.drop`.** -/
theorem Wp.elemDrop (he : s.elem? f y = some (ea, ei))
    (h : Wp m P host (s.setElem ea []) f (vals us ++ rest) Q) :
    Wp m P host s f (vals us ++ .plain (.elemDrop y) :: rest) Q := by
  simpa using Wp.detVals (us := us) (args := []) (res := []) (rest := rest) fam_ok (by trivial)
    (.table (.elemDrop he)) (by simpa using h)

end Bulk

/-! ## Indirect calls -/

/-- The head rule in either reading. -/
theorem Wp.head {W : List Val} {i : Instr} (hi : Inert i)
    (hp : ∃ vs args c₀, W = vs ++ args ∧ Head P s f args (.plain i) c₀)
    (hs : ∀ vs args c₀, W = vs ++ args → Head P s f args (.plain i) c₀ →
      Wp m P host c₀.store c₀.frame (vals vs ++ c₀.code ++ rest) Q) :
    Wp m P host s f (vals W ++ .plain i :: rest) Q := by
  cases m
  · exact HWP.head hi hp hs
  · exact TSafe.head hi hp hs

theorem head_callIndirect {args : List Val} {y : TypeIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.callIndirect x y)) c₀) :
    args = [] ∧ c₀ = ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.callRef y)]⟩ := by
  cases h with
  | callIndirect => exact ⟨rfl, rfl⟩
  | _ => head_absurd

theorem head_returnCallIndirect {args : List Val} {y : TypeIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.returnCallIndirect x y)) c₀) :
    args = [] ∧ c₀ = ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.returnCallRef y)]⟩ := by
  cases h with
  | returnCallIndirect => exact ⟨rfl, rfl⟩
  | _ => head_absurd

/-- **`call_indirect x y`** unfolds to `table.get x`, a cast to the non-null
reference type `(ref y)` and `call_ref y`. -/
theorem Wp.callIndirect {y : TypeIdx}
    (h : Wp m P host s f (vals us ++ .plain (.tableGet x) :: .plain (.refCast ⟨true, .typeIdx y⟩) ::
      .plain (.callRef y) :: rest) Q) :
    Wp m P host s f (vals us ++ .plain (.callIndirect x y) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .callIndirect⟩ fun vs args c₀ hW hh => ?_
  obtain ⟨rfl, rfl⟩ := head_callIndirect hh
  have hvs : vs = us := by simpa using hW.symm
  subst hvs
  simpa using h

/-- **`return_call_indirect x y`** unfolds to `table.get x`, a cast to `(ref y)`
and `return_call_ref y`. -/
theorem Wp.returnCallIndirect {y : TypeIdx}
    (h : Wp m P host s f (vals us ++ .plain (.tableGet x) :: .plain (.refCast ⟨true, .typeIdx y⟩) ::
      .plain (.returnCallRef y) :: rest) Q) :
    Wp m P host s f (vals us ++ .plain (.returnCallIndirect x y) :: rest) Q := by
  refine Wp.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .returnCallIndirect⟩
    fun vs args c₀ hW hh => ?_
  obtain ⟨rfl, rfl⟩ := head_returnCallIndirect hh
  have hvs : vs = us := by simpa using hW.symm
  subst hvs
  simpa using h

end Silmaril.Wasm.Logic.Hoare
