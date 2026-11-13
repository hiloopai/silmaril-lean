module

public import Silmaril.Wasm.Dataflow.Fragment.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

/-!
# The DCE fragment: reduction lemmas

* `Step.noHost_of_frag`: a step of fragment code uses no host call;
* `Step.frag`: reduction preserves fragment code;
* `head_pure`, `pureArity_step_vals`, `pureArity_step`: a removable producer, applied to
  its operands, steps only to one value, with store and frame unchanged.

Port of an earlier development `Silmaril/Wasm/Dataflow/Fragment.lean`. The source
closed the family cases of `head_pure` by a hygiene-off macro and decomposed the step by
hand with `fnv`; here the family inversions are separate lemmas (`parametric_pure`,
`numeric_pure`, `variable_pure`) and the decomposition is silmaril-lean's
`Step.head_inv`. `pureArity_step` is derived from `pureArity_step_vals` (the source proved
both from scratch).
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf noHost)

theorem fragSeq_iff (is : List Instr) : fragSeq is = true ↔ ∀ i ∈ is, fragInstr i = true := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih]

theorem fragAdminSeq_iff (as : List Admin) :
    fragAdminSeq as = true ↔ ∀ a ∈ as, fragAdmin a = true := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

/-- `CALL_REF` is outside the fragment. -/
theorem IsCallRef.fragAdmin_eq {c : Admin} (h : c.IsCallRef) : fragAdmin c = false := by
  unfold Admin.IsCallRef at h
  split at h <;> simp_all [fragInstr]

/-- `RETURN_CALL_REF` is outside the fragment. -/
theorem IsReturnCallRef.fragAdmin_eq {c : Admin} (h : c.IsReturnCallRef) :
    fragAdmin c = false := by
  unfold Admin.IsReturnCallRef at h
  split at h <;> simp_all [fragInstr]

/-- Removable producers are fragment instructions. -/
theorem pureArity_frag {i : Instr} {n : Nat} (hi : pureArity? i = some n) :
    fragInstr i = true := by
  cases i <;> simp_all [pureArity?, fragInstr]

/-- A removable producer that is not a value is a parametric, numeric or variable
instruction. -/
theorem famOf_of_pure {i : Instr} {n : Nat} (hi : pureArity? i = some n)
    (hv : (Admin.plain i).val? = none) :
    famOf (.plain i) = .parametric ∨ famOf (.plain i) = .numeric ∨
      famOf (.plain i) = .variable := by
  cases i <;> simp_all [pureArity?, famOf, Admin.val?]

/-- A total integer operator does not trap. -/
theorem intBinOp_trap_absurd {t : IntType} {op : IntBinOp} {n : Nat} {x y : BitVec t.width}
    {e : IntTrap} (hi : pureArity? (.intBinOp t op) = some n)
    (he : intBinOp t op x y = .error e) : False := by
  unfold intBinOp at he
  split at he <;> simp_all [pureArity?, intBinOpTotal]

/-! ## Fragment code does not call the host -/

/-- A step of fragment code uses no host call. -/
theorem Step.noHost_of_frag {P : Profile} {H : Type} {host : HostSemantics H}
    {c c' : Config H} (h : Step P host c c') (hc : fragAdminSeq c.code = true) :
    Step P noHost c c' := by
  revert hc
  induction h with
  | parametric h => exact fun _ => .parametric h
  | numeric h => exact fun _ => .numeric h
  | vector h => exact fun _ => .vector h
  | «variable» h => exact fun _ => .«variable» h
  | table h => exact fun _ => .table h
  | memory h => exact fun _ => .memory h
  | reference h => exact fun _ => .reference h
  | aggregate h => exact fun _ => .aggregate h
  | @ctxtInstrs _ _ _ _ vs is _ rest _ hne ih =>
    intro hc
    have hc' : (fragAdminSeq (vals vs) = true ∧ fragAdminSeq is = true) ∧
        fragAdminSeq rest = true := by
      simpa only [fragAdminSeq_append, Bool.and_eq_true] using hc
    exact .ctxtInstrs (ih hc'.1.2) hne
  | @ctxtLabel _ _ _ _ n cont is _ _ ih =>
    intro hc
    have hc' : fragSeq cont = true ∧ fragAdminSeq is = true := by
      simpa only [fragAdminSeq_cons, fragAdmin_label, fragAdminSeq_nil, Bool.and_true,
        Bool.and_eq_true] using hc
    exact .ctxtLabel (ih hc'.2)
  | ctxtHandler _ _ => exact fun hc => absurd hc (by simp)
  | ctxtFrame _ _ => exact fun hc => absurd hc (by simp)
  | block hbt hm => exact fun _ => .block hbt hm
  | loop hbt hm => exact fun _ => .loop hbt hm
  | ifTrue hc => exact fun _ => .ifTrue hc
  | ifFalse => exact fun _ => .ifFalse
  | labelVals => exact fun _ => .labelVals
  | brLabelZero hl hn => exact fun _ => .brLabelZero hl hn
  | brLabelSucc hl => exact fun _ => .brLabelSucc hl
  | brHandler => exact fun _ => .brHandler
  | brIfTrue hc => exact fun _ => .brIfTrue hc
  | brIfFalse => exact fun _ => .brIfFalse
  | brTableLt hi => exact fun _ => .brTableLt hi
  | brTableGe hi => exact fun _ => .brTableGe hi
  | brOnNullNull => exact fun _ => .brOnNullNull
  | brOnNullAddr hv => exact fun _ => .brOnNullAddr hv
  | brOnNonNullNull => exact fun _ => .brOnNonNullNull
  | brOnNonNullAddr hv => exact fun _ => .brOnNonNullAddr hv
  | brOnCastSucceed h => exact fun _ => .brOnCastSucceed h
  | brOnCastFail h => exact fun _ => .brOnCastFail h
  | brOnCastFailSucceed h => exact fun _ => .brOnCastFailSucceed h
  | brOnCastFailFail h => exact fun _ => .brOnCastFailFail h
  | call hx hf => exact fun _ => .call hx hf
  | callRefNull hc => exact fun _ => .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact fun _ => .callRefFunc hc hf he hn hcode
  | callRefHost hc' => exact fun hc => absurd hc (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefHostDiv hc' => exact fun hc => absurd hc (by simp [IsCallRef.fragAdmin_eq hc'])
  | returnCall hx hf => exact fun _ => .returnCall hx hf
  | returnCallRefLabel hc => exact fun _ => .returnCallRefLabel hc
  | returnCallRefHandler hc => exact fun _ => .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact fun _ => .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact fun _ => .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact fun _ => .callIndirect
  | returnCallIndirect => exact fun _ => .returnCallIndirect
  | frameVals hn => exact fun _ => .frameVals hn
  | returnFrame hn => exact fun _ => .returnFrame hn
  | returnLabel => exact fun _ => .returnLabel
  | returnHandler => exact fun _ => .returnHandler
  | throw ht he hn => exact fun _ => .throw ht he hn
  | throwRefNull => exact fun _ => .throwRefNull
  | throwRefInstrs hne => exact fun _ => .throwRefInstrs hne
  | throwRefLabel => exact fun _ => .throwRefLabel
  | throwRefFrame => exact fun _ => .throwRefFrame
  | throwRefHandlerEmpty => exact fun _ => .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact fun _ => .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact fun _ => .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact fun _ => .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact fun _ => .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact fun _ => .throwRefHandlerNext h
  | tryTable hbt hm => exact fun _ => .tryTable hbt hm
  | handlerVals => exact fun _ => .handlerVals
  | trapInstrs hne => exact fun _ => .trapInstrs hne
  | trapLabel => exact fun _ => .trapLabel
  | trapHandler => exact fun _ => .trapHandler
  | trapFrame => exact fun _ => .trapFrame

/-- Reduction preserves fragment code. -/
theorem Step.frag {P : Profile} {H : Type} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : fragAdminSeq c.code = true) : fragAdminSeq c'.code = true := by
  revert hc
  induction h with
  | parametric h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | numeric h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | vector h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | «variable» h => intro hc; cases h <;> simp_all [fragInstr]
  | table h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | memory h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | reference h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | aggregate h => intro hc; cases h <;> simp_all [fragInstr, constI32]
  | @ctxtInstrs _ _ _ _ vs is is' rest _ _ ih =>
    intro hc
    have hc' : fragAdminSeq is = true ∧ fragAdminSeq rest = true := by
      simpa only [fragAdminSeq_append, fragAdminSeq_vals, Bool.true_and,
        Bool.and_eq_true] using hc
    show fragAdminSeq (vals vs ++ is' ++ rest) = true
    simp only [fragAdminSeq_append, fragAdminSeq_vals, ih hc'.1, hc'.2, Bool.and_self]
  | @ctxtLabel _ _ _ _ n cont is is' _ ih =>
    show fragAdminSeq [.label n cont is] = true → fragAdminSeq [.label n cont is'] = true
    intro hc
    have hc' : fragSeq cont = true ∧ fragAdminSeq is = true := by
      simpa only [fragAdminSeq_cons, fragAdmin_label, fragAdminSeq_nil, Bool.and_true,
        Bool.and_eq_true] using hc
    show fragAdminSeq [.label n cont is'] = true
    simp only [fragAdminSeq_cons, fragAdmin_label, fragAdminSeq_nil, hc'.1, ih hc'.2,
      Bool.and_self]
  | callRefFunc hc' => exact fun hc => absurd hc (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefHost hc' => exact fun hc => absurd hc (by simp [IsCallRef.fragAdmin_eq hc'])
  | callRefHostDiv => exact id
  | _ => intro hc; simp_all [fragInstr, constI32, throwing]

/-! ## Head steps of removable producers -/

/-- A single administrative value is a single value. -/
theorem exists_single_val {a : Admin} (h : a.val? ≠ none) : ∃ v : Val, [a] = [v.toAdmin] := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨v, by rw [Admin.eq_of_val? hv]⟩

/-- A parametric head step of a removable producer (`select`) consumes its operands and
produces one value. -/
theorem parametric_pure {i : Instr} {n : Nat} {args : List Val} {is' : List Admin}
    (h : ParametricStep (vals args ++ [.plain i]) is') (hi : pureArity? i = some n) :
    args.length = n ∧ ∃ v : Val, is' = [v.toAdmin] := by
  generalize hl : vals args ++ [Admin.plain i] = l at h
  have hlen := congrArg List.length hl
  have hlast := congrArg List.getLast? hl
  cases h <;> simp at hlen hlast <;> subst hlast <;> simp_all [pureArity?]

/-- A numeric head step of a removable producer consumes its operands and produces one
value: the producer does not trap. -/
theorem numeric_pure {P : Profile} {i : Instr} {n : Nat} {args : List Val} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain i]) is') (hi : pureArity? i = some n) :
    args.length = n ∧ ∃ v : Val, is' = [v.toAdmin] := by
  generalize hl : vals args ++ [Admin.plain i] = l at h
  have hlen := congrArg List.length hl
  have hlast := congrArg List.getLast? hl
  cases h <;> simp at hlen hlast <;> subst hlast
  case intBinOpTrap he => exact (intBinOp_trap_absurd hi he).elim
  all_goals first
    | (simp [pureArity?] at hi; done)
    | exact ⟨by simp_all [pureArity?],
        exists_single_val (by simp [Admin.val?, constI32, Val.i32, Val.toAdmin])⟩

/-- A variable head step of a removable producer (`local.get`) produces one value and
keeps the store and frame. -/
theorem variable_pure {H : Type} {s : Store H} {f : Frame} {i : Instr} {n : Nat}
    {args : List Val} {c : Config H} (h : VariableStep ⟨s, f, vals args ++ [.plain i]⟩ c)
    (hi : pureArity? i = some n) :
    args.length = n ∧ ∃ v : Val, c = ⟨s, f, [v.toAdmin]⟩ := by
  generalize hl : (⟨s, f, vals args ++ [Admin.plain i]⟩ : Config H) = cc at h
  cases h <;> simp only [Config.mk.injEq] at hl <;> obtain ⟨rfl, rfl, hl⟩ := hl <;>
    have hlen := congrArg List.length hl <;> have hlast := congrArg List.getLast? hl <;>
    simp at hlen hlast <;> subst hlast <;> simp_all [pureArity?]

/-- A head step of a removable producer consumes exactly its operands and produces one
value, with the store and frame unchanged. -/
theorem head_pure {P : Profile} {H : Type} {s : Store H} {f : Frame} {args : List Val}
    {i : Instr} {n : Nat} {c₀ : Config H} (hh : Head P s f args (.plain i) c₀)
    (hi : pureArity? i = some n) (hv : (Admin.plain i).val? = none) :
    args.length = n ∧ ∃ v : Val, c₀ = ⟨s, f, [v.toAdmin]⟩ := by
  rcases famOf_of_pure hi hv with hk | hk | hk
  · obtain ⟨is', hp, rfl⟩ : ∃ is', ParametricStep (vals args ++ [.plain i]) is' ∧
        c₀ = ⟨s, f, is'⟩ := by
      simpa [SingleThreaded.Det.FamRel, hk] using hh.fam_inv (by simp [hk])
    obtain ⟨hn, v, rfl⟩ := parametric_pure hp hi
    exact ⟨hn, v, rfl⟩
  · obtain ⟨is', hp, rfl⟩ : ∃ is', NumericStep P (vals args ++ [.plain i]) is' ∧
        c₀ = ⟨s, f, is'⟩ := by
      simpa [SingleThreaded.Det.FamRel, hk] using hh.fam_inv (by simp [hk])
    obtain ⟨hn, v, rfl⟩ := numeric_pure hp hi
    exact ⟨hn, v, rfl⟩
  · have hp : VariableStep ⟨s, f, vals args ++ [.plain i]⟩ c₀ := by
      simpa [SingleThreaded.Det.FamRel, hk] using hh.fam_inv (by simp [hk])
    exact variable_pure hp hi

/-- A removable producer after the values `us` consumes the last `n` of them and leaves
one value, with the store and frame unchanged. -/
theorem pureArity_step_vals {P : Profile} {H : Type} {host : HostSemantics H} {s : Store H}
    {f : Frame} {i : Instr} {n : Nat} {us : List Val} {c : Config H}
    (hi : pureArity? i = some n) (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ c) :
    ∃ ws args : List Val, ∃ v : Val, us = ws ++ args ∧ args.length = n ∧
      c = ⟨s, f, vals ws ++ [v.toAdmin]⟩ := by
  have hfrag : fragAdminSeq (vals us ++ [.plain i]) = true := by
    simp [pureArity_frag hi]
  have h' : Step P noHost ⟨s, f, vals us ++ .plain i :: []⟩ c := Step.noHost_of_frag h hfrag
  cases hv : (Admin.plain i).val? with
  | some w =>
    have hcode : vals us ++ [Admin.plain i] = vals (us ++ [w]) := by
      simp [Admin.eq_of_val? hv, vals]
    have h'' : Step P noHost ⟨s, f, vals (us ++ [w])⟩ c := by simpa [hcode] using h'
    exact (SingleThreaded.Det.not_step_vals h'').elim
  | none =>
    obtain ⟨ws, args, c₀, rfl, hh, rfl⟩ := Step.head_inv h' hv (by simp) (by
      intro he; cases he; simp [pureArity?] at hi)
    obtain ⟨hlen, v, rfl⟩ := head_pure hh hi hv
    exact ⟨ws, args, v, rfl, hlen, by simp⟩

/-- A removable producer, applied to exactly its operands, steps only to a single value,
with the store and frame unchanged. -/
theorem pureArity_step {P : Profile} {H : Type} {host : HostSemantics H} {s : Store H}
    {f : Frame} {i : Instr} {n : Nat} {vs : List Val} {c : Config H}
    (hi : pureArity? i = some n) (hn : vs.length = n)
    (h : Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c) :
    ∃ v : Val, c = ⟨s, f, [v.toAdmin]⟩ := by
  obtain ⟨ws, args, v, rfl, hargs, rfl⟩ := pureArity_step_vals hi h
  have hws : ws = [] := List.eq_nil_of_length_eq_zero (by simp at hn; omega)
  exact ⟨v, by simp [hws, vals]⟩

/-! ## The stutter measure -/

theorem adminSize_pos (a : Admin) : 0 < adminSize a := by
  unfold adminSize; split <;> omega

theorem codeSize_pos {as : List Admin} (h : as ≠ []) : 0 < codeSize as := by
  cases as with
  | nil => exact absurd rfl h
  | cons a as => rw [codeSize_cons]; have := adminSize_pos a; omega

end Silmaril.Wasm.Dataflow
