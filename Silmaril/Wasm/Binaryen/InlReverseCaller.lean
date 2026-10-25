module

public import Silmaril.Wasm.Binaryen.InlG
public import Silmaril.Wasm.Binaryen.InlReverseHead

@[expose] public section

/-! # Right-oriented caller inversions and chosen reverse heads

Caller code can contain the actual inlined call site and an already-activated
callee. These inversions retain both cases instead of pretending that the caller
relation is symmetric. Primitive replay preserves the target's actual selected
result at an arbitrary numerical profile.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem IR.val?_eq {i j : Instr} (related : IR p i j) :
    (Admin.plain i).val? = (Admin.plain j).val? := by
  cases related <;> rfl

/-- Only structured instructions can differ from their original caller form. -/
theorem IR.eq_of_nonstruct_right {i j : Instr} (related : IR p i j)
    (nonstruct : ¬ StructE (.plain j)) : i = j := by
  cases related with
  | flat => rfl
  | site => exact (nonstruct (.inl ⟨_, _, rfl⟩)).elim
  | block _ => exact (nonstruct (.inl ⟨_, _, rfl⟩)).elim
  | loop _ => exact (nonstruct (.inr (.inl ⟨_, _, rfl⟩))).elim
  | if_ _ _ => exact (nonstruct (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))).elim
  | tryTable _ => exact (nonstruct (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))).elim

/-- A transformed block is either the distinguished inline site or the
structured image of an actual original block. -/
theorem IR.block_inv_right {i : Instr} {bt : BlockType} {body : List Instr}
    (related : IR p i (.block bt body)) :
    (i = .call p.fx ∧ bt = .typeIdx p.ty ∧ body = p.SBL) ∨
      ∃ oldBody, i = .block bt oldBody ∧ IRL p oldBody body := by
  cases related with
  | flat => exact .inr ⟨_, rfl, IRL.refl p _⟩
  | site => exact .inl ⟨rfl, rfl, rfl⟩
  | block body => exact .inr ⟨_, rfl, body⟩

theorem IR.loop_inv_right {i : Instr} {bt : BlockType} {body : List Instr}
    (related : IR p i (.loop bt body)) :
    ∃ oldBody, i = .loop bt oldBody ∧ IRL p oldBody body := by
  cases related with
  | flat => exact ⟨_, rfl, IRL.refl p _⟩
  | loop body => exact ⟨_, rfl, body⟩

theorem IR.if_inv_right {i : Instr} {bt : BlockType} {thenBody elseBody : List Instr}
    (related : IR p i (.if_ bt thenBody elseBody)) :
    ∃ oldThen oldElse, i = .if_ bt oldThen oldElse ∧
      IRL p oldThen thenBody ∧ IRL p oldElse elseBody := by
  cases related with
  | flat => exact ⟨_, _, rfl, IRL.refl p _, IRL.refl p _⟩
  | if_ thenBody elseBody => exact ⟨_, _, rfl, thenBody, elseBody⟩

theorem IR.tryTable_inv_right {i : Instr} {bt : BlockType} {catches : List Catch}
    {body : List Instr} (related : IR p i (.tryTable bt catches body)) :
    ∃ oldBody, i = .tryTable bt catches oldBody ∧ IRL p oldBody body := by
  cases related with
  | flat => exact ⟨_, rfl, IRL.refl p _⟩
  | tryTable body => exact ⟨_, rfl, body⟩

/-- A value on the transformed side was the same original value. -/
theorem IR.val_inv_right {v : Val} {i j : Instr}
    (value : Admin.plain j = v.toAdmin) (related : IR p i j) : i = j := by
  have original : Admin.plain i = v.toAdmin :=
    Admin.eq_of_val? (by rw [related.val?_eq, value, Admin.val?_toAdmin])
  exact Admin.plain.inj (original.trans value.symm)

theorem AG.val?_eq {E : List (Option Val)} {a b : Admin} (related : AG p E a b) :
    a.val? = b.val? := by
  cases related with
  | plain related => exact related.val?_eq
  | _ => rfl

theorem AG.val_inv_right {E : List (Option Val)} {a : Admin} {v : Val}
    (related : AG p E a v.toAdmin) : a = v.toAdmin :=
  Admin.eq_of_val? (by rw [related.val?_eq, Admin.val?_toAdmin])

theorem AG.plain_inv_right {E : List (Option Val)} {a : Admin} {i : Instr}
    (related : AG p E a (.plain i)) : ∃ old, a = .plain old ∧ IR p old i := by
  cases related with
  | plain instruction => exact ⟨_, rfl, instruction⟩

/-- A target label can be ordinary caller control or the live inlined callee.
Both original shapes, including the retained callee frame, are explicit. -/
theorem AG.label_inv_right {E : List (Option Val)} {a : Admin} {n : Nat}
    {cont : List Instr} {body : List Admin} (related : AG p E a (.label n cont body)) :
    (∃ oldCont oldBody, a = .label n oldCont oldBody ∧
      IRL p oldCont cont ∧ LG p E oldBody body) ∨
    (cont = [] ∧ ∃ F oldBody, a = .frame n F oldBody ∧
      F.module = p.mi ∧ F.locals = E ∧ SiteR p n oldBody body) := by
  cases related with
  | label cont body => exact .inl ⟨_, _, rfl, cont, body⟩
  | site moduleEq locals body => exact .inr ⟨rfl, _, _, rfl, moduleEq, locals, body⟩

theorem AG.handler_inv_right {E : List (Option Val)} {a : Admin} {n : Nat}
    {catches : List Catch} {body : List Admin}
    (related : AG p E a (.handler n catches body)) :
    ∃ oldBody, a = .handler n catches oldBody ∧ LG p E oldBody body := by
  cases related with
  | handler body => exact ⟨_, rfl, body⟩

theorem AG.frame_inv_right {E : List (Option Val)} {a : Admin} {n : Nat}
    {F : Frame} {body : List Admin} (related : AG p E a (.frame n F body)) :
    ∃ oldFrame oldBody, a = .frame n oldFrame oldBody ∧ FR p oldFrame F oldBody body := by
  cases related with
  | frame body => exact ⟨_, _, rfl, body⟩

/-- An unchanged nonstructured target head determines its original flat head. -/
theorem AG.eq_of_nonstruct_flat_right {E : List (Option Val)} {a b : Admin}
    (related : AG p E a b) (simple : SimpleE b) (nonstruct : ¬ StructE b) : a = b := by
  cases related with
  | plain related => rw [IR.eq_of_nonstruct_right related nonstruct]
  | label _ _ => exact (simple.1 _ _ _ rfl).elim
  | handler _ => exact (simple.2.1 _ _ _ rfl).elim
  | frame _ => exact (simple.2.2.1 _ _ _ rfl).elim
  | site _ _ _ => exact (simple.1 _ _ _ rfl).elim
  | _ => rfl

theorem LGq.vals_cons_inv_right : ∀ {vs : List Val} {x : Admin} {rest original : List Admin},
    x.val? = none → LGq p original (vals vs ++ x :: rest) →
    ∃ i j oldRest, x = .plain j ∧ original = vals vs ++ .plain i :: oldRest ∧
      IR p i j ∧ LGq p oldRest rest
  | [], _, _, _, _, .cons head tail => ⟨_, _, _, rfl, rfl, head, tail⟩
  | [], _, _, _, nonvalue, .ref _ _ => by simp at nonvalue
  | v :: vs, x, rest, _, nonvalue, related => by
    have related' : LGq p _ (v.toAdmin :: (vals vs ++ x :: rest)) := related
    generalize value : v.toAdmin = a at related'
    cases related' with
    | cons head tail =>
      obtain ⟨i, j, oldRest, rfl, rfl, headRelated, restRelated⟩ :=
        LGq.vals_cons_inv_right nonvalue tail
      obtain rfl := IR.val_inv_right value.symm head
      exact ⟨i, j, oldRest, rfl, by rw [← value]; rfl, headRelated, restRelated⟩
    | ref r tail =>
      obtain ⟨i, j, oldRest, rfl, rfl, headRelated, restRelated⟩ :=
        LGq.vals_cons_inv_right nonvalue tail
      exact ⟨i, j, oldRest, rfl, by change _ = v.toAdmin :: _; rw [value]; rfl, headRelated, restRelated⟩

theorem LGq.vals_inv_right : ∀ {vs : List Val} {original : List Admin},
    LGq p original (vals vs) → original = vals vs
  | [], _, .nil => rfl
  | v :: vs, _, related => by
    have related' : LGq p _ (v.toAdmin :: vals vs) := related
    generalize value : v.toAdmin = a at related'
    cases related' with
    | cons head tail =>
      obtain rfl := IR.val_inv_right value.symm head
      rw [LGq.vals_inv_right tail, ← value]
      rfl
    | ref r tail =>
      rw [LGq.vals_inv_right tail]
      show _ = v.toAdmin :: _
      rw [value]
      rfl

/-- Recover the original caller head from the actual transformed first
nonvalue. A transformed inlined block can correspond either to ordinary related
code or to the pending fetched source call. Traps and throws retain dead suffixes. -/
theorem LG.vals_cons_inv_right {E : List (Option Val)} :
    ∀ {vs : List Val} {x : Admin} {rest original : List Admin},
    x.val? = none → LG p E original (vals vs ++ x :: rest) →
    (∃ oldHead oldRest, original = vals vs ++ oldHead :: oldRest ∧
      AG p E oldHead x ∧ LGq p oldRest rest) ∨
    (x = .plain (.block (.typeIdx p.ty) p.SBL) ∧
      ∃ oldRest, original = vals vs ++ [.ref (.func p.af), .callRefType p.df] ++ oldRest ∧
        LGq p oldRest rest) ∨
    (x = .trap ∧ ∃ oldRest, original = vals vs ++ .trap :: oldRest) ∨
    (x = .plain .throwRef ∧ ∃ oldRest, original = vals vs ++ .plain .throwRef :: oldRest)
  | [], x, rest, original, nonvalue, related => by
    have related' : LG p E original (x :: rest) := related
    cases related' with
    | val value _ => simp [nonvalue] at value
    | head head tail => exact .inl ⟨_, _, rfl, head, tail⟩
    | plain tail =>
      obtain ⟨i, j, oldRest, rfl, rfl, head, tail⟩ :=
        LGq.vals_cons_inv_right (vs := []) nonvalue tail
      exact .inl ⟨_, _, rfl, .plain head, tail⟩
    | seg tail => exact .inr (.inl ⟨rfl, _, rfl, tail⟩)
    | trapT => exact .inr (.inr (.inl ⟨rfl, _, rfl⟩))
    | throwT => exact .inr (.inr (.inr ⟨rfl, _, rfl⟩))
  | v :: vs, x, rest, original, nonvalue, related => by
    have related' : LG p E original (v.toAdmin :: (vals vs ++ x :: rest)) := related
    generalize value : v.toAdmin = a at related'
    generalize code : vals vs ++ x :: rest = tail at related'
    cases related' with
    | val _ tail =>
      subst code value
      rcases LG.vals_cons_inv_right nonvalue tail with matched | pending | trapped | thrown
      · obtain ⟨oldHead, oldRest, rfl, headRelated, restRelated⟩ := matched
        exact .inl ⟨oldHead, oldRest, rfl, headRelated, restRelated⟩
      · obtain ⟨rfl, oldRest, shape, restRelated⟩ := pending
        exact .inr (.inl ⟨rfl, oldRest, by rw [shape]; rfl, restRelated⟩)
      · obtain ⟨rfl, oldRest, shape⟩ := trapped
        exact .inr (.inr (.inl ⟨rfl, oldRest, by rw [shape]; rfl⟩))
      · obtain ⟨rfl, oldRest, shape⟩ := thrown
        exact .inr (.inr (.inr ⟨rfl, oldRest, by rw [shape]; rfl⟩))
    | head head tail =>
      subst value code
      rw [head.val_inv_right]
      obtain ⟨i, j, oldRest, rfl, rfl, head, tail⟩ :=
        LGq.vals_cons_inv_right nonvalue tail
      exact .inl ⟨_, _, rfl, .plain head, tail⟩
    | plain tail =>
      subst value code
      obtain ⟨i, j, oldRest, rfl, rfl, head, tail⟩ :=
        LGq.vals_cons_inv_right (vs := v :: vs) nonvalue tail
      exact .inl ⟨_, _, rfl, .plain head, tail⟩
    | seg _ | trapT | throwT =>
      have value' := congrArg Admin.val? value
      rw [Admin.val?_toAdmin] at value'
      cases value'

/-- Replay an unchanged computational caller head, retaining the chosen result
and the actual mutable store. Structured control and calls use their own rules. -/
theorem reverse_caller_noncall_head {s t : Store H} {fo : Frame}
    {E : List (Option Val)} {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (simple : SimpleE head) (nonstruct : ¬ StructE head) (nontail : ¬ TailE head)
    (noncall : ¬ head.IsCallRef)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args head originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  have notCall : ¬ CallData t ⟨fo.locals ++ E, p.mi⟩ args head next := by
    rintro ⟨_, _, _, _, _, _, _, isCall, _⟩
    exact noncall isCall
  rcases head_simple_reverse stores moduleEq.symm simple selected with call |
      ⟨originalNext, actual, originalFrame, transformedFrame, code, related⟩
  · exact (notCall call).elim
  · rcases head_out selected simple nonstruct with call | out | ⟨tail, _⟩
    · exact (notCall call).elim
    · refine ⟨originalNext, actual, ⟨?_, ?_, E, extra, ?_, ?_⟩, related⟩
      · rw [originalFrame]; exact moduleEq
      · rw [originalFrame]; exact locals
      · rw [transformedFrame, originalFrame]
      · rw [code]; exact LG.of_out out
    · exact (nontail tail).elim

end Silmaril.Wasm.Binaryen.InlR
