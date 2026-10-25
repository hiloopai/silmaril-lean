module

public import Silmaril.Wasm.Binaryen.InlReverseCallee

@[expose] public section

/-! # Reverse control exits of relocated callees

Relocation is not injective: an original `return` and a branch can both become
the same branch instruction. These inversions use the original `AI`/`LI` witness
to retain that distinction. An inner contextual step is exposed for the recursive
simulation; every terminal label/handler rule is matched directly, at arbitrary
numerical profiles.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem AI.val?_eq {d : Nat} {a b : Admin} (related : AI p d a b) : a.val? = b.val? := by
  cases related with
  | @plain d i good => cases i <;> rfl
  | _ => rfl

theorem AI.val_reverse {d : Nat} {a : Admin} {v : Val}
    (related : AI p d a v.toAdmin) : a = v.toAdmin :=
  Admin.eq_of_val? (by rw [related.val?_eq, Admin.val?_toAdmin])

theorem LI.vals_reverse {d : Nat} : ∀ {vs : List Val} {original : List Admin},
    LI p d original (vals vs) → original = vals vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons head rest => by
    rw [head.val_reverse, LI.vals_reverse rest]
    rfl

theorem LI.cons_reverse {d : Nat} {a : Admin} {rest original : List Admin}
    (related : LI p d original (a :: rest)) :
    ∃ oldHead oldRest, original = oldHead :: oldRest ∧ AI p d oldHead a ∧
      LI p d oldRest rest := by
  cases related with
  | cons head tail => exact ⟨_, _, rfl, head, tail⟩

theorem LI.vals_cons_reverse {d : Nat} : ∀ {vs : List Val} {a : Admin}
    {rest original : List Admin}, LI p d original (vals vs ++ a :: rest) →
    ∃ oldHead oldRest, original = vals vs ++ oldHead :: oldRest ∧ AI p d oldHead a ∧
      LI p d oldRest rest
  | [], _, _, _, related => LI.cons_reverse related
  | _ :: _, _, _, _, .cons head tail => by
    obtain ⟨oldHead, oldRest, shape, related, rest⟩ := LI.vals_cons_reverse tail
    exact ⟨oldHead, oldRest, by rw [head.val_reverse, shape]; rfl, related, rest⟩

theorem AI.plain_reverse {d : Nat} {a : Admin} {i : Instr}
    (related : AI p d a (.plain i)) :
    ∃ old, a = .plain old ∧ InlineTy.retGood d old ∧ InlineTy.xform p.base d old = i := by
  cases related with
  | plain good => exact ⟨_, rfl, good, rfl⟩

theorem xform_br_reverse {base d : Nat} {old : Instr} {index : LabelIdx}
    (relocated : InlineTy.xform base d old = .br index) :
    old = .br index ∨ (old = .return_ ∧ index = InlineTy.xLabel d) := by
  cases old <;> simp_all [InlineTy.xform]

theorem xform_throwRef_reverse {base d : Nat} {old : Instr}
    (relocated : InlineTy.xform base d old = .throwRef) : old = .throwRef := by
  cases old <;> simp_all [InlineTy.xform]

theorem xform_ne_return {base d : Nat} (old : Instr) :
    InlineTy.xform base d old ≠ .return_ := by
  cases old <;> simp [InlineTy.xform]

theorem AI.not_returnCallRef {d : Nat} {a b : Admin} (related : AI p d a b) :
    ¬ b.IsReturnCallRef := by
  cases related with
  | @plain d old good =>
    cases old <;> simp_all [InlineTy.xform, InlineTy.retGood, Admin.IsReturnCallRef]
  | _ => simp [Admin.IsReturnCallRef]

theorem LI.throwing_reverse {d : Nat} {body : List Admin} {a : Nat}
    (related : LI p d body (throwing a)) : body = throwing a := by
  obtain ⟨head, rest, shape, headRelated, tail⟩ :=
    LI.vals_cons_reverse (vs := [.ref (.exn a)]) (a := .plain .throwRef) (rest := []) related
  obtain ⟨old, rfl, _, relocated⟩ := AI.plain_reverse headRelated
  obtain rfl := xform_throwRef_reverse relocated
  cases tail
  exact shape

theorem LI.trap_reverse {d : Nat} {body : List Admin}
    (related : LI p d body [.trap]) : body = [.trap] := by
  cases related with
  | cons head tail => cases head; cases tail; rfl

/-- Every chosen label head is either an exposed inner step (for recursive
matching), or a matching original control exit with the actual target reduct. -/
theorem reverse_callee_label {d n : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {args : List Val} {cont : List Instr} {body body' : List Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (contGood : InlineTy.retGoodL d cont) (bodyRelated : LI p (d + 1) body body')
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.label n (InlineTy.xformL p.base d cont) body') next) :
    (∃ bodyNext : Config H, args = [] ∧
      Step P Det.noHost ⟨t, ⟨L ++ F.locals, p.mi⟩, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame,
        [.label n (InlineTy.xformL p.base d cont) bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Det.Head P s F args (.label n cont body) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  cases selected with
  | ctxtLabel step => exact .inl ⟨_, rfl, step, rfl⟩
  | labelVals shape =>
    rw [shape] at bodyRelated
    exact .inr ⟨_, .labelVals (LI.vals_reverse bodyRelated),
      ⟨moduleEq, prefixLength, locals, rfl, LI.of_vals d _⟩, stores⟩
  | brLabelZero shape zero count =>
    rename_i discarded results index rest
    have combined : vals discarded ++ vals results ++ [Admin.plain (.br index)] ++ rest =
        vals (discarded ++ results) ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨head, oldRest, oldShape, headRelated, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, rfl, good, relocated⟩ := AI.plain_reverse headRelated
    rcases xform_br_reverse relocated with rfl | ⟨rfl, rfl⟩
    · exact .inr ⟨_, .brLabelZero (by simpa using oldShape) zero count,
        ⟨moduleEq, prefixLength, locals, rfl,
          LI.append (LI.of_vals d results) (LI.of_xformL contGood)⟩, stores⟩
    · have depth : d + 1 < 2 ^ 32 := good
      rw [InlineTy.xLabel_toNat depth] at zero
      omega
  | brLabelSucc shape positive =>
    rename_i results index rest
    have combined : vals results ++ [Admin.plain (.br index)] ++ rest =
        vals results ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨head, oldRest, oldShape, headRelated, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, rfl, good, relocated⟩ := AI.plain_reverse headRelated
    rcases xform_br_reverse relocated with rfl | ⟨rfl, rfl⟩
    · exact .inr ⟨_, .brLabelSucc (by simpa using oldShape) positive,
        ⟨moduleEq, prefixLength, locals, rfl,
          LI.append (LI.of_vals d results) (.cons (.plain trivial) .nil)⟩, stores⟩
    · have depth : d + 1 < 2 ^ 32 := good
      refine .inr ⟨_, .returnLabel (by simpa using oldShape),
        ⟨moduleEq, prefixLength, locals, rfl, ?_⟩, stores⟩
      rw [xLabel_pred depth]
      exact LI.append (LI.of_vals d results)
        (.cons (.plain (i := .return_) (show d < 2 ^ 32 by omega)) .nil)
  | returnCallRefLabel shape isReturn =>
    rename_i results head rest
    have combined : vals results ++ [head] ++ rest = vals results ++ head :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    exact (related.not_returnCallRef isReturn).elim
  | returnLabel shape =>
    rename_i results rest
    have combined : vals results ++ [Admin.plain .return_] ++ rest =
        vals results ++ .plain .return_ :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, _, _, relocated⟩ := AI.plain_reverse related
    exact (xform_ne_return old relocated).elim
  | throwRefLabel =>
    obtain rfl := LI.throwing_reverse bodyRelated
    exact .inr ⟨_, .throwRefLabel,
      ⟨moduleEq, prefixLength, locals, rfl,
        LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))⟩, stores⟩
  | trapLabel =>
    obtain rfl := LI.trap_reverse bodyRelated
    exact .inr ⟨_, .trapLabel,
      ⟨moduleEq, prefixLength, locals, rfl, LI.of_out Out.trap⟩, stores⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

/-- Handler control exits preserve the selected exception and catch clause.
Only a step of the protected body is left to the recursive simulation. -/
theorem reverse_callee_handler {d n : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {args : List Val} {catches : List Catch} {body body' : List Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (bodyRelated : LI p d body body')
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args (.handler n catches body') next) :
    (∃ bodyNext : Config H, args = [] ∧
      Step P Det.noHost ⟨t, ⟨L ++ F.locals, p.mi⟩, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.handler n catches bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Det.Head P s F args (.handler n catches body) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  cases selected with
  | ctxtHandler step => exact .inl ⟨_, rfl, step, rfl⟩
  | brHandler shape =>
    rename_i results index rest
    have combined : vals results ++ [Admin.plain (.br index)] ++ rest =
        vals results ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨head, oldRest, oldShape, headRelated, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, rfl, good, relocated⟩ := AI.plain_reverse headRelated
    rcases xform_br_reverse relocated with rfl | ⟨rfl, rfl⟩
    · exact .inr ⟨_, .brHandler (by simpa using oldShape),
        ⟨moduleEq, prefixLength, locals, rfl,
          LI.append (LI.of_vals d results) (.cons (.plain trivial) .nil)⟩, stores⟩
    · exact .inr ⟨_, .returnHandler (by simpa using oldShape),
        ⟨moduleEq, prefixLength, locals, rfl,
          LI.append (LI.of_vals d results) (.cons (.plain good) .nil)⟩, stores⟩
  | returnCallRefHandler shape isReturn =>
    rename_i results head rest
    have combined : vals results ++ [head] ++ rest = vals results ++ head :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    exact (related.not_returnCallRef isReturn).elim
  | returnHandler shape =>
    rename_i results rest
    have combined : vals results ++ [Admin.plain .return_] ++ rest =
        vals results ++ .plain .return_ :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, _, _, relocated⟩ := AI.plain_reverse related
    exact (xform_ne_return old relocated).elim
  | throwRefHandlerEmpty =>
    obtain rfl := LI.throwing_reverse bodyRelated
    exact .inr ⟨_, .throwRefHandlerEmpty,
      ⟨moduleEq, prefixLength, locals, rfl,
        LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))⟩, stores⟩
  | throwRefHandlerCatch exception tag =>
    obtain rfl := LI.throwing_reverse bodyRelated
    rw [stores.ht] at exception
    exact .inr ⟨_, .throwRefHandlerCatch exception (by rw [moduleEq]; exact tag),
      ⟨moduleEq, prefixLength, locals, rfl,
        LI.append (LI.of_vals d _) (.cons (.plain trivial) .nil)⟩, stores⟩
  | throwRefHandlerCatchRef exception tag =>
    obtain rfl := LI.throwing_reverse bodyRelated
    rw [stores.ht] at exception
    exact .inr ⟨_, .throwRefHandlerCatchRef exception (by rw [moduleEq]; exact tag),
      ⟨moduleEq, prefixLength, locals, rfl,
        LI.append (LI.of_vals d _) (.cons (.ref _) (.cons (.plain trivial) .nil))⟩, stores⟩
  | throwRefHandlerCatchAll =>
    obtain rfl := LI.throwing_reverse bodyRelated
    exact .inr ⟨_, .throwRefHandlerCatchAll,
      ⟨moduleEq, prefixLength, locals, rfl, .cons (.plain trivial) .nil⟩, stores⟩
  | throwRefHandlerCatchAllRef =>
    obtain rfl := LI.throwing_reverse bodyRelated
    exact .inr ⟨_, .throwRefHandlerCatchAllRef,
      ⟨moduleEq, prefixLength, locals, rfl, .cons (.ref _) (.cons (.plain trivial) .nil)⟩, stores⟩
  | throwRefHandlerNext noMatch =>
    rename_i clause remaining address
    obtain rfl := LI.throwing_reverse bodyRelated
    have originalNoMatch : ¬ CatchMatches s F address clause := by
      rw [stores.ht] at noMatch
      cases clause <;> simpa only [CatchMatches, moduleEq, withFuncs] using noMatch
    exact .inr ⟨_, .throwRefHandlerNext originalNoMatch,
      ⟨moduleEq, prefixLength, locals, rfl,
        .cons (.handler (LI.of_out (.ok (by
          simp [okI, structuredInstr, IsLocalI, IsTailI])))) .nil⟩, stores⟩
  | handlerVals shape =>
    rw [shape] at bodyRelated
    exact .inr ⟨_, .handlerVals (LI.vals_reverse bodyRelated),
      ⟨moduleEq, prefixLength, locals, rfl, LI.of_vals d _⟩, stores⟩
  | trapHandler =>
    obtain rfl := LI.trap_reverse bodyRelated
    exact .inr ⟨_, .trapHandler,
      ⟨moduleEq, prefixLength, locals, rfl, LI.of_out Out.trap⟩, stores⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

end Silmaril.Wasm.Binaryen.InlR
