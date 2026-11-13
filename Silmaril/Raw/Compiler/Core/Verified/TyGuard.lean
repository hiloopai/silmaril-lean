module

public import Silmaril.Compiler.Core.Verified.TyConv.Defs
public import Silmaril.Compiler.Core.Verified.IntExpr.Defs
/-! # Cerberus's guards of binary operators at every supported integer type

Cerberus elaborates a binary operator to an `unseq` of its operands bound to `(a, b)`, then the
pure guard `case (a, b) of (Specified(x), Specified(y)) => body | …`. After the usual
arithmetic conversions the operands are converted to the common type `T` (`conv_int(T, x)`,
the primitive or std.core's function: `convTy`), and `body` is one of

* `Specified(catch_exceptional_condition(T, op, x', y'))` for a signed `T` (`G.arith`): the
  exact result, undefined behaviour when `T` does not hold it;
* `Specified(wrapI(T, op, x', y'))` for an unsigned `T` (`G.wrap`): the wrap-around;
* `if x' rel y' then Specified(c₁) else Specified(c₂)`, or its negation (`G.cmp`).

`tguard file a b p = some g` recognises the guard syntactically. `G.val g n₁ n₂` is its value
on the operand values (`TyConv.cv` for every conversion), `G.Ok g n₁ n₂` says it is defined:
`tguard_eval` evaluates a defined guard (`PureEvalExt.Ev`), `tguard_fails` runs an undefined one
to the request of undefined behaviour `UB036_exceptional_condition`.

`load_local` is `LoadTask.load_local` for a local of any supported type (`TyActions`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyGuard

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ConvInt (Pure lookupFun)
open TyActions (supported width signed bounds Fits TSlot)
open TyConv (cv)
open Guard (operands lookup_pair_first lookup_pair_second)
open LoadTask (Touched)

/-- `p` converts the symbol `s` to the type it returns. -/
def convTy (file : File Codec.wireModel Unit Unit) (s : Sym) : Pure → Option IntegerType
  | .mk _ () (.call (.sym c) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))),
      .mk _ () (.sym s')]) =>
      if s'.key = s.key ∧ TyConv.isConv file c = true then some ity else none
  | .mk _ () (.convInt ity (.mk _ () (.sym s'))) => if s'.key = s.key then some ity else none
  | _ => none

/-- The guards. -/
inductive G where
  | arith (ity : IntegerType) (op : IntOp)
  | wrap (ity : IntegerType) (op : IntOp)
  | cmp (ity : IntegerType) (r : BinOp) (c₁ c₂ : Int)
  | bit (ity : IntegerType) (o : Bitwise.Op)

/-- The type of the guard's conversions. -/
def G.ty : G → IntegerType
  | .arith ity _ | .wrap ity _ | .cmp ity _ _ _ | .bit ity _ => ity

/-- The value of a guard on the operand values. -/
def G.val : G → Int → Int → Int
  | .arith ity op, x, y => Guard.apply op (cv ity x) (cv ity y)
  | .wrap ity op, x, y => cv ity (Guard.apply op (cv ity x) (cv ity y))
  | .cmp ity r c₁ c₂, x, y => if Guard.holds r (cv ity x) (cv ity y) then c₁ else c₂
  | .bit ity o, x, y => o.apply (cv ity x) (cv ity y)

/-- The guard is defined. -/
def G.Ok : G → Int → Int → Prop
  | .arith ity op, x, y => Fits ity (Guard.apply op (cv ity x) (cv ity y))
  | _, _, _ => True

/-- The body of the first arm, with the operand values bound to `x` and `y`. -/
def bodyG (file : File Codec.wireModel Unit Unit) (x y : Sym) : Pure → Option G
  | .mk _ () (.ctor .specified [.mk _ () (.catchExceptionalCondition ity op p q)]) =>
      if convTy file x p = some ity ∧ convTy file y q = some ity ∧ supported ity = true ∧
          Guard.arith op = true ∧ signed ity = true then some (.arith ity op) else none
  | .mk _ () (.ctor .specified [.mk _ () (.wrapI ity op p q)]) =>
      if convTy file x p = some ity ∧ convTy file y q = some ity ∧ supported ity = true ∧
          Guard.arith op = true then some (.wrap ity op) else none
  | .mk _ () (.if_ (.mk _ () (.op r p q))
      (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₁)))]))
      (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₂)))]))) =>
      match convTy file x p, convTy file y q with
      | some ity, some ity' =>
        if ity' = ity ∧ supported ity = true ∧ Guard.rel r = true then some (.cmp ity r c₁ c₂)
        else none
      | _, _ => none
  | .mk _ () (.if_ (.mk _ () (.not (.mk _ () (.op r p q))))
      (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₁)))]))
      (.mk _ () (.ctor .specified [.mk _ () (.val (.object (.integer c₂)))]))) =>
      match convTy file x p, convTy file y q with
      | some ity, some ity' =>
        if ity' = ity ∧ supported ity = true ∧ Guard.rel r = true then some (.cmp ity r c₂ c₁)
        else none
      | _, _ => none
  | .mk _ () (.ctor .specified [.mk _ () (.ctor c [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))),
      p, q])]) =>
      match Bitwise.ofCtor c with
      | some o =>
        if convTy file x p = some ity ∧ convTy file y q = some ity ∧ supported ity = true then
          some (.bit ity o)
        else none
      | none => none
  | _ => none

/-- The guard of a binary operator over the operand tuple `(a, b)`. -/
def tguard (file : File Codec.wireModel Unit Unit) (a b : Sym) : Pure → Option G
  | .mk _ () (.case_ (.mk _ () (.ctor .tuple [.mk _ () (.sym a'), .mk _ () (.sym b')]))
      ((.mk _ (.ctor .tuple [.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
          .mk _ (.ctor .specified [.mk _ (.base (some y, _))])]), body) :: _)) =>
      if a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧ y.key ≠ x.key then bodyG file x y body
      else none
  | _ => none

/-! ## Evaluation -/

variable {file : Program} {tags : Mem.Concrete.Tags}

theorem convTy_ev {s : Sym} {p : Pure} {ity : IntegerType} (h : convTy file s p = some ity)
    (hs : supported ity = true) {env : Env} {n : Int}
    (hx : env.lookup s = some (.object (.integer n))) :
    Ev file tags env (.inl p) (.inl (.object (.integer (cv ity n)))) := by
  unfold convTy at h
  split at h
  · rename_i _ c _ ann ity' _ s'
    split at h
    · rename_i hc
      cases h
      obtain ⟨hk, hconv⟩ := hc
      have hs' : env.lookup s' = some (.object (.integer n)) := by
        rw [ReturnLit.lookup_key hk]; exact hx
      exact TyConv.conv_ev (ann := ann) hconv hs (.cons .val (.cons (.sym hs') .nil))
    · cases h
  · rename_i _ ity' _ s'
    split at h
    · rename_i hk
      cases h
      have hs' : env.lookup s' = some (.object (.integer n)) := by
        rw [ReturnLit.lookup_key hk]; exact hx
      exact .convInt (.cons (.sym hs') .nil) (TyConv.primitive_conv hs n tags)
    · cases h
  · cases h

theorem G.ok_ty {g : G} (file' : File Codec.wireModel Unit Unit) {x y : Sym} {p : Pure}
    (h : bodyG file' x y p = some g) : supported g.ty = true := by
  unfold bodyG at h
  split at h
  · split at h
    · rename_i hc; cases h; exact hc.2.2.1
    · cases h
  · split at h
    · rename_i hc; cases h; exact hc.2.2.1
    · cases h
  · split at h
    · split at h
      · rename_i hc; cases h; exact hc.2.1
      · cases h
    · cases h
  · split at h
    · split at h
      · rename_i hc; cases h; exact hc.2.1
      · cases h
    · cases h
  · split at h
    · split at h
      · rename_i hc; cases h; exact hc.2.2
      · cases h
    · cases h
  · cases h

theorem bit_prim {c : Ctor} {o : Bitwise.Op} (hc : Bitwise.ofCtor c = some o) (ann : List Annot)
    (ity : IntegerType) (n₁ n₂ : Int) (tags : Mem.Concrete.Tags) :
    primitive (.ctor c) [runtimeValue (.ctype (.mk ann (.basic (.integer ity)))),
      .object (.integer n₁), .object (.integer n₂)] tags = .ok (integer (o.apply n₁ n₂)) := by
  cases c <;> simp [Bitwise.ofCtor] at hc <;> subst hc <;>
    simp [primitive, runtimeValue, intType, Bitwise.Op.apply] <;> rfl

theorem catch_ok {ity : IntegerType} (hs : supported ity = true) {op : IntOp}
    (har : Guard.arith op = true) {x y : Int} (hr : Fits ity (Guard.apply op x y))
    (tags : Mem.Concrete.Tags) :
    primitive (.catchInt ity op) [.object (.integer x), .object (.integer y)] tags =
      .ok (.object (.integer (Guard.apply op x y))) := by
  obtain ⟨lo, hi⟩ := hr
  have lo' : (TyActions.bounds ity).1 ≤ Guard.apply op x y := lo
  have hi' : Guard.apply op x y ≤ (TyActions.bounds ity).2 := hi
  simp [primitive, TyActions.registeredBounds hs, Guard.integerOp_arith har, integer, lo', hi']
  rfl

theorem catch_ub {ity : IntegerType} (hs : supported ity = true) {op : IntOp}
    (har : Guard.arith op = true) {x y : Int} (hr : ¬ Fits ity (Guard.apply op x y))
    (tags : Mem.Concrete.Tags) :
    primitive (.catchInt ity op) [.object (.integer x), .object (.integer y)] tags =
      .error (.ub .unknown .UB036_exceptional_condition) := by
  rw [TyConv.fits_iff, not_and_or, not_le, not_le] at hr
  simp [primitive, TyActions.registeredBounds hs, Guard.integerOp_arith har]
  rcases hr with hr | hr
  · simp [show ¬ ((TyActions.bounds ity).1 ≤ Guard.apply op x y) by omega]; rfl
  · simp [show ¬ (Guard.apply op x y ≤ (TyActions.bounds ity).2) by omega]; rfl

theorem wrap_prim {ity : IntegerType} (hs : supported ity = true) {op : IntOp}
    (har : Guard.arith op = true) (x y : Int) (tags : Mem.Concrete.Tags) :
    primitive (.wrapInt ity op) [.object (.integer x), .object (.integer y)] tags =
      .ok (.object (.integer (cv ity (Guard.apply op x y)))) := by
  simp [primitive, TyActions.registeredBounds hs, Guard.integerOp_arith har, integer, cv]
  rfl

/-- The environment of the arm body. -/
abbrev armEnv (x y : Sym) (n₁ n₂ : Int) (env : Env) : Env :=
  extendEnv [(x, .object (.integer n₁)), (y, .object (.integer n₂))] env

theorem bodyG_args {x y : Sym} {p q : Pure} {ity : IntegerType} (ne : y.key ≠ x.key)
    (hp : convTy file x p = some ity) (hq : convTy file y q = some ity) (hs : supported ity = true)
    (env : Env) (n₁ n₂ : Int) :
    Ev file tags (armEnv x y n₁ n₂ env) (.inr [p, q])
      (.inr [.object (.integer (cv ity n₁)), .object (.integer (cv ity n₂))]) :=
  .cons (convTy_ev hp hs (lookup_pair_first rfl)) (.cons (convTy_ev hq hs (lookup_pair_second rfl ne)) .nil)

/-- A defined arm body evaluates to its value. -/
theorem bodyG_eval {x y : Sym} {p : Pure} {g : G} (h : bodyG file x y p = some g)
    (ne : y.key ≠ x.key) (env : Env) {n₁ n₂ : Int} (ok : g.Ok n₁ n₂) :
    Ev file tags (armEnv x y n₁ n₂ env) (.inl p) (.inl (IntExpr.spec (g.val n₁ n₂))) := by
  unfold bodyG at h
  split at h
  · split at h
    · rename_i _ _ ity op pp pq hc
      cases h
      obtain ⟨hp, hq, hs, har, -⟩ := hc
      exact .ctor (.cons (.catchInt (bodyG_args ne hp hq hs env n₁ n₂) (catch_ok hs har ok tags)) .nil)
        (by simp [primitive]; rfl)
    · cases h
  · split at h
    · rename_i _ _ ity op pp pq hc
      cases h
      obtain ⟨hp, hq, hs, har⟩ := hc
      exact .ctor (.cons (.wrapInt (bodyG_args ne hp hq hs env n₁ n₂) (wrap_prim hs har _ _ tags)) .nil)
        (by simp [primitive]; rfl)
    · cases h
  · split at h
    · rename_i ity ity' hp hq
      split at h
      · rename_i hc
        cases h
        obtain ⟨rfl, hs, hr⟩ := hc
        have args := bodyG_args (tags := tags) ne hp hq hs env n₁ n₂
        simp only [G.val]
        split
        · rename_i hh
          refine .ifTrue (.op args ?_) (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
          simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl
        · rename_i hh
          refine .ifFalse (.op args ?_) (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
          simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl
      · cases h
    · cases h
  · split at h
    · rename_i ity ity' hp hq
      split at h
      · rename_i hc
        cases h
        obtain ⟨rfl, hs, hr⟩ := hc
        have args := bodyG_args (tags := tags) ne hp hq hs env n₁ n₂
        simp only [G.val]
        split
        · rename_i hh
          refine .ifFalse (.not (.cons (.op (v := .true) args ?_) .nil) (by simp [primitive]; rfl))
            (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
          simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl
        · rename_i hh
          refine .ifTrue (.not (.cons (.op (v := .false) args ?_) .nil) (by simp [primitive]; rfl))
            (.ctor (.cons .val .nil) (by simp [primitive]; rfl))
          simp [primitive, Guard.integerBin_rel hr, hh, boolean]; rfl
      · cases h
    · cases h
  · split at h
    · rename_i o ho
      split at h
      · rename_i hc
        cases h
        obtain ⟨hp, hq, hs⟩ := hc
        exact .ctor (.cons (.ctor (.cons .val (.cons (convTy_ev hp hs (lookup_pair_first rfl))
          (.cons (convTy_ev hq hs (lookup_pair_second rfl ne)) .nil))) (bit_prim ho _ _ _ _ _)) .nil)
          (by simp [primitive, integer]; rfl)
      · cases h
    · cases h
  · cases h

/-- The pieces of a recognised guard. -/
theorem tguard_parts {a b : Sym} {p : Pure} {g : G} (h : tguard file a b p = some g) :
    ∃ (ann ann₁ pa pb : List Annot) (a' b' : Sym) (bs : List (Pattern Sym × Pure)),
      p = .mk ann () (.case_ (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')]))
        bs) ∧ a'.key = a.key ∧ b'.key = b.key ∧ b.key ≠ a.key ∧
      ∃ (x y : Sym) (body : Pure), y.key ≠ x.key ∧ bodyG file x y body = some g ∧
        ∀ (n₁ n₂ : Int), selectCase (.tuple [IntExpr.spec n₁, IntExpr.spec n₂]) bs =
          some ([(x, .object (.integer n₁)), (y, .object (.integer n₂))], body) := by
  unfold tguard at h
  split at h
  · rename_i ann ann₁ pa a' pb b' tann tx bs x bx ty sann y cy body rest
    split at h
    · rename_i cond
      obtain ⟨e1, e2, ne, ne'⟩ := cond
      exact ⟨ann, ann₁, pa, pb, a', b', _, rfl, e1, e2, ne, x, y, body, ne', h,
        fun n₁ n₂ => by simp [selectCase, matchPattern, matchPatterns]⟩
    · cases h
  · cases h

/-- **A defined guard** evaluates to `Specified` of its value. -/
theorem tguard_eval {a b : Sym} {p : Pure} {g : G} (h : tguard file a b p = some g)
    (env : Env) {n₁ n₂ : Int} (ok : g.Ok n₁ n₂) :
    Ev file tags (operands a b n₁ n₂ env) (.inl p) (.inl (IntExpr.spec (g.val n₁ n₂))) := by
  obtain ⟨ann, ann₁, pa, pb, a', b', bs, rfl, e1, e2, ne, x, y, body, ne', hb, hsel⟩ := tguard_parts h
  exact .case_ (.ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne))
    .nil)) (by simp [primitive]; rfl)) (hsel n₁ n₂) (bodyG_eval hb ne' _ ok)

/-- **An undefined guard** runs, by local steps from any continuation, to the
`catch_exceptional_condition` whose request is undefined behaviour. -/
theorem tguard_fails {labels : Labels} {a b : Sym} {p : Pure} {g : G}
    (h : tguard file a b p = some g) (env : Env) {n₁ n₂ : Int} (bad : ¬ g.Ok n₁ n₂) (wc : Bool)
    (k : List Frame) (m : Mem.Concrete.State) :
    ArenaFail.Fails file labels wc ⟨.pureExpr p (operands a b n₁ n₂ env), k, m⟩ IntExpr.overflow := by
  obtain ⟨ann, ann₁, pa, pb, a', b', bs, rfl, e1, e2, ne, x, y, body, ne', hb, hsel⟩ := tguard_parts h
  let env₁ := operands a b n₁ n₂ env
  let env₂ := armEnv x y n₁ n₂ env₁
  have scrut : Ev file (tagsOf file m) env₁
      (.inl (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'), .mk pb () (.sym b')])))
      (.inl (.tuple [IntExpr.spec n₁, IntExpr.spec n₂])) :=
    .ctor (.cons (.sym (lookup_pair_first e1)) (.cons (.sym (lookup_pair_second e2 ne)) .nil))
      (by simp [primitive]; rfl)
  have pre : LocalReaches file labels wc ⟨.pureExpr (.mk ann () (.case_ (.mk ann₁ () (.ctor .tuple
      [.mk pa () (.sym a'), .mk pb () (.sym b')])) bs)) env₁, k, m⟩ ⟨.pureExpr body env₂, k, m⟩ := by
    refine .head (.next (c' := .pureExpr (.mk ann₁ () (.ctor .tuple [.mk pa () (.sym a'),
        .mk pb () (.sym b')])) env₁) (k' := .pureCase bs env₁ :: k)
      (by simp [requestAux, awaitsScheduling, env₁]) (PureLocal.plain_pureExpr _ _)) ?_
    refine (PureEvalExt.ev_local file _ scrut _ m rfl).trans ?_
    exact .single (.next (by simp [requestAux, awaitsScheduling, hsel n₁ n₂, env₂])
      (PureLocal.plain_pureExpr _ _))
  unfold bodyG at hb
  split at hb
  · split at hb
    · rename_i q₁ q₂ ity op pp pq hc
      cases hb
      obtain ⟨hp, hq, hs, har, -⟩ := hc
      let CATCH : Pure := .mk q₂ () (.catchExceptionalCondition ity op pp pq)
      let k₁ : List Frame := .arguments (.ctor .specified) [] [] env₂ :: k
      refine ⟨⟨.apply (.catchInt ity op) [.object (.integer (cv ity n₁)), .object (.integer (cv ity n₂))],
        k₁, m⟩, ?_, (fun v hv => by cases hv), .inl ?_⟩
      · refine pre.trans ?_
        refine .head (.next (c' := .pureExpr CATCH env₂) (k' := k₁)
          (by simp [requestAux, awaitsScheduling, arguments, k₁, CATCH]) (PureLocal.plain_pureExpr _ _)) ?_
        refine (PureLocal.arguments_local file (.catchInt ity op) [pp, pq] env₂ k₁ m wc
          (by simp [requestAux, awaitsScheduling, CATCH])).trans ?_
        simpa using PureEvalExt.args_local file _ (bodyG_args ne' hp hq hs env₁ n₁ n₂)
          (.catchInt ity op) [] k₁ m rfl (wc := wc) (labels := labels)
      · rw [PureLocal.requestAux_apply file (op := .catchInt ity op) trivial, catch_ub hs har bad]
    · cases hb
  · split at hb
    · cases hb; exact absurd trivial bad
    · cases hb
  · split at hb
    · split at hb
      · cases hb; exact absurd trivial bad
      · cases hb
    · cases hb
  · split at hb
    · split at hb
      · cases hb; exact absurd trivial bad
      · cases hb
    · cases hb
  · split at hb
    · split at hb
      · cases hb; exact absurd trivial bad
      · cases hb
    · cases hb
  · cases hb

/-! ## Reads of typed locals -/

variable {labels : Labels}

/-- `let weak p = pure(x) in load(T, p')`: the read of the local `x` of type `T`. -/
abbrev loadExpr (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x : Sym) (l : Loc)
    (u : Unit) (ity : IntegerType) : EE :=
  .mk a0 (.wseq (.mk pa (.base (some p, pt))) (.mk a1 (.pure (.mk a2 () (.sym x))))
    (.mk la (.action (.mk .pos (.mk l u (.load (TyActions.tyVal a3 c1 ity) (.mk a4 () (.sym p')) .na))))))

theorem requestAux_load_apply (ann : List Annot) {ity : IntegerType} (hs : supported ity = true)
    (k : List Frame) {m : Mem.Concrete.State} {id addr n : Int}
    (slot : TSlot m id addr (width ity) n) (hn : Fits ity n) :
    ∃ a : Access, a.write = false ∧
      requestAux file labels m (.apply (.memory .load) [.ctype (Mem.Concrete.tyType ann ity),
        .object (.pointer (.allocated id addr))]) k false =
      .memory "Load" {m with lastUsed := some id} (.value (.loaded (.specified (.integer n))))
        (.annotations [a] :: k) := by
  refine ⟨⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none, [], false,
    addr, width ity⟩, rfl, ?_⟩
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, fromMemory,
    Mem.Concrete.load_ty (TyActions.layout_of hs) _ ann slot.live slot.plain hn slot.bytes,
    Mem.Concrete.access_ty (TyActions.layout_of hs) _ ann slot.live, bind,
    Except.bind, pure, Except.pure]
  rfl

/-- **The read of a typed local**, outside calls and over any continuation: local steps to
`Specified n`, the value of the slot `x` points to, with one read access. -/
theorem load_local (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x : Sym) (l : Loc)
    (u : Unit) {ity : IntegerType} (hs : supported ity = true) (hp' : p'.key = p.key) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : Fits ity n) (slot : TSlot m id addr (width ity) n) :
    ∃ a m', a.write = false ∧ Touched m m' ∧
      LocalReaches file labels false
        ⟨.effectExpr (loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x l u ity) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer n))), .annotations [a] :: k, m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated id addr))
  let LOAD : EE := .mk la (.action (.mk .pos (.mk l u (.load (TyActions.tyVal a3 c1 ity)
    (.mk a4 () (.sym p')) .na))))
  let env₁ := extendEnv [(p, ptr)] env
  have hp : env₁.lookup p' = some ptr := ConvInt.lookup_one hp'
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x l u ity) env, k, m⟩
      ⟨.effectExpr (.mk a1 (.pure (.mk a2 () (.sym x)))) env,
        .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq m a0 _ _ _ env k false) (LoadTask.plain_effectExpr _ env))
  obtain ⟨l₁, s₂⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) a1 a2 x
    env hx (.effectBind (.mk pa (.base (some p, pt))) LOAD env :: k) m
  let m₁ : Mem.Concrete.State := {m with currentLocation := l₁}
  have s₃ : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa (.base (some p, pt))) LOAD env :: k, m₁⟩
      ⟨.effectExpr LOAD env₁, k, m₁⟩ :=
    .single (.next (LoadTask.requestAux_bind m₁ pa p pt ptr LOAD env k false)
      (LoadTask.plain_effectExpr _ _))
  obtain ⟨l₂, s₄⟩ := LoadTask.focus_local (file := file) (labels := labels) (wc := false)
    (LoadTask.plain_pureExpr (TyActions.tyVal a3 c1 ity) env₁)
    (LoadTask.requestAux_load m₁ la l u (TyActions.tyVal a3 c1 ity) (.mk a4 () (.sym p')) env₁ k false)
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l₂}
  have s₅ : LocalReaches file labels false
      ⟨.pureExpr (TyActions.tyVal a3 c1 ity) env₁,
        .arguments (.memory .load) [] [.mk a4 () (.sym p')] env₁ :: k, m₂⟩
      ⟨.apply (.memory .load) [.ctype (Mem.Concrete.tyType c1 ity), ptr], k, m₂⟩ :=
    .head (.next (LoadTask.requestAux_val m₂ a3 _ env₁ _ false) (LoadTask.plain_value _))
      (.head (.next (LoadTask.requestAux_argument m₂ _ [] _ _ [] env₁ k false)
        (LoadTask.plain_pureExpr _ _))
        (.head (.next (LoadTask.requestAux_sym m₂ a4 p' env₁ hp _ false) (LoadTask.plain_value _))
          (.single (.next (LoadTask.requestAux_last_argument m₂ _ _ _ env₁ k false)
            (LoadTask.plain_apply _ _)))))
  have slot₂ : TSlot m₂ id addr (width ity) n :=
    TyActions.Touched.slot (m := m) ⟨l₂, m.lastUsed, rfl⟩ slot
  obtain ⟨a, ha, hload⟩ := requestAux_load_apply (file := file) (labels := labels) c1 hs k slot₂ hn
  refine ⟨a, {m₂ with lastUsed := some id}, ha, ⟨l₂, some id, rfl⟩, ?_⟩
  exact s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail (.memory hload)))))

end Silmaril.Compile.Core.Verified.TyGuard
