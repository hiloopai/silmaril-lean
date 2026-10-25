module

public import Silmaril.Wasm.Binaryen.GlobReadRel

@[expose] public section

/-! # Directize: the simulation relation

Directize (`Pass/Directize.lean`) replaces `i32.const k; call_indirect t y` by `call fx`
(and `return_call_indirect` by `return_call`) when slot `k` of table `t` holds `ref.func`
of function `fx`. Unlike a global read (`Binaryen/GlobReadRel.lean`) the site is two
instructions against one, so the relation is not pointwise: `GIL` and `GL` have
list-level site constructors.

* `GIL.site`: `i32.const k; call_indirect t y ~ call fx` in the code of a frame of the
  rewritten module's instance `mi`, when the static check `ok t k y fx` holds.
* `GL.s0`: the same site in administrative code. When `call_indirect` unfolds, the right
  side steps `call` (`GL.s1`: `i32.const k; table.get t; ref.cast; call_ref y ~
  ref.func a; call_ref <d>`); `table.get` and `ref.cast` are left-only steps that shrink
  the code (`GL.s2`, then the pointwise `ref.func a; call_ref y ~ ref.func a; call_ref
  <d>`).
* `GA.ann`/`GA.retAnn`: call annotations are irrelevant (`Admin.IsCallRef`), so any two
  `call_ref` forms are related.
* `GL.deadTrap`/`GL.deadThrow`: the code after a trap or a thrown exception is dead and
  may differ (a bubble may discard part of a site on the left).

The store side is the invariant `DInv`: every statically known slot holds the callee's
address, and the callee has the type of the call (the cast fact).
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-! ## Call and return-call forms -/

/-- `call_indirect` (`false`) or `return_call_indirect` (`true`). -/
def ciI : Bool → TableIdx → TypeIdx → Instr
  | false, t, y => .callIndirect t y
  | true, t, y => .returnCallIndirect t y

/-- `call` or `return_call`. -/
def clI : Bool → FuncIdx → Instr
  | false, x => .call x
  | true, x => .returnCall x

/-- `call_ref` or `return_call_ref` with an index. -/
def crI : Bool → TypeIdx → Instr
  | false, y => .callRef y
  | true, y => .returnCallRef y

/-- `call_ref` or `return_call_ref` with a defined type. -/
def crT : Bool → DefType → Admin
  | false, d => .callRefType d
  | true, d => .returnCallRefType d

/-- The cast of `call_indirect t y`. -/
def castY (y : TypeIdx) : Instr := .refCast ⟨true, .typeIdx y⟩

/-- The static facts of a site: slot `k` of table `t` is known to hold function `fx`, of
type `y`. -/
abbrev SiteOk := TableIdx → BitVec 32 → TypeIdx → FuncIdx → Prop

variable (ok : SiteOk) (mi : ModuleInst)

mutual
/-- Instructions under frames of instance `cur`: equal up to sites. -/
inductive GI (cur : ModuleInst) : Instr → Instr → Prop where
  | flat (i : Instr) : GI cur i i
  | block {bt : BlockType} {b b' : List Instr} (h : GIL cur b b') : GI cur (.block bt b) (.block bt b')
  | loop {bt : BlockType} {b b' : List Instr} (h : GIL cur b b') : GI cur (.loop bt b) (.loop bt b')
  | if_ {bt : BlockType} {t t' e e' : List Instr} (h₁ : GIL cur t t') (h₂ : GIL cur e e') :
      GI cur (.if_ bt t e) (.if_ bt t' e')
  | tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr} (h : GIL cur b b') :
      GI cur (.tryTable bt cs b) (.tryTable bt cs b')
/-- Instruction sequences: pointwise, and sites. -/
inductive GIL (cur : ModuleInst) : List Instr → List Instr → Prop where
  | nil : GIL cur [] []
  | cons {i i' : Instr} {is is' : List Instr} (h : GI cur i i') (t : GIL cur is is') :
      GIL cur (i :: is) (i' :: is')
  | site {r : Bool} {t : TableIdx} {k : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
      {is is' : List Instr} (hq : cur = mi) (hok : ok t k y fx) (h : GIL cur is is') :
      GIL cur (.intConst .i32 k :: ciI r t y :: is) (clI r fx :: is')
end

mutual
/-- Administrative instructions; an activation re-indexes its body at its own instance. -/
inductive GA : ModuleInst → Admin → Admin → Prop where
  | plain {cur : ModuleInst} {i i' : Instr} (h : GI ok mi cur i i') : GA cur (.plain i) (.plain i')
  | ref (cur : ModuleInst) (r : Ref) : GA cur (.ref r) (.ref r)
  | ann {cur : ModuleInst} {a b : Admin} (ha : a.IsCallRef) (hb : b.IsCallRef) : GA cur a b
  | retAnn {cur : ModuleInst} {a b : Admin} (ha : a.IsReturnCallRef) (hb : b.IsReturnCallRef) :
      GA cur a b
  | label {cur : ModuleInst} {n : Nat} {c c' : List Instr} {b b' : List Admin}
      (hc : GIL ok mi cur c c') (h : GL cur b b') : GA cur (.label n c b) (.label n c' b')
  | handler {cur : ModuleInst} {n : Nat} {cs : List Catch} {b b' : List Admin} (h : GL cur b b') :
      GA cur (.handler n cs b) (.handler n cs b')
  | frame {cur : ModuleInst} {n : Nat} {F : Frame} {b b' : List Admin} (h : GL F.module b b') :
      GA cur (.frame n F b) (.frame n F b')
  | trap (cur : ModuleInst) : GA cur .trap .trap
/-- Administrative sequences: pointwise, the three site states, and dead code. -/
inductive GL : ModuleInst → List Admin → List Admin → Prop where
  | nil (cur : ModuleInst) : GL cur [] []
  | cons {cur : ModuleInst} {a b : Admin} {os ns : List Admin} (h : GA cur a b) (t : GL cur os ns) :
      GL cur (a :: os) (b :: ns)
  | s0 {cur : ModuleInst} {r : Bool} {t : TableIdx} {k : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
      {os ns : List Admin} (hq : cur = mi) (hok : ok t k y fx) (h : GL cur os ns) :
      GL cur (constI32 k :: .plain (ciI r t y) :: os) (.plain (clI r fx) :: ns)
  | s1 {cur : ModuleInst} {r : Bool} {t : TableIdx} {k : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
      {a : Nat} {d : DefType} {os ns : List Admin} (hq : cur = mi) (hok : ok t k y fx)
      (ha : mi.funcs[fx.toNat]? = some a) (h : GL cur os ns) :
      GL cur (constI32 k :: .plain (.tableGet t) :: .plain (castY y) :: .plain (crI r y) :: os)
        (.ref (.func a) :: crT r d :: ns)
  | s2 {cur : ModuleInst} {r : Bool} {t : TableIdx} {k : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
      {a : Nat} {d : DefType} {os ns : List Admin} (hq : cur = mi) (hok : ok t k y fx)
      (ha : mi.funcs[fx.toNat]? = some a) (h : GL cur os ns) :
      GL cur (.ref (.func a) :: .plain (castY y) :: .plain (crI r y) :: os)
        (.ref (.func a) :: crT r d :: ns)
  | deadTrap {cur : ModuleInst} {os ns : List Admin} (hr : os ≠ []) :
      GL cur (.trap :: os) (.trap :: ns)
  | deadThrow {cur : ModuleInst} {a : Nat} {os ns : List Admin} (hr : os ≠ []) :
      GL cur (.ref (.exn a) :: .plain .throwRef :: os) (.ref (.exn a) :: .plain .throwRef :: ns)
end

variable {ok mi}

/-! ## Reflexivity and sequences -/

theorem GIL.refl {cur : ModuleInst} : ∀ is : List Instr, GIL ok mi cur is is
  | [] => .nil
  | i :: is => .cons (.flat i) (GIL.refl is)

mutual
theorem GA.refl {cur : ModuleInst} : ∀ a : Admin, GA ok mi cur a a
  | .plain i => .plain (.flat i)
  | .ref r => .ref _ r
  | .callRefType _ => .ann trivial trivial
  | .returnCallRefType _ => .retAnn trivial trivial
  | .label _ c b => .label (GIL.refl c) (GL.refl b)
  | .handler _ _ b => .handler (GL.refl b)
  | .frame _ _ b => .frame (GL.refl b)
  | .trap => .trap _
theorem GL.refl {cur : ModuleInst} : ∀ l : List Admin, GL ok mi cur l l
  | [] => .nil _
  | a :: l => .cons (GA.refl a) (GL.refl l)
end

theorem GIL.append {cur : ModuleInst} : ∀ {A A' B B' : List Instr}, GIL ok mi cur A A' →
    GIL ok mi cur B B' → GIL ok mi cur (A ++ B) (A' ++ B')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (GIL.append t h')
  | _, _, _, _, .site hq hok t, h' => .site hq hok (GIL.append t h')

theorem expression_ciI (r : Bool) (t : TableIdx) (y : TypeIdx) (k : BitVec 32) (is : List Instr) :
    expression (.intConst .i32 k :: ciI r t y :: is) =
      constI32 k :: .plain (ciI r t y) :: expression is := rfl

theorem GL.of_GIL {cur : ModuleInst} : ∀ {is is' : List Instr}, GIL ok mi cur is is' →
    GL ok mi cur (expression is) (expression is')
  | _, _, .nil => .nil _
  | _, _, .cons h t => .cons (.plain h) (GL.of_GIL t)
  | _, _, .site hq hok t => .s0 hq hok (GL.of_GIL t)

theorem GL.append {cur : ModuleInst} : ∀ {A B nA nB : List Admin}, GL ok mi cur A nA →
    GL ok mi cur B nB → GL ok mi cur (A ++ B) (nA ++ nB)
  | _, _, _, _, .nil _, h => h
  | _, _, _, _, .cons h t, h' => .cons h (GL.append t h')
  | _, _, _, _, .s0 hq hok t, h' => .s0 hq hok (GL.append t h')
  | _, _, _, _, .s1 hq hok ha t, h' => .s1 hq hok ha (GL.append t h')
  | _, _, _, _, .s2 hq hok ha t, h' => .s2 hq hok ha (GL.append t h')
  | _, _, _, _, .deadTrap hr, _ => .deadTrap (by simp [hr])
  | _, _, _, _, .deadThrow hr, _ => .deadThrow (by simp [hr])

theorem GL.of_vals {cur : ModuleInst} (vs : List Val) : GL ok mi cur (vals vs) (vals vs) :=
  GL.refl _

/-! ## Values -/

theorem isCallRef_val {v : Val} (h : v.toAdmin.IsCallRef) : False := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.IsCallRef] at h

theorem isReturnCallRef_val {v : Val} (h : v.toAdmin.IsReturnCallRef) : False := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Admin.IsReturnCallRef] at h

theorem GI.eq_of_flat {cur : ModuleInst} {i i' : Instr} (h : GI ok mi cur i i')
    (hs : structuredInstr i = false) : i' = i := by
  cases h with
  | flat => rfl
  | _ => simp [structuredInstr] at hs

theorem GA.val_inv {cur : ModuleInst} {v : Val} {b : Admin} (h : GA ok mi cur v.toAdmin b) :
    b = v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin] at h ⊢ <;>
    first
    | (cases h with
      | plain h => exact congrArg Admin.plain (GI.eq_of_flat h rfl)
      | ann ha => simp [Admin.IsCallRef] at ha
      | retAnn ha => simp [Admin.IsReturnCallRef] at ha)
    | (cases h with
      | ref => rfl
      | ann ha => simp [Admin.IsCallRef] at ha
      | retAnn ha => simp [Admin.IsReturnCallRef] at ha)

/-- A value is not the head of a site. -/
theorem vals_cons_eq {V : List Val} {e x : Admin} {rest os : List Admin}
    (hx : x.val? = none) (h : vals V ++ e :: rest = x :: os) : V = [] ∧ e = x ∧ rest = os := by
  cases V with
  | nil => simpa using h
  | cons v V =>
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    have := congrArg Admin.val? h.1
    rw [Admin.val?_toAdmin, hx] at this
    cases this

theorem Admin.eq_of_val? {a : Admin} {v : Val} (h : a.val? = some v) : a = v.toAdmin := by
  unfold Admin.val? at h
  split at h <;> cases h <;> rfl

theorem GL.eq_of_vals {cur : ModuleInst} : ∀ {l ns : List Admin}, GL ok mi cur l ns →
    (∀ x ∈ l, x.val? ≠ none) → ns = l
  | _, _, .nil _, _ => rfl
  | _, _, .cons h t, hv => by
    obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp (hv _ List.mem_cons_self)
    have e := Admin.eq_of_val? hv'
    subst e
    rw [GA.val_inv h, GL.eq_of_vals t fun x hx => hv x (List.mem_cons_of_mem _ hx)]
  | _, _, .s0 (r := r) (t := t) (y := y) .., hv =>
    absurd (hv (.plain (ciI r t y)) (by simp)) (by cases r <;> simp [ciI, Admin.val?])
  | _, _, .s1 (t := t) .., hv => absurd (hv (.plain (.tableGet t)) (by simp)) (by simp [Admin.val?])
  | _, _, .s2 (y := y) .., hv => absurd (hv (.plain (castY y)) (by simp)) (by simp [castY, Admin.val?])
  | _, _, .deadTrap _, hv => absurd (hv .trap (by simp)) (by simp [Admin.val?])
  | _, _, .deadThrow _, hv => absurd (hv (.plain .throwRef) (by simp)) (by simp [Admin.val?])

theorem GL.vals_inv {cur : ModuleInst} {vs : List Val} {ns : List Admin}
    (h : GL ok mi cur (vals vs) ns) : ns = vals vs :=
  GL.eq_of_vals h fun x hx => by
    simp only [vals, List.mem_map] at hx
    obtain ⟨v, -, rfl⟩ := hx
    simp

/-! ## Splitting at the first non-value -/

variable (ok mi) in
/-- The shapes of the right code for left code `vals V ++ e :: rest`: pointwise at `e`, dead
code after a trap or a thrown exception, or one of the three site states. -/
def Split (cur : ModuleInst) (V : List Val) (e : Admin) (rest ns : List Admin) : Prop :=
  (∃ e' rest', ns = vals V ++ e' :: rest' ∧ GA ok mi cur e e' ∧ GL ok mi cur rest rest') ∨
  (∃ rest', ns = vals V ++ e :: rest' ∧ rest ≠ [] ∧
    (e = .trap ∨ (e = .plain .throwRef ∧ ∃ V₀ a, V = V₀ ++ [.ref (.exn a)]))) ∨
  (∃ V₀ r t k y fx ns', V = V₀ ++ [.i32 k] ∧ e = .plain (ciI r t y) ∧ cur = mi ∧ ok t k y fx ∧
    ns = vals V₀ ++ .plain (clI r fx) :: ns' ∧ GL ok mi cur rest ns') ∨
  (∃ V₀ r t k y fx a d os ns', V = V₀ ++ [.i32 k] ∧ e = .plain (.tableGet t) ∧
    rest = .plain (castY y) :: .plain (crI r y) :: os ∧ cur = mi ∧ ok t k y fx ∧
    mi.funcs[fx.toNat]? = some a ∧ ns = vals V₀ ++ .ref (.func a) :: crT r d :: ns' ∧
    GL ok mi cur os ns') ∨
  (∃ V₀ r t k y fx a d os ns', V = V₀ ++ [.ref (.func a)] ∧ e = .plain (castY y) ∧
    rest = .plain (crI r y) :: os ∧ cur = mi ∧ ok t k y fx ∧
    mi.funcs[fx.toNat]? = some a ∧ ns = vals V₀ ++ .ref (.func a) :: crT r d :: ns' ∧
    GL ok mi cur os ns')

theorem Split.cons {cur : ModuleInst} {V : List Val} {e : Admin} {rest ns : List Admin} (v : Val)
    (h : Split ok mi cur V e rest ns) : Split ok mi cur (v :: V) e rest (v.toAdmin :: ns) := by
  rcases h with ⟨e', rest', rfl, h₁, h₂⟩ | ⟨rest', rfl, h₁, h₂⟩ |
      ⟨V₀, r, t, k, y, fx, ns', rfl, h₁, h₂, h₃, rfl, h₄⟩ |
      ⟨V₀, r, t, k, y, fx, a, d, os, ns', rfl, h₁, h₂, h₃, h₄, h₅, rfl, h₆⟩ |
      ⟨V₀, r, t, k, y, fx, a, d, os, ns', rfl, h₁, h₂, h₃, h₄, h₅, rfl, h₆⟩
  · exact .inl ⟨e', rest', by simp [vals], h₁, h₂⟩
  · refine .inr (.inl ⟨rest', by simp [vals], h₁, ?_⟩)
    rcases h₂ with h₂ | ⟨h₂, V₀, a, rfl⟩
    · exact .inl h₂
    · exact .inr ⟨h₂, v :: V₀, a, rfl⟩
  · exact .inr (.inr (.inl ⟨v :: V₀, r, t, k, y, fx, ns', rfl, h₁, h₂, h₃, by simp [vals], h₄⟩))
  · exact .inr (.inr (.inr (.inl ⟨v :: V₀, r, t, k, y, fx, a, d, os, ns', rfl, h₁, h₂, h₃, h₄, h₅,
      by simp [vals], h₆⟩)))
  · exact .inr (.inr (.inr (.inr ⟨v :: V₀, r, t, k, y, fx, a, d, os, ns', rfl, h₁, h₂, h₃, h₄, h₅,
      by simp [vals], h₆⟩)))

theorem val_eq_of_toAdmin {v : Val} {x : Admin} {w : Val} (hx : x.val? = some w)
    (h : v.toAdmin = x) : v = w := by
  have := congrArg Admin.val? h
  rw [Admin.val?_toAdmin, hx] at this
  exact Option.some.inj this

/-- **The split at the first non-value.** -/
theorem GL.split {cur : ModuleInst} : ∀ {V : List Val} {e : Admin} {rest ns : List Admin},
    e.val? = none → GL ok mi cur (vals V ++ e :: rest) ns → Split ok mi cur V e rest ns
  | [], e, rest, ns, he, h => by
    simp only [vals, List.map_nil, List.nil_append] at h
    cases h with
    | cons h t => exact .inl ⟨_, _, rfl, h, t⟩
    | s0 => simp [constI32, Val.toAdmin, Val.i32, Admin.val?] at he
    | s1 => simp [constI32, Val.toAdmin, Val.i32, Admin.val?] at he
    | s2 => simp [Admin.val?] at he
    | deadTrap hr => exact .inr (.inl ⟨_, rfl, hr, .inl rfl⟩)
    | deadThrow => simp [Admin.val?] at he
  | v :: V, e, rest, ns, he, h => by
    generalize hL : vals (v :: V) ++ e :: rest = L at h
    simp only [vals, List.map_cons, List.cons_append] at hL
    cases h with
    | nil => cases hL
    | cons ha t =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hL
      rw [GA.val_inv ha]
      exact (GL.split he t).cons v
    | s0 hq hok t =>
      obtain ⟨h₁, h₂⟩ := List.cons.inj hL
      obtain rfl := val_eq_of_toAdmin (w := .i32 _) rfl h₁
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_eq (V := V) (by cases ‹Bool› <;> rfl) h₂
      exact .inr (.inr (.inl ⟨[], _, _, _, _, _, _, rfl, rfl, hq, hok, rfl, t⟩))
    | s1 hq hok ha t =>
      obtain ⟨h₁, h₂⟩ := List.cons.inj hL
      obtain rfl := val_eq_of_toAdmin (w := .i32 _) rfl h₁
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_eq (V := V) rfl h₂
      exact .inr (.inr (.inr (.inl ⟨[], _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, hq, hok, ha,
        rfl, t⟩)))
    | s2 hq hok ha t =>
      obtain ⟨h₁, h₂⟩ := List.cons.inj hL
      obtain rfl := val_eq_of_toAdmin (w := .ref (.func _)) rfl h₁
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_eq (V := V) rfl h₂
      exact .inr (.inr (.inr (.inr ⟨[], _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, hq, hok, ha,
        rfl, t⟩)))
    | deadTrap hr =>
      obtain ⟨h₁, -⟩ := List.cons.inj hL
      have := congrArg Admin.val? h₁
      rw [Admin.val?_toAdmin] at this
      cases this
    | deadThrow hr =>
      obtain ⟨h₁, h₂⟩ := List.cons.inj hL
      obtain rfl := val_eq_of_toAdmin (w := .ref (.exn _)) rfl h₁
      obtain ⟨rfl, rfl, rfl⟩ := vals_cons_eq (V := V) rfl h₂
      exact .inr (.inl ⟨_, rfl, hr, .inr ⟨rfl, [], _, rfl⟩⟩)

theorem GL.result_inv {cur : ModuleInst} {r : Result} {ns : List Admin}
    (h : GL ok mi cur r.toAdmin ns) : ns = r.toAdmin := by
  cases r with
  | values vs => exact GL.vals_inv h
  | trap =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t =>
      cases h with
      | trap => cases t; rfl
      | ann ha => exact ha.elim
      | retAnn ha => exact ha.elim
    | deadTrap hr => exact absurd rfl hr
  | throw a =>
    simp only [Result.toAdmin] at h ⊢
    cases h with
    | cons h t =>
      cases h with
      | ref =>
        cases t with
        | cons h' t' =>
          cases h' with
          | plain h' => rw [GI.eq_of_flat h' rfl]; cases t'; rfl
          | ann ha => exact ha.elim
          | retAnn ha => exact ha.elim
      | ann ha => exact ha.elim
      | retAnn ha => exact ha.elim
    | deadThrow hr => exact absurd rfl hr

/-! ## Calls -/

theorem isCallRef_retToCallIn {c : Admin} (h : c.IsReturnCallRef) (m : ModuleInst) :
    (c.retToCallIn m).IsCallRef := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · simp only [Admin.retToCallIn]; split <;> trivial
  · trivial
  · exact h.elim

theorem isCallRef_crT {r : Bool} {d : DefType} (h : r = false) : (crT r d).IsCallRef := by
  subst h; trivial

theorem crI_flat (r : Bool) (y : TypeIdx) : structuredInstr (crI r y) = false := by
  cases r <;> rfl

theorem GA.crI_crT {cur : ModuleInst} (r : Bool) (y : TypeIdx) (d : DefType) :
    GA ok mi cur (.plain (crI r y)) (crT r d) := by
  cases r
  · exact .ann trivial trivial
  · exact .retAnn trivial trivial

/-! ## Stores -/

variable (ok mi) in
/-- Related function code, at the instance of the function. -/
def FC (cur : ModuleInst) : FuncCode H → FuncCode H → Prop
  | .wasm f, .wasm g => f.type = g.type ∧ f.locals = g.locals ∧ GIL ok mi cur f.body g.body
  | .host h, .host h' => h = h'
  | _, _ => False

variable (ok mi) in
/-- Related function instances: same type and instance, related code. -/
def FR (fi gi : FuncInst H) : Prop :=
  fi.type = gi.type ∧ fi.module = gi.module ∧ FC ok mi fi.module fi.code gi.code

theorem FC.refl {cur : ModuleInst} : ∀ c : FuncCode H, FC ok mi cur c c
  | .wasm _ => ⟨rfl, rfl, GIL.refl _⟩
  | .host _ => rfl

theorem FR.refl (fi : FuncInst H) : FR ok mi fi fi := ⟨rfl, rfl, FC.refl _⟩

variable (ok mi) in
/-- The stores of the two runs: equal up to related functions. -/
structure SR (s t : Store H) : Prop where
  funcs : List.Forall₂ (FR ok mi) s.funcs t.funcs
  eq : t = withFuncs s t.funcs

theorem SR.get {s t : Store H} (h : SR ok mi s t) {a : Nat} {fi : FuncInst H}
    (hf : s.funcs[a]? = some fi) : ∃ gi, t.funcs[a]? = some gi ∧ FR ok mi fi gi := by
  have hl := h.funcs.length_eq
  have ha := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨t.funcs[a]'(by omega), by simp, ?_⟩
  have := List.forall₂_iff_get.mp h.funcs |>.2 a ha (by omega)
  simpa [(List.getElem?_eq_some_iff.mp hf).2] using this

theorem SR.get' {s t : Store H} (h : SR ok mi s t) {a : Nat} {gi : FuncInst H}
    (hf : t.funcs[a]? = some gi) : ∃ fi, s.funcs[a]? = some fi ∧ FR ok mi fi gi := by
  have hl := h.funcs.length_eq
  have ha := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨s.funcs[a]'(by omega), by simp, ?_⟩
  have := List.forall₂_iff_get.mp h.funcs |>.2 a (by omega) ha
  simpa [(List.getElem?_eq_some_iff.mp hf).2] using this

theorem SR.sameTypes {s t : Store H} (h : SR ok mi s t) : SameTypes t.funcs s.funcs := by
  unfold SameTypes
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map]
  cases hj : s.funcs[j]? with
  | none =>
    have : t.funcs[j]? = none := by
      rw [List.getElem?_eq_none_iff] at hj ⊢; rw [← h.funcs.length_eq]; exact hj
    rw [this]
  | some fi =>
    obtain ⟨gi, hg, hr⟩ := h.get hj
    rw [hg]; simp [hr.1]

theorem SR.mono {s t s' : Store H} (h : SR ok mi s t) (hs : s'.funcs = s.funcs) :
    SR ok mi s' (withFuncs s' t.funcs) :=
  ⟨by rw [hs]; exact h.funcs, rfl⟩

theorem SR.length {s t : Store H} (h : SR ok mi s t) : t.funcs.length = s.funcs.length :=
  h.funcs.length_eq.symm

variable (ok mi) in
/-- Related configurations: equal frames, code related at the frame's instance. -/
def MR (c d : Config H) : Prop :=
  c.frame = d.frame ∧ GL ok mi c.frame.module c.code d.code

/-! ## The invariant -/

variable (ok mi) in
/-- **The store invariant**: the slot of every site holds the address of its callee, which
has the type of the call. -/
def DInv (s : Store H) : Prop :=
  ∀ t k y fx, ok t k y fx → ∃ a ta ti, mi.funcs[fx.toNat]? = some a ∧
    mi.tables[t.toNat]? = some ta ∧ s.tables[ta]? = some ti ∧ ti.refs[k.toNat]? = some (.func a) ∧
    RefOk s (.func a) (mi.instRef ⟨true, .typeIdx y⟩) ∧ a < s.funcs.length

/-- The invariant survives Core store extension that keeps the slot tables. -/
theorem DInv.extend {s s' : Store H} (h : DInv ok mi s) (he : Extend s s')
    (ht : ∀ t k y fx, ok t k y fx → ∀ ta, mi.tables[t.toNat]? = some ta →
      s'.tables[ta]? = s.tables[ta]?) : DInv ok mi s' := by
  intro t k y fx hok
  obtain ⟨a, ta, ti, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h t k y fx hok
  exact ⟨a, ta, ti, h₁, h₂, by rw [ht t k y fx hok ta h₂]; exact h₃, h₄, h₅.extend he,
    by have := he.funcs.1; omega⟩

theorem DInv.of_tables {s s' : Store H} (h : DInv ok mi s) (ht : s'.tables = s.tables)
    (hf : s'.funcs.map FuncInst.type = s.funcs.map FuncInst.type)
    (hr : ∀ a rt, RefOk s (.func a) rt → RefOk s' (.func a) rt) : DInv ok mi s' := by
  intro t k y fx hok
  obtain ⟨a, ta, ti, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h t k y fx hok
  have hl := congrArg List.length hf
  simp only [List.length_map] at hl
  exact ⟨a, ta, ti, h₁, h₂, by rw [ht]; exact h₃, h₄, hr _ _ h₅, by omega⟩

end Silmaril.Wasm.Binaryen.DirSim
