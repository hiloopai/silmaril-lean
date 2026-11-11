module

public import Silmaril.Wasm.SSA.Translate.Defs

/-!
# Invariants of the translation into SSA

A context `c` agrees with an environment and the fragment's locals
(`Agree`) when the variable at the level of each local holds that local's
value. `Ext` says a later context/environment pair extends an earlier one:
same labels, at least as many variables and labels, and the old levels keep
their values. Labels are named by level; `TgtL` is where an abrupt outcome
leaves (label level and value). This file also evaluates the generated
terms (`pack`, `argTm`, `resTm`), `unpack` and `initZeros`, and proves that
fragment runs preserve the number of locals.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-- Term evaluation in the dialect. -/
abbrev TEval (env : Env WVal) (t : Tm Prim) (v : SVal) : Prop :=
  Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval instr env t () v ()

/-- Region evaluation in the dialect. -/
abbrev REval (env : Env WVal) (r : Region Prim) (l : Nat) (v : SVal) : Prop :=
  Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval instr env r () l v ()

/-- The variable at level `lv` holds `v`. -/
def VarOK (c : Ctx) (env : Env WVal) (lv : Nat) (v : WVal) : Prop :=
  lv < c.depth ∧ env (c.depth - 1 - lv) = .atom v

/-- The locals' levels hold the locals. -/
def Agree (c : Ctx) (env : Env WVal) (ls : List WVal) : Prop :=
  List.Forall₂ (VarOK c env) c.locals ls

/-- A result level holds a result. -/
def ResOK (c : Ctx) (env : Env WVal) : Option Nat → Option WVal → Prop
  | none, none => True
  | some l, some v => VarOK c env l v
  | _, _ => False

/-- A carried value. -/
def resV : Option WVal → SVal
  | none => .unit
  | some v => .atom v

/-- A tuple of atoms with a tail. -/
def tupleV (ls : List WVal) (tail : SVal) : SVal := ls.foldr (fun a t => .pair (.atom a) t) tail

/-- A block argument. -/
def packV (ls : List WVal) (r : Option WVal) : SVal := tupleV ls (resV r)

/-- `(c', env')` extends `(c, env)`. -/
structure Ext (c : Ctx) (env : Env WVal) (c' : Ctx) (env' : Env WVal) : Prop where
  labels : c'.labels = c.labels
  ret : c'.ret = c.ret
  trap : c'.trap = c.trap
  fty : c'.fty = c.fty
  ldepth : c.ldepth ≤ c'.ldepth
  len : c'.locals.length = c.locals.length
  depth : c.depth ≤ c'.depth
  env : ∀ lv, lv < c.depth → env' (c'.depth - 1 - lv) = env (c.depth - 1 - lv)

/-- Label levels are in scope. -/
def WF (c : Ctx) : Prop :=
  (∀ m, LabelK.join m ∈ c.labels → m < c.ldepth) ∧ c.ret < c.ldepth ∧ c.trap < c.ldepth

/-- Where an abrupt outcome leaves: a label level and the value passed. -/
def TgtL (c : Ctx) {α : Type} : Out α → Option (Nat × SVal)
  | .brk l ls r =>
      match c.labels[l]? with
      | some (.join m) => some (m, packV ls r)
      | some .ret => some (c.ret, resV (if c.fty.isSome then r else none))
      | none => none
  | .ret r => some (c.ret, resV (if c.fty.isSome then r else none))
  | .trap => some (c.trap, .unit)
  | .ok .. => none

/-! ## Contexts -/

theorem Ext.refl (c : Ctx) (env : Env WVal) : Ext c env c env :=
  ⟨rfl, rfl, rfl, rfl, le_refl _, rfl, le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {c₁ c₂ c₃ : Ctx} {e₁ e₂ e₃ : Env WVal} (h₁ : Ext c₁ e₁ c₂ e₂)
    (h₂ : Ext c₂ e₂ c₃ e₃) : Ext c₁ e₁ c₃ e₃ where
  labels := h₂.labels.trans h₁.labels
  ret := h₂.ret.trans h₁.ret
  trap := h₂.trap.trans h₁.trap
  fty := h₂.fty.trans h₁.fty
  ldepth := h₁.ldepth.trans h₂.ldepth
  len := h₂.len.trans h₁.len
  depth := h₁.depth.trans h₂.depth
  env lv hlv := (h₂.env lv (by have := h₁.depth; omega)).trans (h₁.env lv hlv)

theorem VarOK.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env') {lv : Nat}
    {v : WVal} (hv : VarOK c env lv v) : VarOK c' env' lv v :=
  ⟨by have := h.depth; have := hv.1; omega, (h.env lv hv.1).trans hv.2⟩

theorem ResOK.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env') :
    ∀ {rl : Option Nat} {r : Option WVal}, ResOK c env rl r → ResOK c' env' rl r
  | none, none, _ => trivial
  | some _, some _, hv => VarOK.ext h hv
  | none, some _, hv => hv.elim
  | some _, none, hv => hv.elim

theorem Ext.bind (c : Ctx) (env : Env WVal) (x : SVal) : Ext c env c.bind (extend env x) where
  labels := rfl
  ret := rfl
  trap := rfl
  fty := rfl
  ldepth := le_refl _
  len := rfl
  depth := Nat.le_succ _
  env lv hlv := by
    show extend env x (c.depth + 1 - 1 - lv) = env (c.depth - 1 - lv)
    have : c.depth + 1 - 1 - lv = (c.depth - 1 - lv) + 1 := by omega
    rw [this]; rfl

theorem Ext.enter (c : Ctx) (env : Env WVal) : Ext c env c.enter env :=
  ⟨rfl, rfl, rfl, rfl, Nat.le_succ _, rfl, le_refl _, fun _ _ => rfl⟩

theorem Ext.setLocals {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env') (ls : List Nat)
    (hl : ls.length = c'.locals.length) : Ext c env { c' with locals := ls } env' :=
  { h with len := hl.trans h.len }

theorem varOK_new (c : Ctx) (env : Env WVal) (v : WVal) :
    VarOK c.bind (extend env (.atom v)) c.depth v := by
  refine ⟨Nat.lt_succ_self _, ?_⟩
  show extend env (.atom v) (c.depth + 1 - 1 - c.depth) = .atom v
  rw [show c.depth + 1 - 1 - c.depth = 0 by omega]; rfl

theorem Agree.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env')
    (hl : c'.locals = c.locals) {ls : List WVal} (ha : Agree c env ls) : Agree c' env' ls := by
  unfold Agree; rw [hl]; exact ha.imp fun _ _ hv => VarOK.ext h hv

theorem Agree.bind {c : Ctx} {env : Env WVal} {ls : List WVal} (ha : Agree c env ls) (x : SVal) :
    Agree c.bind (extend env x) ls := Agree.ext (Ext.bind c env x) rfl ha

theorem Agree.length {c : Ctx} {env : Env WVal} {ls : List WVal} (ha : Agree c env ls) :
    c.locals.length = ls.length := ha.length_eq

theorem WF.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env') (hw : WF c) : WF c' := by
  refine ⟨fun m hm => ?_, ?_, ?_⟩
  · rw [h.labels] at hm; exact lt_of_lt_of_le (hw.1 m hm) h.ldepth
  · rw [h.ret]; exact lt_of_lt_of_le hw.2.1 h.ldepth
  · rw [h.trap]; exact lt_of_lt_of_le hw.2.2 h.ldepth

theorem forall₂_set {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ (i : Nat) {a b}, R a b →
      List.Forall₂ R (as.set i a) (bs.set i b)
  | [], [], .nil, _, _, _, _ => .nil
  | _ :: _, _ :: _, .cons _ t, 0, _, _, hab => .cons hab t
  | _ :: _, _ :: _, .cons h t, i + 1, _, _, hab => .cons h (forall₂_set t i hab)

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {i : Nat} {b}, bs[i]? = some b →
      ∃ a, as[i]? = some a ∧ R a b
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons hab _, 0, _, h => by
      simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _ :: _, _ :: _, .cons _ t, i + 1, _, h => by
      simp at h; exact forall₂_getElem? t (by simpa using h)

theorem resOK_head? {c : Ctx} {env : Env WVal} :
    ∀ {lvls : List Nat} {vs : List WVal}, List.Forall₂ (VarOK c env) lvls vs →
      ResOK c env lvls.head? vs.head?
  | [], [], .nil => trivial
  | _ :: _, _ :: _, .cons h _ => h

theorem forall₂_dropLast {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → List.Forall₂ R as.dropLast bs.dropLast
  | [], [], .nil => .nil
  | [_], [_], .cons _ .nil => .nil
  | _ :: _ :: _, _ :: _ :: _, .cons h t => by
      simp only [List.dropLast_cons_cons]; exact .cons h (forall₂_dropLast t)

theorem forall₂_getLast? {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {b}, bs.getLast? = some b →
      ∃ a, as.getLast? = some a ∧ R a b
  | [], [], .nil, _, h => by simp at h
  | [_], [_], .cons hab .nil, _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _ :: a₂ :: as, _ :: b₂ :: bs, .cons _ t, b, h => by
      rw [List.getLast?_cons_cons] at h ⊢
      exact forall₂_getLast? t h

/-! ## Terms -/

theorem eval_var {c : Ctx} {env : Env WVal} {lv : Nat} {v : WVal} (h : VarOK c env lv v) :
    TEval env (c.var lv) (.atom v) :=
  .var_of_eq h.2

theorem eval_resTm {c : Ctx} {env : Env WVal} :
    ∀ {rl : Option Nat} {r : Option WVal}, ResOK c env rl r → TEval env (c.resTm rl) (resV r)
  | none, none, _ => .unit
  | some _, some _, h => eval_var h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem eval_pack {c : Ctx} {env : Env WVal} {ls : List WVal} (ha : Agree c env ls)
    {rl : Option Nat} {r : Option WVal} (hr : ResOK c env rl r) :
    TEval env (c.pack rl) (packV ls r) := by
  unfold Ctx.pack packV tupleV
  unfold Agree at ha
  generalize c.locals = xs at ha ⊢
  induction ha with
  | nil => exact eval_resTm hr
  | cons h _ ih => exact .pair (eval_var h) ih

theorem eval_argTm {c : Ctx} {env : Env WVal} {lvls : List Nat} {vs : List WVal}
    (h : List.Forall₂ (VarOK c env) lvls vs) : TEval env (c.argTm lvls) (encodeList vs) := by
  unfold Ctx.argTm
  induction h with
  | nil => exact .unit
  | cons h _ ih => exact .pair (eval_var h) ih

@[simp] theorem decodeList_encodeList : ∀ vs : List WVal, decodeList (encodeList vs) = some vs
  | [] => rfl
  | a :: as => by simp [encodeList, decodeList, decodeList_encodeList as]

theorem TgtL_cast {c : Ctx} {α β : Type} {o : Out α} (h : o.Abrupt) :
    TgtL c (o.cast : Out β) = TgtL c o := by
  cases o <;> simp_all [Out.cast, Out.Abrupt, TgtL]

theorem WF.tgt {c : Ctx} (hw : WF c) {α : Type} {o : Out α} {m : Nat} {v : SVal}
    (h : TgtL c o = some (m, v)) : m < c.ldepth := by
  cases o with
  | ok => simp [TgtL] at h
  | brk l ls r =>
      simp only [TgtL] at h
      split at h
      · rename_i m' hm; simp at h; obtain ⟨rfl, -⟩ := h
        exact hw.1 _ (List.mem_of_getElem? hm)
      · simp at h; obtain ⟨rfl, -⟩ := h; exact hw.2.1
      · simp at h
  | ret => simp [TgtL] at h; obtain ⟨rfl, -⟩ := h; exact hw.2.1
  | trap => simp [TgtL] at h; obtain ⟨rfl, -⟩ := h; exact hw.2.2

/-! ## Unpacking and initialisation -/

theorem eval_unpack : ∀ (ls : List WVal) (c : Ctx) (t : Nat) (env : Env WVal) (tail : SVal)
    (K : Ctx → List Nat → Nat → Region Prim) (d l : Nat) (v : SVal),
    d = c.depth + 2 * ls.length → t < c.depth → env (c.depth - 1 - t) = tupleV ls tail →
    (∀ lvls tl env', List.Forall₂ (VarOK { c with depth := d } env') lvls ls → tl < d →
      env' (d - 1 - tl) = tail → (∀ lv, lv < c.depth → env' (d - 1 - lv) = env (c.depth - 1 - lv)) →
      REval env' (K { c with depth := d } lvls tl) l v) →
    REval env (unpack ls.length c t K) l v
  | [], c, t, env, tail, K, d, l, v, hd, ht, he, hK => by
      subst hd
      exact hK [] t env .nil (by simpa using ht) (by simpa [tupleV] using he) (fun _ _ => by simp)
  | a :: as, c, t, env, tail, K, d, l, v, hd, ht, he, hK => by
      simp only [List.length_cons, unpack]
      refine .let₂ (va := .atom a) (vb := tupleV as tail) (.var_of_eq he) ?_
      refine eval_unpack as { c with depth := c.depth + 2 } (c.depth + 1) _ tail _ d l v
        (by simp only [List.length_cons] at hd; simp only; omega) (by simp) (by simp [tupleV]) ?_
      intro lvls tl env' hl htl hte hpre
      refine hK (c.depth :: lvls) tl env' (.cons ⟨by show c.depth < d; rw [hd]; simp, ?_⟩ hl) htl hte ?_
      · have := hpre (c.depth) (by simp)
        simp only at this
        rw [this, show c.depth + 2 - 1 - c.depth = 1 by omega]; rfl
      · intro lv hlv
        have := hpre lv (by simp; omega)
        simp only at this
        rw [this, show c.depth + 2 - 1 - lv = (c.depth - 1 - lv) + 2 by omega]; rfl

theorem eval_initZeros : ∀ (ts : List IntType) (c : Ctx) (env : Env WVal) (ls : List WVal)
    (K : Ctx → Region Prim) (l : Nat) (v : SVal), Agree c env ls →
    (∀ c' env', c'.ldepth = c.ldepth → c'.labels = c.labels → c'.ret = c.ret →
      c'.trap = c.trap → c'.fty = c.fty → Agree c' env' (ls ++ ts.map WVal.zero) →
      REval env' (K c') l v) →
    REval env (initZeros ts c K) l v
  | [], c, env, ls, K, l, v, ha, hK => hK c env rfl rfl rfl rfl rfl (by simpa using ha)
  | t :: ts, c, env, ls, K, l, v, ha, hK => by
      simp only [initZeros]
      refine .let₁ (s₁ := ()) (va := .atom (WVal.zero t)) (.op (s₁ := ()) .unit ?_) ?_
      · show Prim.run _ _ = _; simp [Prim.run, decodeList, Op.eval]
      refine eval_initZeros ts _ _ (ls ++ [WVal.zero t]) K l v ?_ ?_
      · unfold Agree
        exact List.rel_append (ha.imp fun _ _ hv => VarOK.ext (Ext.bind c env _) hv)
          (.cons (varOK_new c env _) .nil)
      · intro c' env' h1 h2 h3 h4 h5 ha'
        exact hK c' env' h1 h2 h3 h4 h5 (by simpa using ha')

/-! ## Locals are preserved in number -/

/-- The locals of an outcome have the length of the starting locals. -/
def LenOK {α : Type} (ls : List WVal) : Out α → Prop
  | .ok ls' _ | .brk _ ls' _ => ls'.length = ls.length
  | _ => True

theorem LenOK.cast {α β : Type} {ls : List WVal} {o : Out α} (h : LenOK ls o) :
    LenOK ls (o.cast : Out β) := by
  cases o <;> simp_all [LenOK, Out.cast]

end Silmaril.Proofs.Wasm.SSA.Translate
