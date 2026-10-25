module

public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

@[expose] public section

/-! # Simulation under function and global address maps: the relations

RemoveUnusedModuleElements (`Pass/RUME.lean`) removes functions and globals and
renumbers the rest. Instances of the source and target modules then live at
different store addresses. This file defines the relation between two
configurations (side `A` and side `B`) used to prove that they execute in
lockstep (`RUMESim/Main.lean`).

* Addresses below `n0` (functions) and `g0` (globals) are *foreign*: they
  belong to the store the module was instantiated in. Foreign code runs
  unchanged on both sides. Every reference in the store and in foreign code
  names a foreign function (`refF`, `StoreF`), so foreign code never sees an
  address of the module.
* The module's own code runs in frames of the module instances `MA`/`MB`
  (mode `ours`); its instructions are related by the index relations `KF`/`KG`
  (`IRel`), and the addresses they resolve to by `F`/`G`.
* A direct call produces `REF.FUNC_ADDR a; CALL_REF`; the two addresses are
  related by `F` (`CodeR.pair`).
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## Foreign values -/

/-- A reference that names no function address at or above `n0`. -/
def refF (n0 : Nat) : Ref → Prop
  | .func a => a < n0
  | .extern r => refF n0 r
  | _ => True

/-- A value that names no function address at or above `n0`. -/
def valF (n0 : Nat) : Val → Prop
  | .ref r => refF n0 r
  | _ => True

/-- A field value that names no function address at or above `n0`. -/
def fvF (n0 : Nat) : FieldVal → Prop
  | .val v => valF n0 v
  | .pack _ _ => True

/-- Locals that name no function address at or above `n0`. -/
def localsF (n0 : Nat) (ls : List (Option Val)) : Prop :=
  ∀ o ∈ ls, ∀ v, o = some v → valF n0 v

/-- A foreign module instance: its functions and globals are foreign. -/
def modF (n0 g0 : Nat) (mi : ModuleInst) : Prop :=
  (∀ a ∈ mi.funcs, a < n0) ∧ (∀ a ∈ mi.globals, a < g0)

@[simp] theorem valF_ref (n0 : Nat) (r : Ref) : valF n0 (.ref r) = refF n0 r := rfl
@[simp] theorem valF_num (n0 : Nat) (v : NumVal) : valF n0 (.num v) = True := rfl
@[simp] theorem valF_vec (n0 : Nat) (b : BitVec 128) : valF n0 (.vec b) = True := rfl
@[simp] theorem valF_i32_eq (n0 : Nat) (b : BitVec 32) : valF n0 (Val.i32 b) = True := rfl
@[simp] theorem refF_func (n0 a : Nat) : refF n0 (.func a) = (a < n0) := rfl
@[simp] theorem refF_extern (n0 : Nat) (r : Ref) : refF n0 (.extern r) = refF n0 r := rfl
@[simp] theorem refF_null (n0 : Nat) : refF n0 .null = True := rfl
@[simp] theorem refF_i31 (n0 : Nat) (b : BitVec 31) : refF n0 (.i31 b) = True := rfl
@[simp] theorem refF_struct (n0 a : Nat) : refF n0 (.struct a) = True := rfl
@[simp] theorem refF_array (n0 a : Nat) : refF n0 (.array a) = True := rfl
@[simp] theorem refF_exn (n0 a : Nat) : refF n0 (.exn a) = True := rfl
@[simp] theorem refF_host (n0 a : Nat) : refF n0 (.host a) = True := rfl
@[simp] theorem fvF_val (n0 : Nat) (v : Val) : fvF n0 (.val v) = valF n0 v := rfl
@[simp] theorem fvF_pack (n0 : Nat) (p : PackType) (b : BitVec p.width) :
    fvF n0 (.pack p b) = True := rfl

theorem valF_i32 (n0 : Nat) (b : BitVec 32) : valF n0 (Val.i32 b) := trivial

/-- The store's references are foreign, and so are the module instances of its
foreign Wasm functions. -/
structure StoreF (n0 g0 : Nat) (S : Store H) : Prop where
  tables : ∀ ti ∈ S.tables, ∀ r ∈ ti.refs, refF n0 r
  elems : ∀ ei ∈ S.elems, ∀ r ∈ ei.refs, refF n0 r
  structs : ∀ si ∈ S.structs, ∀ fv ∈ si.fields, fvF n0 fv
  arrays : ∀ ai ∈ S.arrays, ∀ fv ∈ ai.fields, fvF n0 fv
  exns : ∀ e ∈ S.exns, ∀ v ∈ e.fields, valF n0 v
  globals : ∀ g ∈ S.globals, valF n0 g.value
  funcs : ∀ a < n0, ∀ fi, S.funcs[a]? = some fi → ∀ c, fi.code = .wasm c → modF n0 g0 fi.module

/-! ## The simulation context -/

/-- The parameters of the simulation. -/
structure SimCtx where
  /-- Foreign function addresses are those below `n0`. -/
  n0 : Nat
  /-- Foreign global addresses are those below `g0`. -/
  g0 : Nat
  /-- Related function addresses. -/
  F : Nat → Nat → Prop
  /-- Related global addresses. -/
  G : Nat → Nat → Prop
  /-- Related function indices. -/
  KF : Nat → Nat → Prop
  /-- Related global indices. -/
  KG : Nat → Nat → Prop
  /-- The module instance on side `A`. -/
  MA : ModuleInst
  /-- The module instance on side `B`. -/
  MB : ModuleInst

/-- Well-formedness of the parameters. -/
structure SimCtx.WF (X : SimCtx) : Prop where
  types : X.MA.types = X.MB.types
  mems : X.MA.mems = X.MB.mems
  datas : X.MA.datas = X.MB.datas
  kf : ∀ x y a, X.KF x y → X.MA.funcs[x]? = some a → ∃ b, X.MB.funcs[y]? = some b ∧ X.F a b
  kg : ∀ x y a, X.KG x y → X.MA.globals[x]? = some a → ∃ b, X.MB.globals[y]? = some b ∧ X.G a b
  gfun : ∀ a b b', X.G a b → X.G a b' → b = b'
  ginj : ∀ a a' b, X.G a b → X.G a' b → a = a'

/-! ## Instructions of the module -/

/-- Instructions the module's code may contain unchanged: the profile's flat
instructions other than calls and global accesses, every constant (values), and
the `throw_ref`/`call_ref` that exceptions and returning tail calls leave behind.
Memory instructions retain their indices; bulk-memory reductions may emit them
even when the executable profile accepts scalar loads/stores/size/grow. -/
def simpleI : Instr → Bool
  | .nop | .unreachable | .drop | .select none | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .localSet _ | .localTee _ | .intConst _ _ | .floatConst _ _ | .vecConst _
  | .intLoad .. | .intStore .. | .floatLoad .. | .floatStore ..
  | .vecLoad .. | .vecStore .. | .vecLoadLane .. | .vecStoreLane ..
  | .vecExtractLane .. | .vecSplat _ | .vecIntBinOp .. | .vecShiftOp .. | .vecExtBinOp .. | .vecShuffle _
  | .memorySize _ | .memoryGrow _ | .memoryFill _ | .memoryCopy .. | .memoryInit .. | .dataDrop _
  | .intUnOp _ _ | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _
  | .floatUnOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ | .convert _ | .throwRef | .callRef _
    => true
  | _ => false

mutual
/-- Related instructions of the module's code. -/
inductive IRel (X : SimCtx) : Instr → Instr → Prop where
  | call {x y : FuncIdx} (h : X.KF x.toNat y.toNat) : IRel X (.call x) (.call y)
  | globalGet {x y : GlobalIdx} (h : X.KG x.toNat y.toNat) :
      IRel X (.globalGet x) (.globalGet y)
  | globalSet {x y : GlobalIdx} (h : X.KG x.toNat y.toNat) :
      IRel X (.globalSet x) (.globalSet y)
  | block {bt : BlockType} {b b' : List Instr} (h : IRels X b b') :
      IRel X (.block bt b) (.block bt b')
  | loop {bt : BlockType} {b b' : List Instr} (h : IRels X b b') :
      IRel X (.loop bt b) (.loop bt b')
  | if_ {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : IRels X b₁ b₁')
      (h₂ : IRels X b₂ b₂') : IRel X (.if_ bt b₁ b₂) (.if_ bt b₁' b₂')
  | simple {i : Instr} (h : simpleI i = true) : IRel X i i
/-- Pointwise `IRel`. -/
inductive IRels (X : SimCtx) : List Instr → List Instr → Prop where
  | nil : IRels X [] []
  | cons {i j : Instr} {is js : List Instr} (h : IRel X i j) (t : IRels X is js) :
      IRels X (i :: is) (j :: js)
end

/-! ## Code -/

/-- Foreign code (`same`: unchanged) or the module's code (`ours`). -/
inductive Mode where
  | same
  | ours
  deriving DecidableEq

/-- A foreign frame. -/
abbrev FrameS (X : SimCtx) (f : Frame) : Prop := modF X.n0 X.g0 f.module ∧ localsF X.n0 f.locals

/-- Related frames of the module. -/
abbrev FrameO (X : SimCtx) (f f' : Frame) : Prop :=
  f.module = X.MA ∧ f'.module = X.MB ∧ f.locals = f'.locals ∧ localsF X.n0 f.locals

/-- Related frames in a mode. -/
abbrev FrameRel (X : SimCtx) : Mode → Frame → Frame → Prop
  | .same, f, f' => f = f' ∧ FrameS X f
  | .ours, f, f' => FrameO X f f'

mutual
/-- Related administrative instructions. -/
inductive ARel (X : SimCtx) : Mode → Admin → Admin → Prop where
  | plainS {i : Instr} : ARel X .same (.plain i) (.plain i)
  | plainO {i j : Instr} (h : IRel X i j) : ARel X .ours (.plain i) (.plain j)
  | ref {m : Mode} {r : Ref} (h : refF X.n0 r) : ARel X m (.ref r) (.ref r)
  | callRefType {m : Mode} {d : DefType} : ARel X m (.callRefType d) (.callRefType d)
  | returnCallRefType {d : DefType} : ARel X .same (.returnCallRefType d) (.returnCallRefType d)
  | trap {m : Mode} : ARel X m .trap .trap
  | labelS {n : Nat} {cont : List Instr} {b b' : List Admin} (h : CodeR X .same b b') :
      ARel X .same (.label n cont b) (.label n cont b')
  | labelO {n : Nat} {cont cont' : List Instr} {b b' : List Admin} (hc : IRels X cont cont')
      (h : CodeR X .ours b b') : ARel X .ours (.label n cont b) (.label n cont' b')
  | handler {n : Nat} {cs : List Catch} {b b' : List Admin} (h : CodeR X .same b b') :
      ARel X .same (.handler n cs b) (.handler n cs b')
  | frameS {m : Mode} {n : Nat} {fr : Frame} {b b' : List Admin} (hf : FrameS X fr)
      (h : CodeR X .same b b') : ARel X m (.frame n fr b) (.frame n fr b')
  | frameO {m : Mode} {n : Nat} {fr fr' : Frame} {b b' : List Admin} (hf : FrameO X fr fr')
      (h : CodeR X .ours b b') : ARel X m (.frame n fr b) (.frame n fr' b')
/-- Related instruction sequences: pointwise, except that a call target is
related by `F`. -/
inductive CodeR (X : SimCtx) : Mode → List Admin → List Admin → Prop where
  | nil {m : Mode} : CodeR X m [] []
  | cons {m : Mode} {x y : Admin} {xs ys : List Admin} (h : ARel X m x y)
      (t : CodeR X m xs ys) : CodeR X m (x :: xs) (y :: ys)
  | pair {m : Mode} {a b : Nat} {d : DefType} {xs ys : List Admin} (h : X.F a b)
      (t : CodeR X m xs ys) :
      CodeR X m (.ref (.func a) :: .callRefType d :: xs) (.ref (.func b) :: .callRefType d :: ys)
end

/-! ## Stores -/

/-- Replace the functions and globals of a store. -/
def _root_.Silmaril.Wasm.Execution.Core.Store.withFG (S : Store H) (fs : List (FuncInst H)) (gs : List GlobalInst) : Store H :=
  { S with funcs := fs, globals := gs }

/-- Related function addresses: a foreign address on both sides, or functions of
the two module instances with related code. -/
def FuncPair (X : SimCtx) (S T : Store H) (a b : Nat) : Prop :=
  (a < X.n0 ∧ b = a) ∨
  (X.n0 ≤ a ∧ X.n0 ≤ b ∧ ∃ (fA fB : FuncInst H) (cA cB : Func), S.funcs[a]? = some fA ∧
    T.funcs[b]? = some fB ∧ fA.type = fB.type ∧ fA.module = X.MA ∧ fB.module = X.MB ∧
    fA.code = .wasm cA ∧ fB.code = .wasm cB ∧ cA.locals = cB.locals ∧ IRels X cA.body cB.body)

/-- A function type whose parameters are numeric. -/
def NumParams (d : DefType) : Prop :=
  ∀ ps rs, Expand d (.func ps rs) → ∀ p ∈ ps.toList, ∃ t, p = .num t

/-- The function at `a`, if any, takes numeric parameters. -/
def NumParamsAt (fs : List (FuncInst H)) (a : Nat) : Prop :=
  ∀ fi, fs[a]? = some fi → NumParams fi.type

/-- Related stores. -/
structure StoreRel (X : SimCtx) (S T : Store H) : Prop where
  rest : S.withFG [] [] = T.withFG [] []
  funcs : ∀ a < X.n0, S.funcs[a]? = T.funcs[a]?
  globals : ∀ a < X.g0, S.globals[a]? = T.globals[a]?
  fpair : ∀ a b, X.F a b → FuncPair X S T a b
  gpair : ∀ a b, X.G a b → X.g0 ≤ a ∧ X.g0 ≤ b ∧ ∃ g, S.globals[a]? = some g ∧ T.globals[b]? = some g
  fgn : StoreF X.n0 X.g0 S
  intp : ∀ a b, X.F a b → NumParamsAt S.funcs a

/-- Related configurations. -/
abbrev ConfRel (X : SimCtx) (m : Mode) (c c' : Config H) : Prop :=
  StoreRel X c.store c'.store ∧ FrameRel X m c.frame c'.frame ∧ CodeR X m c.code c'.code

/-! ## Basic facts -/

theorem Store.withFG_eq {S T : Store H} (h : S.withFG [] [] = T.withFG [] []) :
    T = S.withFG T.funcs T.globals := by
  cases S; cases T
  simp only [Store.withFG, Store.mk.injEq] at h ⊢
  simp_all

@[simp] theorem Store.withFG_funcs (S : Store H) (fs gs) : (S.withFG fs gs).funcs = fs := rfl
@[simp] theorem Store.withFG_globals (S : Store H) (fs gs) : (S.withFG fs gs).globals = gs := rfl
@[simp] theorem Store.withFG_tables (S : Store H) (fs gs) : (S.withFG fs gs).tables = S.tables := rfl
@[simp] theorem Store.withFG_elems (S : Store H) (fs gs) : (S.withFG fs gs).elems = S.elems := rfl
@[simp] theorem Store.withFG_structs (S : Store H) (fs gs) :
    (S.withFG fs gs).structs = S.structs := rfl
@[simp] theorem Store.withFG_arrays (S : Store H) (fs gs) : (S.withFG fs gs).arrays = S.arrays := rfl
@[simp] theorem Store.withFG_exns (S : Store H) (fs gs) : (S.withFG fs gs).exns = S.exns := rfl
@[simp] theorem Store.withFG_tags (S : Store H) (fs gs) : (S.withFG fs gs).tags = S.tags := rfl
@[simp] theorem Store.withFG_mems (S : Store H) (fs gs) : (S.withFG fs gs).mems = S.mems := rfl
@[simp] theorem Store.withFG_datas (S : Store H) (fs gs) : (S.withFG fs gs).datas = S.datas := rfl

theorem toAdmin_ne_callRefType (v : Val) (d : DefType) : v.toAdmin ≠ .callRefType d := by
  cases v with
  | num n =>
    obtain ⟨tp, b⟩ := n
    cases tp <;> simp [Val.toAdmin]
  | vec b => simp [Val.toAdmin]
  | ref r => simp [Val.toAdmin]

theorem toAdmin_eq_ref {v : Val} {r : Ref} (h : v.toAdmin = .ref r) : v = .ref r := by
  cases v with
  | num n =>
    obtain ⟨tp, b⟩ := n
    cases tp <;> simp [Val.toAdmin] at h
  | vec b => simp [Val.toAdmin] at h
  | ref r' =>
    simp only [Val.toAdmin, Admin.ref.injEq] at h
    subst h; rfl

theorem vals_cons_eq (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs := rfl

theorem simpleI_intConst (t : IntType) (b : BitVec t.width) : simpleI (.intConst t b) = true := rfl

/-- A related value is the same foreign value. -/
theorem ARel.val_inv {X : SimCtx} {m : Mode} {v : Val} {y : Admin} (h : ARel X m v.toAdmin y) :
    y = v.toAdmin ∧ valF X.n0 v := by
  cases v with
  | num n =>
    obtain ⟨tp, b⟩ := n
    cases tp with
    | int t =>
      change ARel X m (.plain (.intConst t b)) y at h
      cases h with
      | plainS => exact ⟨rfl, trivial⟩
      | plainO h' => cases h'; exact ⟨rfl, trivial⟩
    | float t =>
      change ARel X m (.plain (.floatConst t b)) y at h
      cases h with
      | plainS => exact ⟨rfl, trivial⟩
      | plainO h' => cases h'; exact ⟨rfl, trivial⟩
  | vec b =>
    change ARel X m (.plain (.vecConst b)) y at h
    cases h with
    | plainS => exact ⟨rfl, trivial⟩
    | plainO h' => cases h'; exact ⟨rfl, trivial⟩
  | ref r =>
    change ARel X m (.ref r) y at h
    cases h with
    | ref h' => exact ⟨rfl, h'⟩

/-- A foreign value is related to itself. -/
theorem ARel.val {X : SimCtx} {m : Mode} {v : Val} (h : valF X.n0 v) :
    ARel X m v.toAdmin v.toAdmin := by
  cases v with
  | num n =>
    obtain ⟨tp, b⟩ := n
    cases tp with
    | int t =>
      change ARel X m (.plain (.intConst t b)) (.plain (.intConst t b))
      cases m
      · exact .plainS
      · exact .plainO (.simple rfl)
    | float t =>
      change ARel X m (.plain (.floatConst t b)) (.plain (.floatConst t b))
      cases m
      · exact .plainS
      · exact .plainO (.simple rfl)
  | vec b =>
    change ARel X m (.plain (.vecConst b)) (.plain (.vecConst b))
    cases m
    · exact .plainS
    · exact .plainO (.simple rfl)
  | ref r => exact .ref h

theorem CodeR.ofVals {X : SimCtx} : ∀ {m : Mode} {vs : List Val}, (∀ v ∈ vs, valF X.n0 v) →
    CodeR X m (Execution.Core.vals vs) (Execution.Core.vals vs)
  | _, [], _ => .nil
  | _, v :: vs, h => .cons (ARel.val (h v (by simp))) (CodeR.ofVals fun w hw => h w (by simp [hw]))

theorem CodeR.append {X : SimCtx} : ∀ {m : Mode} {xs ys xs' ys' : List Admin}, CodeR X m xs ys →
    CodeR X m xs' ys' → CodeR X m (xs ++ xs') (ys ++ ys')
  | _, _, _, _, _, .nil, h' => h'
  | _, _, _, _, _, .cons ha t, h' => .cons ha (CodeR.append t h')
  | _, _, _, _, _, .pair hF t, h' => .pair hF (CodeR.append t h')

theorem CodeR.length {X : SimCtx} : ∀ {m : Mode} {xs ys : List Admin}, CodeR X m xs ys →
    xs.length = ys.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ t => by simp [CodeR.length t]
  | _, _, _, .pair _ t => by simp [CodeR.length t]

/-- Splitting a related sequence at its first non-value. -/
theorem CodeR.split_fnv {X : SimCtx} : ∀ {m : Mode} {e : Admin} {rest : List Admin}
    {V : List Val} {ys : List Admin}, e.val? = none →
    CodeR X m (Execution.Core.vals V ++ e :: rest) ys →
    (∃ e' rest', ys = Execution.Core.vals V ++ e' :: rest' ∧ (∀ v ∈ V, valF X.n0 v) ∧
      ARel X m e e' ∧ CodeR X m rest rest') ∨
    (∃ (V₀ : List Val) (a b : Nat) (d : DefType) (rest' : List Admin),
      V = V₀ ++ [.ref (.func a)] ∧ e = .callRefType d ∧
      ys = Execution.Core.vals V₀ ++ .ref (.func b) :: .callRefType d :: rest' ∧
      (∀ v ∈ V₀, valF X.n0 v) ∧ X.F a b ∧ CodeR X m rest rest')
  | m, e, rest, [], ys, he, h => by
    change CodeR X m (e :: rest) ys at h
    generalize hc : e :: rest = c at h
    cases h with
    | nil => cases hc
    | cons ha t =>
      injection hc with h1 h2
      subst h1 h2
      exact .inl ⟨_, _, rfl, by simp, ha, t⟩
    | pair hF t =>
      injection hc with h1 h2
      subst h1
      simp [Admin.val?] at he
  | m, e, rest, v :: V, ys, he, h => by
    rw [vals_cons_eq, List.cons_append] at h
    generalize hc : v.toAdmin :: (Execution.Core.vals V ++ e :: rest) = c at h
    cases h with
    | nil => cases hc
    | @cons _ x y xs ys' ha t =>
      injection hc with h1 h2
      subst h1 h2
      obtain ⟨rfl, hv⟩ := ARel.val_inv ha
      rcases CodeR.split_fnv he t with ⟨e', rest', rfl, hV, hee, hr⟩ |
          ⟨V₀, a, b, d, rest', rfl, rfl, rfl, hV, hF, hr⟩
      · refine .inl ⟨e', rest', rfl, ?_, hee, hr⟩
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hv
        · exact hV w hw
      · refine .inr ⟨v :: V₀, a, b, d, rest', rfl, rfl, rfl, ?_, hF, hr⟩
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hv
        · exact hV w hw
    | @pair _ a b d xs ys' hF t =>
      injection hc with h1 h2
      have hv := toAdmin_eq_ref h1
      subst hv
      cases V with
      | nil =>
        change e :: rest = Admin.callRefType d :: xs at h2
        injection h2 with h3 h4
        subst h3 h4
        exact .inr ⟨[], a, b, d, ys', rfl, rfl, rfl, by simp, hF, t⟩
      | cons w W =>
        rw [vals_cons_eq, List.cons_append] at h2
        injection h2 with h3 h4
        exact absurd h3 (toAdmin_ne_callRefType w d)

/-- Splitting a related sequence anywhere: the right part stays related (a call
target cut off from its `CALL_REF` leaves a bare `CALL_REF`, which is related to
itself). -/
theorem CodeR.split_app {X : SimCtx} : ∀ {m : Mode} {r u ys : List Admin},
    CodeR X m (u ++ r) ys → ∃ u' r', ys = u' ++ r' ∧ u'.length = u.length ∧ CodeR X m r r'
  | _, _, [], ys, h => ⟨[], ys, rfl, rfl, h⟩
  | m, r, x :: u, ys, h => by
    rw [List.cons_append] at h
    generalize hc : x :: (u ++ r) = c at h
    cases h with
    | nil => cases hc
    | @cons _ x' y xs ys' ha t =>
      injection hc with h1 h2
      subst h2
      obtain ⟨u', r', rfl, hl, hr⟩ := CodeR.split_app t
      exact ⟨y :: u', r', rfl, by simp [hl], hr⟩
    | @pair _ a b d xs ys' hF t =>
      injection hc with h1 h2
      cases u with
      | nil =>
        rw [List.nil_append] at h2
        subst h2
        exact ⟨[.ref (.func b)], .callRefType d :: ys', rfl, rfl, .cons .callRefType t⟩
      | cons z u =>
        rw [List.cons_append] at h2
        injection h2 with h3 h4
        subst h4
        obtain ⟨u', r', rfl, hl, hr⟩ := CodeR.split_app t
        exact ⟨.ref (.func b) :: .callRefType d :: u', r', rfl, by simp [hl], hr⟩

/-- Related values are equal and foreign. -/
theorem CodeR.vals_inv {X : SimCtx} : ∀ {m : Mode} {V : List Val} {ys : List Admin},
    CodeR X m (Execution.Core.vals V) ys → ys = Execution.Core.vals V ∧ ∀ v ∈ V, valF X.n0 v
  | m, [], ys, h => by
    change CodeR X m [] ys at h
    cases h
    exact ⟨rfl, by simp⟩
  | m, v :: V, ys, h => by
    rw [vals_cons_eq] at h
    generalize hc : v.toAdmin :: Execution.Core.vals V = c at h
    cases h with
    | nil => cases hc
    | @cons _ x y xs ys' ha t =>
      injection hc with h1 h2
      subst h1 h2
      obtain ⟨rfl, hv⟩ := ARel.val_inv ha
      obtain ⟨rfl, hV⟩ := CodeR.vals_inv t
      refine ⟨rfl, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hv
      · exact hV w hw
    | @pair _ a b d xs ys' hF t =>
      injection hc with h1 h2
      cases V with
      | nil => exact absurd h2 (by simp [Execution.Core.vals])
      | cons w W =>
        rw [vals_cons_eq] at h2
        injection h2 with h3 h4
        exact absurd h3 (toAdmin_ne_callRefType w d)

/-- Related module code lowers to related administrative code. -/
theorem IRels.expression {X : SimCtx} : ∀ {is js : List Instr}, IRels X is js →
    CodeR X .ours (expression is) (expression js)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (.plainO h) (IRels.expression t)

theorem IRels.append {X : SimCtx} : ∀ {is js is' js' : List Instr}, IRels X is js →
    IRels X is' js' → IRels X (is ++ is') (js ++ js')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (IRels.append t h')

theorem CodeR.expression_same {X : SimCtx} : ∀ (is : List Instr),
    CodeR X .same (expression is) (expression is)
  | [] => .nil
  | _ :: is => .cons .plainS (CodeR.expression_same is)

/-- The instruction relation of a mode on continuations. -/
def ContRel (X : SimCtx) : Mode → List Instr → List Instr → Prop
  | .same, c, c' => c = c'
  | .ours, c, c' => IRels X c c'

theorem ContRel.expression {X : SimCtx} {m : Mode} {c c' : List Instr} (h : ContRel X m c c') :
    CodeR X m (expression c) (expression c') := by
  cases m
  · cases h; exact CodeR.expression_same c
  · exact IRels.expression h

/-- Inversion of a related label. -/
theorem ARel.label_inv {X : SimCtx} {m : Mode} {n : Nat} {cont : List Instr} {b : List Admin}
    {y : Admin} (h : ARel X m (.label n cont b) y) :
    ∃ cont' b', y = .label n cont' b' ∧ ContRel X m cont cont' ∧ CodeR X m b b' := by
  cases h with
  | labelS h => exact ⟨_, _, rfl, rfl, h⟩
  | labelO hc h => exact ⟨_, _, rfl, hc, h⟩

/-- Inversion of a related frame. -/
theorem ARel.frame_inv {X : SimCtx} {m : Mode} {n : Nat} {fr : Frame} {b : List Admin}
    {y : Admin} (h : ARel X m (.frame n fr b) y) :
    ∃ m' fr' b', y = .frame n fr' b' ∧ FrameRel X m' fr fr' ∧ CodeR X m' b b' := by
  cases h with
  | frameS hf h => exact ⟨.same, _, _, rfl, ⟨rfl, hf⟩, h⟩
  | frameO hf h => exact ⟨.ours, _, _, rfl, hf, h⟩

/-- Inversion of a related handler. -/
theorem ARel.handler_inv {X : SimCtx} {m : Mode} {n : Nat} {cs : List Catch} {b : List Admin}
    {y : Admin} (h : ARel X m (.handler n cs b) y) :
    m = .same ∧ ∃ b', y = .handler n cs b' ∧ CodeR X .same b b' := by
  cases h with
  | handler h => exact ⟨rfl, _, rfl, h⟩

theorem ARel.trap_inv {X : SimCtx} {m : Mode} {y : Admin} (h : ARel X m .trap y) : y = .trap := by
  cases h; rfl

theorem ARel.callRefType_inv {X : SimCtx} {m : Mode} {d : DefType} {y : Admin}
    (h : ARel X m (.callRefType d) y) : y = .callRefType d := by
  cases h; rfl

theorem ARel.returnCallRefType_inv {X : SimCtx} {m : Mode} {d : DefType} {y : Admin}
    (h : ARel X m (.returnCallRefType d) y) : m = .same ∧ y = .returnCallRefType d := by
  cases h; exact ⟨rfl, rfl⟩

theorem ARel.ref_inv {X : SimCtx} {m : Mode} {r : Ref} {y : Admin}
    (h : ARel X m (.ref r) y) : y = .ref r ∧ refF X.n0 r := by
  cases h with
  | ref h => exact ⟨rfl, h⟩

end Silmaril.Wasm.Binaryen.RUMESim
