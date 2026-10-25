module

public import Silmaril.Wasm.Binaryen.Lower

@[expose] public section

/-! # Folding lift (the CHECKED stage of `binaryen-lean`)

Binaryen reads a binary with `IRBuilder` (`src/wasm/wasm-ir-builder.cpp`,
version_133), which rebuilds expression trees from stack code, so that tree
passes (Precompute, OptimizeInstructions) see `i32.add (local.get 0) (i32.const 0)`
rather than three siblings. `foldDeep` does the same: it lifts structured control
with `liftInstr`, then folds every body with `foldB`, recursively inside blocks,
loops and ifs.

`foldB` refines `Lower.fold` in two ways, so that the trees are
Binaryen-shaped:

* **Only single-value operands.** An instruction of operand arity `n` takes the
  top `n` finished trees only when each of them produces exactly one value
  (`resArity`), so a `local.set` or a `call` of a void function is never taken as
  an operand. `resArity` is defined only for *complete* trees (an `op` whose
  argument count is its operand arity), so a tree with operands still on the
  stack is never an operand either.
* **If conditions.** `.if_ bt [] t e` preceded by a single-value tree takes it as
  its condition, `.if_ bt [cond] t e`; this is `If::condition` in Binaryen.

Both are lowering-preserving for *every* arity and result-arity function, as
`lowerList_fold` states: `BExpr.lower (.if_ bt c t e)` is
`lowerList c ++ [if ..]`.

Trust: `foldDeep_lower` (F1) and `foldModule_lower` (F2) are proved, so the
folded module lowers to the input by construction. The driver still checks it per
run (`checkedLift`, by the executable equality `instrsEqb`, sound by
`instrsEqb_sound`) and falls back to the structured flat lift `structuredLift` (`structuredLift_lower`,
from `lowerList_liftInstrs`) on failure; `checkedLift_lower` covers both branches.

`Instr` has no `DecidableEq` instance (its `deriving` clause is `Repr` only), so
`instrEqb` is a hand-written structural equality, complete on the profile and
`false` (hence conservative) on everything else.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- The function type at a type index, if it is a function type. -/
def funcTypeAt? (m : Module) (x : TypeIdx) : Option FuncType :=
  match m.typeDefinitions[x.toNat]? with
  | some ⟨_, _, .func ft⟩ => some ft
  | _ => none

/-- The type indices of every function, imported then defined. -/
def funcTypeIdxs (m : Module) : List TypeIdx :=
  (m.imports.filterMap fun i => match i.type with | .func x => some x | _ => none) ++
    m.funcs.map (·.type)

/-- The function type of a function index. -/
def funcTypeOf? (m : Module) (f : FuncIdx) : Option FuncType :=
  (funcTypeIdxs m)[f.toNat]? >>= funcTypeAt? m

/-- The payload type of a tag index, with imported tags preceding defined tags. -/
def tagTypeOf? (m : Module) (x : TagIdx) : Option FuncType :=
  ((m.imports.filterMap fun i => match i.type with | .tag t => some t | _ => none) ++
    m.tags)[x.toNat]? >>= funcTypeAt? m

/-- Operand arities of flat instructions (how many stack values each pops), for
the profile, including `some 0` for nullary ones; `none` means unknown, and the
instruction is left unfolded. `nres` is the result count of the enclosing
function (the arity of `return`). Any choice is sound (`lowerList_foldB`); these
are Binaryen's trees. -/
def arityIn (m : Module) (nres : Option Nat) : Instr → Option Nat
  | .nop | .localGet _ | .globalGet _ | .intConst .. | .floatConst .. | .memorySize _ | .dataDrop _
  | .refNull _ | .refFunc _ | .tableSize _ | .elemDrop _ | .vecConst _ => some 0
  | .tableGet _ | .drop | .refIsNull | .throwRef | .localSet _ | .localTee _ | .globalSet _ | .brIf _ | .brTable _ _
  | .intUnOp _ _ | .intTestOp _ _ | .floatUnOp _ _ | .convert _ | .intLoad .. | .floatLoad .. | .memoryGrow _
  | .vecLoad .full .. | .vecSplat (.int .i32x4) | .vecExtractLane (.int .i32x4) none _ => some 1
  | .tableSet _ | .tableGrow _ | .intBinOp _ _ | .intRelOp _ _ | .floatBinOp _ _ | .floatRelOp _ _
  | .intStore .. | .floatStore ..
  | .vecStore .. | .vecIntBinOp .i32x4 .add | .vecIntBinOp .i32x4 .sub
  | .vecIntBinOp .i32x4 .mul | .vecIntBinOp .i32x4 (.min .signed) | .vecShiftOp .i32x4 (.shr _)
  | .vecExtBinOp .i32x4 .i64x2 (.extmul _ .signed) | .vecShuffle _ => some 2
  | .tableFill _ | .tableCopy .. | .tableInit .. | .select _ | .memoryFill _ | .memoryCopy ..
  | .memoryInit .. => some 3
  | .return_ => nres
  | .call f => (funcTypeOf? m f).map (·.params.length)
  | .callIndirect _ y => (funcTypeAt? m y).map (·.params.length + 1)
  | .throw x => (tagTypeOf? m x).map (·.params.length)
  | _ => none

/-- Operand arities with no enclosing function (`return` unfolded). -/
def arityOf (m : Module) : Instr → Option Nat := arityIn m none

/-- Result counts of flat instructions; `none` for stack-polymorphic or unknown ones. -/
def resultArityOf (m : Module) : Instr → Option Nat
  | .nop | .drop | .localSet _ | .globalSet _ | .brIf _ | .intStore .. | .floatStore ..
  | .tableSet _ | .tableFill _ | .tableCopy .. | .tableInit .. | .elemDrop _
  | .memoryFill _ | .memoryCopy .. | .memoryInit .. | .dataDrop _ | .vecStore .. => some 0
  | .localGet _ | .localTee _ | .globalGet _ | .intConst .. | .floatConst ..
  | .intUnOp _ _ | .intTestOp _ _ | .floatUnOp _ _ | .convert _
  | .intBinOp _ _ | .intRelOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ | .select _ | .intLoad .. | .floatLoad .. | .memorySize _ | .memoryGrow _
  | .refNull _ | .refIsNull | .refFunc _ | .tableGet _ | .tableSize _ | .tableGrow _ => some 1
  | .vecConst _ | .vecLoad .full .. | .vecSplat (.int .i32x4) | .vecExtractLane (.int .i32x4) none _
  | .vecIntBinOp .i32x4 .add | .vecIntBinOp .i32x4 .sub | .vecIntBinOp .i32x4 .mul
  | .vecIntBinOp .i32x4 (.min .signed)
  | .vecShiftOp .i32x4 (.shr _) | .vecExtBinOp .i32x4 .i64x2 (.extmul _ .signed)
  | .vecShuffle _ => some 1
  | .call f => (funcTypeOf? m f).map (·.results.length)
  | .callIndirect _ y => (funcTypeAt? m y).map (·.results.length)
  | _ => none

/-- Result count of a parameterless block type. -/
def blockResults (m : Module) : BlockType → Option Nat
  | .empty => some 0
  | .value _ => some 1
  | .typeIdx x => match funcTypeAt? m x with
    | some ft => if ft.params.isEmpty then some ft.results.length else none
    | none => none

/-- How many values a *complete* tree produces; `none` for incomplete trees (an
`op` with fewer folded operands than its arity, an `if` without its condition)
and for unknown or polymorphic ones. Shallow: completeness of the children holds
because `foldB` only folds trees with a result arity. -/
def resArity (m : Module) (ar : Instr → Option Nat) : BExpr → Option Nat
  | .op i args => if ar i == some args.length then resultArityOf m i else none
  | .block bt _ | .loop bt _ => blockResults m bt
  | .if_ bt c _ _ => if c.length == 1 then blockResults m bt else none
  | .tryTable .. => none

/-! ## The folding stack machine -/

/-- One step of the folding stack machine (most recent tree first). An instruction
of arity `n > 0` takes the top `n` trees when each produces one value; an `if`
without a condition takes a single-value top tree as its condition. -/
def foldStepB (ar : Instr → Option Nat) (ra : BExpr → Option Nat) (stk : List BExpr) :
    BExpr → List BExpr
  | .op i [] =>
    match ar i with
    | some (n + 1) =>
      if n + 1 ≤ stk.length ∧ (stk.take (n + 1)).all (fun e => ra e == some 1) = true then
        .op i (stk.take (n + 1)).reverse :: stk.drop (n + 1)
      else .op i [] :: stk
    | _ => .op i [] :: stk
  | .if_ bt [] th el =>
    match stk with
    | c :: rest => if ra c == some 1 then .if_ bt [c] th el :: rest else .if_ bt [] th el :: stk
    | [] => [.if_ bt [] th el]
  | e => e :: stk

/-- Fold a list of trees (one level). -/
def foldB (ar : Instr → Option Nat) (ra : BExpr → Option Nat) (es : List BExpr) : List BExpr :=
  (es.foldl (foldStepB ar ra) []).reverse

theorem lowerList_foldStepB (ar : Instr → Option Nat) (ra : BExpr → Option Nat)
    (stk : List BExpr) (e : BExpr) :
    BExpr.lowerList (foldStepB ar ra stk e).reverse =
      BExpr.lowerList stk.reverse ++ e.lower := by
  unfold foldStepB
  split
  · split
    · split
      · exact lowerList_reverse_take_drop _ _ _
      · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]
    · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]
  · split
    · split
      · simp only [List.reverse_cons, BExpr.lowerList_append,
          BExpr.lower, BExpr.lowerList_cons, BExpr.lowerList_nil, List.append_nil,
          List.nil_append, List.append_assoc]
      · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]
    · simp only [List.reverse_cons, List.reverse_nil,
        BExpr.lowerList_singleton, List.nil_append, BExpr.lowerList_nil]
  · simp only [List.reverse_cons, BExpr.lowerList_append, BExpr.lowerList_singleton]

theorem lowerList_foldl_foldStepB (ar : Instr → Option Nat) (ra : BExpr → Option Nat)
    (es stk : List BExpr) :
    BExpr.lowerList (es.foldl (foldStepB ar ra) stk).reverse =
      BExpr.lowerList stk.reverse ++ BExpr.lowerList es := by
  induction es generalizing stk with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, lowerList_foldStepB, BExpr.lowerList_cons, List.append_assoc]

/-- **`foldB` never changes the lowering**, for every arity and result-arity function. -/
theorem lowerList_foldB (ar : Instr → Option Nat) (ra : BExpr → Option Nat) (es : List BExpr) :
    BExpr.lowerList (foldB ar ra es) = BExpr.lowerList es := by
  have h := lowerList_foldl_foldStepB ar ra es []
  simpa [foldB] using h

/-! ## Deep folding -/

mutual
/-- Fold every body of a tree. -/
def foldE (ar : Instr → Option Nat) (ra : BExpr → Option Nat) : BExpr → BExpr
  | .op i args => .op i (foldL ar ra args)
  | .block bt b => .block bt (foldB ar ra (foldL ar ra b))
  | .loop bt b => .loop bt (foldB ar ra (foldL ar ra b))
  | .if_ bt c t e =>
    .if_ bt (foldB ar ra (foldL ar ra c)) (foldB ar ra (foldL ar ra t))
      (foldB ar ra (foldL ar ra e))
  | .tryTable bt cs b => .tryTable bt cs (foldB ar ra (foldL ar ra b))
/-- `foldE` on a list. -/
def foldL (ar : Instr → Option Nat) (ra : BExpr → Option Nat) : List BExpr → List BExpr
  | [] => []
  | e :: es => foldE ar ra e :: foldL ar ra es
end

mutual
theorem lower_foldE (ar : Instr → Option Nat) (ra : BExpr → Option Nat) :
    ∀ e : BExpr, (foldE ar ra e).lower = e.lower
  | .op i args => by
    simp only [foldE, BExpr.lower_op, lowerList_foldL ar ra args]
  | .block bt b => by
    simp only [foldE, BExpr.lower, lowerList_foldB, lowerList_foldL ar ra b]
  | .loop bt b => by
    simp only [foldE, BExpr.lower, lowerList_foldB, lowerList_foldL ar ra b]
  | .if_ bt c t e => by
    simp only [foldE, BExpr.lower, lowerList_foldB, lowerList_foldL ar ra c,
      lowerList_foldL ar ra t, lowerList_foldL ar ra e]
  | .tryTable bt cs b => by
    simp only [foldE, BExpr.lower, lowerList_foldB, lowerList_foldL ar ra b]
theorem lowerList_foldL (ar : Instr → Option Nat) (ra : BExpr → Option Nat) :
    ∀ es : List BExpr, BExpr.lowerList (foldL ar ra es) = BExpr.lowerList es
  | [] => rfl
  | e :: es => by
    simp only [foldL, BExpr.lowerList_cons, lower_foldE ar ra e, lowerList_foldL ar ra es]
end

/-- Lift a flat body to trees: structured lift, then fold at every level. -/
def foldDeep (ar : Instr → Option Nat) (ra : BExpr → Option Nat) (is : List Instr) :
    List BExpr :=
  foldB ar ra (foldL ar ra (liftInstrs is))

/-- Fold one function, with `return` taking the function's results as operands. -/
def foldFunc (m : Module) (f : Func) : BFunc :=
  let ar := arityIn m ((funcTypeAt? m f.type).map (·.results.length))
  f.mapBody (foldDeep ar (resArity m ar))

/-- The folding lift of a module. -/
def foldModule (m : Module) : BModule :=
  ⟨m, m.funcs.map (foldFunc m)⟩

/-- **F1.** Deep folding preserves the lowering. -/
theorem foldDeep_lower (ar : Instr → Option Nat) (ra : BExpr → Option Nat) (is : List Instr) :
    BExpr.lowerList (foldDeep ar ra is) = is := by
  rw [foldDeep, lowerList_foldB, lowerList_foldL, lowerList_liftInstrs]

theorem foldFunc_lower (m : Module) (f : Func) :
    Declaration.Func.mapBody BExpr.lowerList (foldFunc m f) = f := by
  rcases f with ⟨t, ls, body⟩
  simp only [foldFunc, Declaration.Func.mapBody, foldDeep_lower]

/-- **F2.** The folding lift of a module lowers back to it. -/
theorem foldModule_lower (m : Module) : (foldModule m).lower = m := by
  have h : (m.funcs.map (foldFunc m)).map (Declaration.Func.mapBody BExpr.lowerList) =
      m.funcs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id m.funcs]
    exact List.map_congr_left (fun f _ => foldFunc_lower m f)
  simp only [BModule.lower, foldModule, h]

/-! ## Executable equality of instructions -/

mutual
/-- Structural equality on profile instructions; `false` outside the profile. -/
def instrEqb : Instr → Instr → Bool
  | .nop, .nop | .unreachable, .unreachable | .drop, .drop | .return_, .return_ => true
  | .select none, .select none => true
  | .block bt b, .block bt' b' | .loop bt b, .loop bt' b' => bt == bt' && instrsEqb b b'
  | .if_ bt t e, .if_ bt' t' e' => bt == bt' && instrsEqb t t' && instrsEqb e e'
  | .br l, .br l' | .brIf l, .brIf l' => l == l'
  | .brTable ls l, .brTable ls' l' => ls == ls' && l == l'
  | .call f, .call f' => f == f'
  | .throw x, .throw y => x == y
  | .throwRef, .throwRef => true
  | .tryTable bt cs b, .tryTable bt' cs' b' => bt == bt' && cs == cs' && instrsEqb b b'
  | .callIndirect x y, .callIndirect x' y' => x == x' && y == y'
  | .localGet x, .localGet x' | .localSet x, .localSet x' | .localTee x, .localTee x' =>
      x == x'
  | .globalGet x, .globalGet x' | .globalSet x, .globalSet x' => x == x'
  | .memorySize x, .memorySize y | .memoryGrow x, .memoryGrow y
  | .memoryFill x, .memoryFill y => x == y
  | .memoryCopy x y, .memoryCopy u v => x == u && y == v
  | .memoryInit x d, .memoryInit y e => x == y && d == e
  | .dataDrop d, .dataDrop e | .elemDrop d, .elemDrop e => d == e
  | .tableGet x, .tableGet y | .tableSet x, .tableSet y
  | .tableSize x, .tableSize y | .tableGrow x, .tableGrow y
  | .tableFill x, .tableFill y => x == y
  | .tableCopy x y, .tableCopy u v => x == u && y == v
  | .tableInit x d, .tableInit y e => x == y && d == e
  | .intLoad t p x a, .intLoad t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | .intStore t p x a, .intStore t' p' x' a' => t == t' && p == p' && x == x' && a == a'
  | .intConst t b, .intConst t' b' => t == t' && b.toNat == b'.toNat
  | .intUnOp t o, .intUnOp t' o' => t == t' && o == o'
  | .intBinOp t o, .intBinOp t' o' => t == t' && o == o'
  | .intTestOp t o, .intTestOp t' o' => t == t' && o == o'
  | .intRelOp t o, .intRelOp t' o' => t == t' && o == o'
  | .floatLoad t x a, .floatLoad t' x' a' | .floatStore t x a, .floatStore t' x' a' =>
      t == t' && x == x' && a == a'
  | .floatConst t b, .floatConst t' b' => t == t' && b.toNat == b'.toNat
  | .floatUnOp t o, .floatUnOp t' o' => t == t' && o == o'
  | .floatBinOp t o, .floatBinOp t' o' => t == t' && o == o'
  | .floatRelOp t o, .floatRelOp t' o' => t == t' && o == o'
  | .convert o, .convert o' => o == o'
  | _, _ => false
/-- `instrEqb` on lists. -/
def instrsEqb : List Instr → List Instr → Bool
  | [], [] => true
  | i :: is, i' :: is' => instrEqb i i' && instrsEqb is is'
  | _, _ => false
end

/-- List soundness from element soundness. -/
theorem instrsEqb_sound_of {b b' : List Instr} (h : instrsEqb b b' = true)
    (ih : ∀ j ∈ b, ∀ j', instrEqb j j' = true → j = j') : b = b' := by
  induction b generalizing b' with
  | nil =>
    cases b' with
    | nil => rfl
    | cons j' js' => unfold instrsEqb at h; simp at h
  | cons j js ihl =>
    cases b' with
    | nil => unfold instrsEqb at h; simp at h
    | cons j' js' =>
      unfold instrsEqb at h
      simp only [Bool.and_eq_true] at h
      rw [ih j (by simp) j' h.1, ihl h.2 (fun k hk => ih k (by simp [hk]))]

/-- `instrEqb` is sound, by induction on a size bound. -/
theorem instrEqb_sound_lt :
    ∀ (n : Nat) (i i' : Instr), sizeOf i < n → instrEqb i i' = true → i = i'
  | 0, _, _, hs, _ => absurd hs (Nat.not_lt_zero _)
  | n + 1, i, i', hs, h => by
    have hlist : ∀ b b' : List Instr, sizeOf b < n → instrsEqb b b' = true → b = b' :=
      fun b _ hb hbb => instrsEqb_sound_of hbb fun j hj j' =>
        instrEqb_sound_lt n j j' (by have := List.sizeOf_lt_of_mem hj; omega)
    unfold instrEqb at h
    split at h
    all_goals (try simp only [Bool.and_eq_true, beq_iff_eq] at h)
    all_goals first
      | rfl
      | (subst h; rfl)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl)
      | (simp at h; done)
      | (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h)
      | (obtain ⟨⟨rfl, h2⟩, h3⟩ := h; simp only [Instr.if_.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2, hlist _ _ (by omega) h3])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.block.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; simp only [Instr.loop.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨⟨rfl, rfl⟩, h2⟩ := h; simp only [Instr.tryTable.sizeOf_spec] at hs;
         rw [hlist _ _ (by omega) h2])
      | (obtain ⟨rfl, h2⟩ := h; rw [BitVec.eq_of_toNat_eq h2])
      | (obtain ⟨rfl, -⟩ := h; cases ‹IntTestOp›; cases ‹IntTestOp›; rfl)

theorem instrEqb_sound {i i' : Instr} (h : instrEqb i i' = true) : i = i' :=
  instrEqb_sound_lt _ i i' (Nat.lt_succ_self _) h

/-- **`instrsEqb` is sound.** -/
theorem instrsEqb_sound {is is' : List Instr} (h : instrsEqb is is' = true) : is = is' :=
  instrsEqb_sound_of h fun _ _ _ => instrEqb_sound

/-- Executable check that two modules have the same function bodies. -/
def sameBodies (m m' : Module) : Bool :=
  m.funcs.length == m'.funcs.length &&
    (m.funcs.zip m'.funcs).all fun (f, f') =>
      f.type == f'.type && f.locals == f'.locals && instrsEqb f.body f'.body

theorem funcs_eq_of_all {fs fs' : List Func} (hl : fs.length = fs'.length)
    (h : ((fs.zip fs').all fun (f, f') =>
      f.type == f'.type && f.locals == f'.locals && instrsEqb f.body f'.body) = true) :
    fs = fs' := by
  induction fs generalizing fs' with
  | nil => cases fs' with
    | nil => rfl
    | cons => simp at hl
  | cons f fs ih => cases fs' with
    | nil => simp at hl
    | cons f' fs' =>
      rcases f with ⟨t, l, b⟩
      rcases f' with ⟨t', l', b'⟩
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, h3⟩, h4⟩ := h
      obtain rfl : b = b' := instrsEqb_sound h3
      rw [ih (by simpa using hl) h4]

/-- **`sameBodies` is sound**: equal function lists. -/
theorem sameBodies_sound {m m' : Module} (h : sameBodies m m' = true) :
    m.funcs = m'.funcs := by
  simp only [sameBodies, Bool.and_eq_true, beq_iff_eq] at h
  exact funcs_eq_of_all h.1 h.2

/-- **Structured flat lift**: structured control as tree nodes (`liftInstrs`), every
other instruction a leaf with no operands. Unlike `BModule.lift` (whole `block`/`loop`/`if`
as one leaf, which `BExpr.inProfile` rejects) its result can be in the profile. -/
def structuredLift (m : Module) : BModule :=
  ⟨m, m.funcs.map (Declaration.Func.mapBody liftInstrs)⟩

theorem structuredLift_lower (m : Module) : (structuredLift m).lower = m := by
  cases m with
  | mk types imports tags globals memories tables funcs data elems start exports =>
    have h : (funcs.map (Declaration.Func.mapBody liftInstrs)).map
        (Declaration.Func.mapBody BExpr.lowerList) = funcs := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id funcs]
      refine List.map_congr_left (fun f _ => ?_)
      rcases f with ⟨t, ls, body⟩
      simp [Declaration.Func.mapBody, lowerList_liftInstrs]
    simp only [BModule.lower, structuredLift, h]

/-- **The checked lift.** The folded module when its lowering is checked equal to the
input, otherwise the structured flat lift `structuredLift`; the flag says which. Either way `(checkedLift m).1.lower = m`
(`checkedLift_lower`). Since F1/F2 are proved the folded branch is correct by
construction; the check is kept as the runtime witness, reported as `folded`. -/
def checkedLift (m : Module) : BModule × Bool :=
  let f := foldModule m
  if sameBodies f.lower m then (f, true) else (structuredLift m, false)

theorem checkedLift_lower (m : Module) : (checkedLift m).1.lower = m := by
  unfold checkedLift
  dsimp only
  split
  · exact foldModule_lower m
  · exact structuredLift_lower m

end Silmaril.Wasm.Binaryen.Exe
