module

public import Silmaril.Wasm.Binaryen.Lower

@[expose] public section

/-! # Core-instruction traversals used by the IR analyses

Free branch targets, referenced globals, index renaming and tail-call
detection on Core 3.0 `Instr`. They are stated on Core instructions so that the
IR versions are literally "the traversal of the lowering"
(`BExpr.labels e = instrsLabels e.lower`), keeping every analysis anchored on the
defining semantics. The recursion follows `Validation.Instr.freeFuncs`.

Binaryen counterparts (version_133): `BranchUtils::getExitingBranches`
(`src/ir/branch-utils.h`), the global and call scans of
`RemoveUnusedModuleElements` (`src/passes/RemoveUnusedModuleElements.cpp`).
-/

namespace Silmaril.Wasm.Binaryen

/-- Drop label `0` and shift the others down: the free labels of a body seen from
outside the construct that binds label `0`. -/
def unbind (ns : List Nat) : List Nat :=
  ns.filterMap fun n => if n = 0 then none else some (n - 1)

/-- The label a handler branches to (outside the `try_table`). -/
def Catch.label : Catch → Nat
  | .catch_ _ l | .catchRef _ l | .catchAll l | .catchAllRef l => l.toNat

/-- Free branch targets of an instruction, as de Bruijn depths relative to the
instruction's own context. -/
def instrLabels : Instr → List Nat
  | .br l | .brIf l | .brOnNull l | .brOnNonNull l => [l.toNat]
  | .brOnCast l _ _ | .brOnCastFail l _ _ => [l.toNat]
  | .brTable ls d => d.toNat :: ls.map Idx.toNat
  | .block _ body | .loop _ body => unbind (body.attach.flatMap fun i => instrLabels i.val)
  | .if_ _ b₁ b₂ =>
      unbind (b₁.attach.flatMap (fun i => instrLabels i.val) ++
        b₂.attach.flatMap (fun i => instrLabels i.val))
  | .tryTable _ cs body =>
      cs.map Catch.label ++ unbind (body.attach.flatMap fun i => instrLabels i.val)
  | _ => []
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- Free branch targets of a sequence. -/
def instrsLabels (is : List Instr) : List Nat := is.flatMap instrLabels

/-- Global indices an instruction reads or writes. -/
def instrGlobals : Instr → List Nat
  | .globalGet g | .globalSet g => [g.toNat]
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.flatMap fun i => instrGlobals i.val
  | .if_ _ b₁ b₂ =>
      b₁.attach.flatMap (fun i => instrGlobals i.val) ++
        b₂.attach.flatMap (fun i => instrGlobals i.val)
  | _ => []
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- Global indices referenced by a sequence. -/
def instrsGlobals (is : List Instr) : List Nat := is.flatMap instrGlobals

/-- Does the instruction contain a tail call? (`return_call*`). -/
def instrHasTailCall : Instr → Bool
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ => true
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      body.attach.any fun i => instrHasTailCall i.val
  | .if_ _ b₁ b₂ =>
      b₁.attach.any (fun i => instrHasTailCall i.val) ||
        b₂.attach.any (fun i => instrHasTailCall i.val)
  | _ => false
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- An index renaming for functions and globals (absolute indices). -/
structure Ren where
  func : Nat → Nat
  global : Nat → Nat

namespace Ren

def funcIdx (ρ : Ren) (f : FuncIdx) : FuncIdx := (Idx.ofNat? (ρ.func f.toNat)).getD f
def globalIdx (ρ : Ren) (g : GlobalIdx) : GlobalIdx := (Idx.ofNat? (ρ.global g.toNat)).getD g

/-- Rename function and global indices inside an instruction. -/
def instr (ρ : Ren) : Instr → Instr
  | .call f => .call (ρ.funcIdx f)
  | .returnCall f => .returnCall (ρ.funcIdx f)
  | .refFunc f => .refFunc (ρ.funcIdx f)
  | .globalGet g => .globalGet (ρ.globalIdx g)
  | .globalSet g => .globalSet (ρ.globalIdx g)
  | .block bt body => .block bt (body.attach.map fun i => instr ρ i.val)
  | .loop bt body => .loop bt (body.attach.map fun i => instr ρ i.val)
  | .if_ bt b₁ b₂ =>
      .if_ bt (b₁.attach.map fun i => instr ρ i.val) (b₂.attach.map fun i => instr ρ i.val)
  | .tryTable bt cs body => .tryTable bt cs (body.attach.map fun i => instr ρ i.val)
  | i => i
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

/-- Rename inside a sequence. -/
def instrs (ρ : Ren) (is : List Instr) : List Instr := is.map ρ.instr

mutual
/-- Rename inside a folded tree. -/
def bexpr (ρ : Ren) : BExpr → BExpr
  | .op i args => .op (ρ.instr i) (Ren.bexprs ρ args)
  | .block bt b => .block bt (Ren.bexprs ρ b)
  | .loop bt b => .loop bt (Ren.bexprs ρ b)
  | .if_ bt c t e => .if_ bt (Ren.bexprs ρ c) (Ren.bexprs ρ t) (Ren.bexprs ρ e)
  | .tryTable bt cs b => .tryTable bt cs (Ren.bexprs ρ b)
/-- Rename inside a list of trees. -/
def bexprs (ρ : Ren) : List BExpr → List BExpr
  | [] => []
  | e :: es => Ren.bexpr ρ e :: Ren.bexprs ρ es
end

theorem instr_block (ρ : Ren) (bt : BlockType) (body : List Instr) :
    ρ.instr (.block bt body) = .block bt (body.map ρ.instr) := by
  rw [Ren.instr]; simp only [List.attach_map_val]

theorem instr_loop (ρ : Ren) (bt : BlockType) (body : List Instr) :
    ρ.instr (.loop bt body) = .loop bt (body.map ρ.instr) := by
  rw [Ren.instr]; simp only [List.attach_map_val]

theorem instr_if (ρ : Ren) (bt : BlockType) (b₁ b₂ : List Instr) :
    ρ.instr (.if_ bt b₁ b₂) = .if_ bt (b₁.map ρ.instr) (b₂.map ρ.instr) := by
  rw [Ren.instr]; simp only [List.attach_map_val]

theorem instr_tryTable (ρ : Ren) (bt : BlockType) (cs : List Catch) (body : List Instr) :
    ρ.instr (.tryTable bt cs body) = .tryTable bt cs (body.map ρ.instr) := by
  rw [Ren.instr]; simp only [List.attach_map_val]

mutual
theorem lower_bexpr_aux (ρ : Ren) : (e : BExpr) →
    (ρ.bexpr e).lower = (BExpr.lower e).map ρ.instr
  | .op i args => by
    simp only [bexpr, BExpr.lower, List.map_append, List.map_cons, List.map_nil,
      lowerList_bexprs_aux ρ args]
  | .block bt b => by
    simp only [bexpr, BExpr.lower, List.map_cons, List.map_nil, instr_block,
      lowerList_bexprs_aux ρ b]
  | .loop bt b => by
    simp only [bexpr, BExpr.lower, List.map_cons, List.map_nil, instr_loop,
      lowerList_bexprs_aux ρ b]
  | .if_ bt c t e => by
    simp only [bexpr, BExpr.lower, List.map_append, List.map_cons, List.map_nil, instr_if,
      lowerList_bexprs_aux ρ c, lowerList_bexprs_aux ρ t, lowerList_bexprs_aux ρ e]
  | .tryTable bt cs b => by
    simp only [bexpr, BExpr.lower, List.map_cons, List.map_nil, instr_tryTable,
      lowerList_bexprs_aux ρ b]
theorem lowerList_bexprs_aux (ρ : Ren) : (es : List BExpr) →
    BExpr.lowerList (ρ.bexprs es) = (BExpr.lowerList es).map ρ.instr
  | [] => rfl
  | e :: es => by
    simp only [bexprs, BExpr.lowerList_cons, List.map_append, lower_bexpr_aux ρ e,
      lowerList_bexprs_aux ρ es]
end

/-- Renaming commutes with lowering. -/
theorem lowerList_bexprs (ρ : Ren) (es : List BExpr) :
    BExpr.lowerList (ρ.bexprs es) = ρ.instrs (BExpr.lowerList es) :=
  lowerList_bexprs_aux ρ es

end Ren

/-- Free branch targets of a folded tree: those of its lowering. -/
def BExpr.labels (e : BExpr) : List Nat := instrsLabels e.lower

/-- Free branch targets of a list of trees. -/
def BExpr.labelsList (es : List BExpr) : List Nat := instrsLabels (BExpr.lowerList es)

/-! ### Free branch targets without lowering

`BExpr.labels` and `BExpr.labelsList` are defined through the lowering. Compiled code
computes the same lists on the trees instead (`@[csimp]`), so callers that ask for the
labels of every block body (`isBot`, the unwrapping checks) do not lower each body. -/

mutual
/-- `BExpr.labels`, computed on the tree. -/
def BExpr.labelsFast : BExpr → List Nat
  | .op i args => BExpr.labelsListFast args ++ instrLabels i
  | .block _ b => unbind (BExpr.labelsListFast b)
  | .loop _ b => unbind (BExpr.labelsListFast b)
  | .if_ _ c t e =>
      BExpr.labelsListFast c ++ unbind (BExpr.labelsListFast t ++ BExpr.labelsListFast e)
  | .tryTable _ cs b => cs.map Catch.label ++ unbind (BExpr.labelsListFast b)
/-- `BExpr.labelsList`, computed on the trees. -/
def BExpr.labelsListFast : List BExpr → List Nat
  | [] => []
  | e :: es => BExpr.labelsFast e ++ BExpr.labelsListFast es
end

private theorem flatMap_attach_val_labels {α β : Type} (l : List α) (f : α → List β) :
    (l.attach.flatMap fun i => f i.val) = l.flatMap f := by
  conv_rhs => rw [← List.attach_map_subtype_val l]
  rw [List.flatMap_map]

private theorem instrsLabels_append' (a b : List Instr) :
    instrsLabels (a ++ b) = instrsLabels a ++ instrsLabels b := by
  simp [instrsLabels]

private theorem instrsLabels_single' (i : Instr) : instrsLabels [i] = instrLabels i := by
  simp [instrsLabels]

private theorem instrLabels_nested (i : Instr) : instrLabels i =
    match i with
    | .block _ body | .loop _ body => unbind (instrsLabels body)
    | .if_ _ b₁ b₂ => unbind (instrsLabels b₁ ++ instrsLabels b₂)
    | .tryTable _ cs body => cs.map Catch.label ++ unbind (instrsLabels body)
    | i => instrLabels i := by
  cases i <;> first | rfl | (rw [instrLabels.eq_def]; simp only [flatMap_attach_val_labels, instrsLabels])

mutual
theorem BExpr.labelsFast_eq : ∀ e : BExpr, BExpr.labelsFast e = BExpr.labels e
  | .op i args => by
      rw [BExpr.labelsFast, BExpr.labelsListFast_eq args, BExpr.labels, BExpr.labelsList,
        BExpr.lower, instrsLabels_append', instrsLabels_single']
  | .block bt b => by
      rw [BExpr.labelsFast, BExpr.labelsListFast_eq b, BExpr.labels, BExpr.labelsList,
        BExpr.lower, instrsLabels_single', instrLabels_nested]
  | .loop bt b => by
      rw [BExpr.labelsFast, BExpr.labelsListFast_eq b, BExpr.labels, BExpr.labelsList,
        BExpr.lower, instrsLabels_single', instrLabels_nested]
  | .if_ bt c t e => by
      rw [BExpr.labelsFast, BExpr.labelsListFast_eq c, BExpr.labelsListFast_eq t,
        BExpr.labelsListFast_eq e, BExpr.labels, BExpr.labelsList, BExpr.labelsList,
        BExpr.labelsList, BExpr.lower, instrsLabels_append', instrsLabels_single',
        instrLabels_nested]
  | .tryTable bt cs b => by
      rw [BExpr.labelsFast, BExpr.labelsListFast_eq b, BExpr.labels, BExpr.labelsList,
        BExpr.lower, instrsLabels_single', instrLabels_nested]
theorem BExpr.labelsListFast_eq : ∀ es : List BExpr,
    BExpr.labelsListFast es = BExpr.labelsList es
  | [] => rfl
  | e :: es => by
      rw [BExpr.labelsListFast, BExpr.labelsFast_eq e, BExpr.labelsListFast_eq es, BExpr.labels,
        BExpr.labelsList, BExpr.labelsList, BExpr.lowerList, instrsLabels_append']
end

/-- Compiled code computes `BExpr.labels` on the tree. -/
@[csimp] theorem BExpr.labels_eq_fast : @BExpr.labels = @BExpr.labelsFast := by
  funext e; exact (BExpr.labelsFast_eq e).symm

/-- Compiled code computes `BExpr.labelsList` on the trees. -/
@[csimp] theorem BExpr.labelsList_eq_fast : @BExpr.labelsList = @BExpr.labelsListFast := by
  funext es; exact (BExpr.labelsListFast_eq es).symm

end Silmaril.Wasm.Binaryen
