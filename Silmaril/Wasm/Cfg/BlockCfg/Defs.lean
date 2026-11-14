module

public import Silmaril.Wasm.Cfg.BlockTree.Defs
public import Silmaril.Wasm.Cfg.Defs

@[expose] public section

/-!
# The basic-block CFG of a function body: the edge relation

The nodes are the blocks `lookup` names (`Silmaril.Wasm.Cfg.BlockTree.Defs`) and four special
targets: `exit` (the function returns), `trap` (`unreachable`), `raise` (an exception leaves
the function) and `invalid` (a branch to a label that does not exist, so the body is invalid).

The edges are defined from `lookup` alone, with no builder:
* `entry body p i` is where control goes on reaching position `i` of sequence `p`: the block
  there if there is one, else the continuation `cont body p` of the sequence. The body's own
  continuation is `exit`. The continuation of a nested sequence is its parent's entry just after
  the opening block.
* `labels body p` lists the label targets in scope in sequence `p`, innermost first. A `loop`'s
  label is its body's entry. The label of a `block`, `if` or `try_table` is its continuation.
  The function's own label (the outermost one) is `exit`.
* `succOf body b s` gives the successors of block `b` with segment `s`, determined by its
  terminator: structured instructions enter their arms; `try_table` also has an edge to each
  catch label; branches resolve by depth; `return` and tail calls exit; `unreachable` traps;
  `throw` and `throw_ref` raise. A block without a terminator falls through.

Scope: these are the edges of the control instructions. Traps of ordinary instructions
(division, memory bounds, calls) and exceptions raised inside a `try_table` body are not
edges here: the `try_table` block's catch edges stand for them.
-/

namespace Silmaril.Wasm.Cfg

/-- A node of the basic-block CFG. -/
inductive Target where
  | block (b : BlockId)
  | exit
  | trap
  | raise
  | invalid
  deriving DecidableEq, Repr

/-- The continuation of the sequence at the reversed path `rp`. -/
def contRev (body : Expr) : List SeqStep → Target
  | [] => .exit
  | (m, _) :: rp =>
    if (lookup body ⟨rp.reverse, m + 1⟩).isSome then .block ⟨rp.reverse, m + 1⟩ else contRev body rp

/-- The continuation of sequence `p`: where control goes when `p` finishes. -/
def cont (body : Expr) (p : List SeqStep) : Target := contRev body p.reverse

/-- Where control goes on reaching position `i` of sequence `p`. -/
def entry (body : Expr) (p : List SeqStep) (i : Nat) : Target :=
  if (lookup body ⟨p, i⟩).isSome then .block ⟨p, i⟩ else cont body p

/-- Whether the block `⟨p, m⟩` ends with a `loop`. -/
def isLoopAt (body : Expr) (p : List SeqStep) (m : Nat) : Bool :=
  match lookup body ⟨p, m⟩ with
  | some ⟨_, some (.loop ..)⟩ => true
  | _ => false

/-- The label targets in scope in the sequence at the reversed path `rp`, innermost first. -/
def labelsRev (body : Expr) : List SeqStep → List Target
  | [] => [.exit]
  | (m, a) :: rp =>
    (if isLoopAt body rp.reverse m then entry body (rp.reverse ++ [(m, a)]) 0
      else contRev body ((m, a) :: rp)) :: labelsRev body rp

/-- The label targets in scope in sequence `p`, innermost first. -/
def labels (body : Expr) (p : List SeqStep) : List Target := labelsRev body p.reverse

/-- The target of branching to label `l` under the label targets `ℓ`. -/
def resolveT (ℓ : List Target) (l : LabelIdx) : Target := ℓ.getD l.value.val .invalid

/-- The successors of block `b`, whose segment is `s`. -/
def succOf (body : Expr) (b : BlockId) (s : Segment) : List Target :=
  let next := entry body b.seq (b.idx + 1)
  let ℓ := labels body b.seq
  let arm (a : Nat) := entry body (b.seq ++ [(b.idx, a)]) 0
  match s.term with
  | none => [next]
  | some (.block ..) | some (.loop ..) => [arm 0]
  | some (.if_ ..) => [arm 0, arm 1]
  | some (.tryTable _ cs _) => arm 0 :: cs.map fun c => resolveT ℓ (catchLabel c)
  | some (.br l) => [resolveT ℓ l]
  | some (.brIf l) | some (.brOnNull l) | some (.brOnNonNull l) | some (.brOnCast l ..)
  | some (.brOnCastFail l ..) => [resolveT ℓ l, next]
  | some (.brTable ls d) => (ls ++ [d]).map (resolveT ℓ)
  | some .return_ | some (.returnCall _) | some (.returnCallRef _)
  | some (.returnCallIndirect ..) => [.exit]
  | some .unreachable => [.trap]
  | some (.throw _) | some .throwRef => [.raise]
  | some _ => [next]

/-- The entry node of the CFG. -/
def cfgEntry (body : Expr) : Target := entry body [] 0

/-- **The basic-block CFG edge relation**: `t` is a successor of block `b`. -/
def Edge (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ s, lookup body b = some s ∧ t ∈ succOf body b s

/-! ## The builder: one pass, with the continuation and label targets in context -/

/-- Where control goes entering a nested sequence `c` at `path`: its first block, else `next`. -/
def armEntry (path : List SeqStep) (c : List Instr) (next : Target) : Target :=
  if c.isEmpty then next else .block ⟨path, 0⟩

/-- The successors of the block `⟨path, k⟩` ending with terminator `i`, given its fall-through
`next` and the label targets `ℓ`. -/
def succE (path : List SeqStep) (k : Nat) (next : Target) (ℓ : List Target) (i : Instr) :
    List Target :=
  let arm (a : Nat) (c : List Instr) := armEntry (path ++ [(k, a)]) c next
  match i with
  | .block _ b | .loop _ b => [arm 0 b]
  | .if_ _ t e => [arm 0 t, arm 1 e]
  | .tryTable _ cs b => arm 0 b :: cs.map fun c => resolveT ℓ (catchLabel c)
  | .br l => [resolveT ℓ l]
  | .brIf l | .brOnNull l | .brOnNonNull l | .brOnCast l .. | .brOnCastFail l .. =>
    [resolveT ℓ l, next]
  | .brTable ls d => (ls ++ [d]).map (resolveT ℓ)
  | .return_ | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. => [.exit]
  | .unreachable => [.trap]
  | .throw _ | .throwRef => [.raise]
  | _ => [next]

mutual
/-- The blocks of a sequence with their successors, as `walk` (`BlockTree.Defs`) with the
sequence's continuation `cn` and label targets `ℓ` in context. -/
def walkE (path : List SeqStep) (k : Nat) (acc : List Instr) (cn : Target) (ℓ : List Target) :
    List Instr → List (BlockId × List Target)
  | [] => if acc.isEmpty then [] else [(⟨path, k⟩, [cn])]
  | i :: is =>
    if isTerminator i then
      let next := if is.isEmpty then cn else .block ⟨path, k + 1⟩
      (⟨path, k⟩, succE path k next ℓ i) ::
        (nestedE path k next ℓ i ++ walkE path (k + 1) [] cn ℓ is)
    else walkE path k (i :: acc) cn ℓ is
/-- The blocks, with successors, of the sequences that the terminator of block `k` opens. -/
def nestedE (path : List SeqStep) (k : Nat) (next : Target) (ℓ : List Target) :
    Instr → List (BlockId × List Target)
  | .block _ b | .tryTable _ _ b => walkE (path ++ [(k, 0)]) 0 [] next (next :: ℓ) b
  | .loop _ b =>
    walkE (path ++ [(k, 0)]) 0 [] next (armEntry (path ++ [(k, 0)]) b next :: ℓ) b
  | .if_ _ t e =>
    walkE (path ++ [(k, 0)]) 0 [] next (next :: ℓ) t ++
      walkE (path ++ [(k, 1)]) 0 [] next (next :: ℓ) e
  | _ => []
end

/-- **The basic-block CFG of a body**, as an adjacency list built in one pass. -/
def blockCfg (body : Expr) : List (BlockId × List Target) := walkE [] 0 [] .exit [.exit] body

end Silmaril.Wasm.Cfg
