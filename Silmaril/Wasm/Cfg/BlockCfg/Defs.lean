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

**Scope: a syntactic, incomplete graph.** `Edge` is defined from the instruction tree by the
structured-control rules above. It is not derived from, or proved against, the execution
semantics: no theorem here says that a run of the function follows these edges.
- `Edge` holds the edges of the control instructions only.
- What other instructions may do is recorded separately, as *effect marks* (`blockEffects`) and
  *effect edges* (`effectSucc`, below):
  - instructions that may trap (division, truncation, memory and table accesses, null and cast
    checks, array bounds) give a `trap` effect edge;
  - calls may trap, raise or not return, so they give `trap` and `raise` effect edges;
  - a block inside a `try_table` body that raises (by `throw` or a call) is marked
    `unresolvedHandler`: its exception may be caught by the enclosing `try_table`, and this
    graph does not resolve which handler catches it.
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

/-! ## Effect marks and effect edges

Syntactic marks of what a block's instructions may do besides its control edges. They are
conservative ("may"), not derived from the semantics. -/

/-- An effect a block may have besides its control edges. -/
inductive Effect where
  /-- An instruction may trap (division, truncation, memory, table, null, cast, array bounds). -/
  | mayTrap
  /-- A call: the callee may trap, raise, or not return. -/
  | call
  /-- The block may raise inside a `try_table` body; the catching handler is not resolved. -/
  | unresolvedHandler
  deriving DecidableEq, Repr

/-- The effects of one instruction (not counting the control edges of terminators). -/
def instrEffects : Instr → List Effect
  | .call _ | .returnCall _ => [.call]
  | .callRef _ | .callIndirect .. | .returnCallRef _ | .returnCallIndirect .. => [.call, .mayTrap]
  | .intBinOp _ (.div _) | .intBinOp _ (.rem _) | .convert (.trunc ..) => [.mayTrap]
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad .. | .vecLoadLane ..
  | .vecStore .. | .vecStoreLane .. | .memoryFill _ | .memoryCopy .. | .memoryInit .. => [.mayTrap]
  | .tableGet _ | .tableSet _ | .tableFill _ | .tableCopy .. | .tableInit .. => [.mayTrap]
  | .refAsNonNull | .refCast _ | .i31Get _ | .structGet .. | .structSet .. => [.mayTrap]
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
  | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData ..
  | .arrayInitElem .. => [.mayTrap]
  | _ => []

/-- Whether the sequence at the reversed path `rp` lies inside a `try_table` body. -/
def inTryRev (body : Expr) : List SeqStep → Bool
  | [] => false
  | (m, _) :: rp =>
    (match lookup body ⟨rp.reverse, m⟩ with
      | some ⟨_, some (.tryTable ..)⟩ => true
      | _ => false) || inTryRev body rp

/-- Whether sequence `p` lies inside a `try_table` body. -/
def inTry (body : Expr) (p : List SeqStep) : Bool := inTryRev body p.reverse

/-- Whether a block may raise: it calls, or ends with `throw`/`throw_ref`. -/
def mayRaise (s : Segment) : Bool :=
  s.instrs.any (fun i => (instrEffects i).contains .call) ||
    match s.term with | some (.throw _) | some .throwRef => true | _ => false

/-- The effect marks of block `b` with segment `s`, without repetition. -/
def blockEffects (body : Expr) (b : BlockId) (s : Segment) : List Effect :=
  let es := s.instrs.flatMap instrEffects
  [Effect.mayTrap, .call].filter es.contains ++
    (if inTry body b.seq && mayRaise s then [.unresolvedHandler] else [])

/-- **The effect edges** of block `b`: to `trap` if it may trap or calls, to `raise` if it
calls. These are "may" edges, kept apart from `Edge`. -/
def effectSucc (body : Expr) (b : BlockId) (s : Segment) : List Target :=
  let es := blockEffects body b s
  (if es.contains .mayTrap || es.contains .call then [.trap] else []) ++
    (if es.contains .call then [.raise] else [])

/-- `t` is an effect successor of block `b`. -/
def EffectEdge (body : Expr) (b : BlockId) (t : Target) : Prop :=
  ∃ s, lookup body b = some s ∧ t ∈ effectSucc body b s

end Silmaril.Wasm.Cfg
