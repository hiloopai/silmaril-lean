module

public import Silmaril.Compiler.Core.Verified.LoopTransfer.Defs
public import Silmaril.Compiler.Core.Verified.LocalsStmt.Defs

/-! # Saved loop bodies retain their right continuations

A save inside the left side of a sequence is collected with that sequence's
right side attached. `Context` represents exactly these wrappers, including
their patterns and annotations. Entering the wrapped body restores the
corresponding continuation stack without changing memory or the environment.
Unique semantic label keys turn syntactic membership into actual lookup.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopContext

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open SeqReach (Reaches)

/-- A hole in the left operand of nested strong or weak sequences. -/
inductive Context where
  | hole
  | strong (ann : List Annot) (pat : Pattern Sym) (right : EE) (inner : Context)
  | weak (ann : List Annot) (pat : Pattern Sym) (right : EE) (inner : Context)

def Context.fill : Context → EE → EE
  | .hole, e => e
  | .strong ann pat right c, e => .mk ann (.sseq pat (c.fill e) right)
  | .weak ann pat right c, e => .mk ann (.wseq pat (c.fill e) right)

/-- The frames at the hole, with every sequence's original environment. -/
def Context.frames : Context → Env → List Frame → List Frame
  | .hole, _, k => k
  | .strong _ pat right c, env, k => c.frames env (.strongBind pat right env :: k)
  | .weak _ pat right c, env, k => c.frames env (.effectBind pat right env :: k)

/-- Reentering a collected label body reinstalls all right continuations.
Sequence annotations do not focus the diagnostic location in the Core rules. -/
theorem Context.enter (c : Context) (e : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (file : Program) (labels : Labels) :
    Reaches file labels ⟨.effectExpr (c.fill e) env, k, m⟩
      ⟨.effectExpr e env, c.frames env k, m⟩ := by
  induction c generalizing k with
  | hole => exact .refl
  | strong ann pat right c ih =>
    exact (ReturnConst.sequence_reaches file labels ann pat _ right env k m).trans (ih _)
  | weak ann pat right c ih =>
    exact (Locals.wseq_reaches ann pat _ right env k m).trans (ih _)

/-- The procedure boundary selected at the hole is the original one. -/
theorem Context.procedureContext (c : Context) (env : Env) (k : List Frame) (labels : Labels) :
    procedureContext labels (c.frames env k) = procedureContext labels k := by
  induction c generalizing k with
  | hole => rfl
  | strong ann pat right c ih => exact ih _
  | weak ann pat right c ih => exact ih _

/-- Every label collected below the hole is wrapped in exactly this context. -/
theorem Context.saves_mem (c : Context) {e body : EE} {s : Sym} {params : List Sym}
    (hit : (s, params, body) ∈ saves e) :
    (s, params, c.fill body) ∈ saves (c.fill e) := by
  induction c with
  | hole => exact hit
  | strong ann pat right c ih =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | weak ann pat right c ih =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

/-- Lookup is unchanged by inserting bindings with other semantic keys. -/
theorem lookup_foldl_other {α : Type} (xs : List (Sym × α)) (s : Sym) (m : Map Sym α)
    (apart : ∀ x ∈ xs, x.1.key ≠ s.key) :
    (xs.foldl (fun acc b => acc.insert b.1 b.2) m).lookup s = m.lookup s := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih _ (by intro y hy; exact apart y (List.mem_cons_of_mem _ hy))]
    exact Map.lookup_insert_of_key_ne x.2 m (Ne.symm (apart x (by simp)))

/-- With unique semantic keys, membership suffices for lookup in a label map.
Without uniqueness the last binding wins, so that hypothesis is essential. -/
theorem lookup_ofList_unique {α : Type} (xs : List (Sym × α))
    (unique : (xs.map (fun x => x.1.key)).Nodup) {s : Sym} {v : α}
    (hit : (s, v) ∈ xs) : (Map.ofList xs).lookup s = some v := by
  have general (xs : List (Sym × α)) (m : Map Sym α)
      (unique : (xs.map (fun x => x.1.key)).Nodup) {s : Sym} {v : α}
      (hit : (s, v) ∈ xs) :
      (xs.foldl (fun acc b => acc.insert b.1 b.2) m).lookup s = some v := by
    induction xs generalizing m with
    | nil => cases hit
    | cons x xs ih =>
      obtain ⟨apart, tail⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp hit with eq | hit
      · subst x
        rw [List.foldl_cons, lookup_foldl_other]
        · exact Map.lookup_insert s v m
        · intro y hy eq
          exact apart (List.mem_map.mpr ⟨y, hy, eq⟩)
      · exact ih (m.insert x.1 x.2) tail hit
  exact general xs ∅ unique hit

/-- A save below a continuation context resolves to its wrapped body,
including when unrelated labels occur elsewhere in that syntax. -/
theorem Context.lookup_save (c : Context) (ann : List Annot) (label : Sym × BaseType)
    (params : List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE))) (body : EE)
    (unique : ((saves (c.fill (.mk ann (.save label params body)))).map
      (fun x => x.1.key)).Nodup) :
    (Map.ofList (saves (c.fill (.mk ann (.save label params body))))).lookup label.1 =
      some (params.map Prod.fst, c.fill body) := by
  apply lookup_ofList_unique _ unique
  exact c.saves_mem (by exact List.mem_cons_self)

/-- An annotated back edge carrying a local pointer reenters the collected
body, then restores its right continuations. Its slot invariant survives both
the diagnostic focus and rebinding the same allocation. -/
theorem backedge {file : Program} {labels localLabels : Labels}
    (c : Context) (body : EE) (ann pann : List Annot) (label x : Sym)
    {env : Env} {m : Mem.Concrete.State} {ls : List StateMem.Local}
    {ds : StateExpr.Key → Option IntExpr.Term} (inv : StateMem.Inv env m ls ds)
    {l : StateMem.Local} (hl : l ∈ ls) (key : x.key = l.sym.key)
    (k retained : List Frame)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup label = some ([x], c.fill body)) :
    let env' := extendEnv [(x, StateMem.ptr l)] env
    let m' := ReturnConst.focusMemory ann m
    StateMem.Inv env' m' ls ds ∧
      Reaches file labels
        ⟨.effectExpr (.mk ann (.run () label [.mk pann () (.sym x)])) env, k, m⟩
        ⟨.effectExpr body env', c.frames env' retained, m'⟩ := by
  dsimp only
  refine ⟨LoopTransfer.rebind (inv.focus ann) hl x key, ?_⟩
  have run := LoopTransfer.run_reaches (file := file) (labels := labels)
    ann label env (.mk pann () (.sym x)) [] (StateMem.ptr l) []
    (SeqReach.pure_symbol pann x env _ (inv.lookup hl key)) .nil k retained localLabels [x]
    (c.fill body) context lookup rfl m
  exact run.trans (c.enter body _ retained _ file labels)

end Silmaril.Compile.Core.Verified.LoopContext
