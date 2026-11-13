module

public import Silmaril.Wasm.Resource.Client.Defs
public import Silmaril.Wasm.Resource.ExternExamples.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs

@[expose] public section

/-!
# A typestate checker for `externref` clients in the untyped game

The client verifier of `Silmaril.Wasm.Resource.Client` (abstract interpretation `okL`, handles in
locals, `Fact.loc`) run on the untyped game of `Silmaril.Wasm.Game.Untyped`, where handles are raw
`Val`s (`externref` included) and **Opponent supplies the store** with every export call and every
answer.

## The environment guard

`keptSpec S₀ G` (`Silmaril.Wasm.Resource.ExternExamples`) blames the environment for stores that
change the functions of `G` or hold references outside `G`. It does not blame an answer of the
wrong arity, and in the untyped game nothing else does: an answer `values [h₁, h₂]` to `alloc` is
not an allocation (`HEv.allocOfResult`), yet the module's `local.set` takes `h₂` and a later
`use h₂` is a protocol violation. So no module that allocates and then uses satisfies `keptSpec`
(`Silmaril.Wasm.Resource.ExternClientExamples`: `exAUF_refuted_kept`). `keptSpecA` adds the arity
of Core's host contract (`UReply.OkFor`) for the allocator: an answer `values ws` to `alloc` has
one value (`AllocArity`). It is a weaker sentence than `keptSpec`.

## References to the imports

The guard set `G` must contain the host functions of `use` and `free`: a store changing them
would let other code run in their place. So the environment may pass references to them, as
values. The analysis tells values from call targets: `Tight R` says that every call
instruction of administrative code (`callRefType`, `returnCallRefType`) sits right after the
value prefix of its sequence, and the reference it consumes names a function of `R` (the
reachable functions, avoiding the three imports). Dynamic calls (`call_ref`, `call_indirect`,
`return_call_ref`, `return_call_indirect`) are rejected (`noDynI`), so a reference value never
becomes a call target.

## The checker

`checkU S₀ fs addrs ia iu if_` on the instantiated store `S₀`: the reachable non-import
functions `reachU` (closure from the exports) pass the client check `funcOkC` with no handle
pairs (handles live in locals) and have no dynamic call; they contain the exports and avoid
the three imports; the host functions of the imports have the arities `[] → …`, `[h] → …`. The
guard set is `guardU`: `reachU` and the host functions of the three imports.

## Whole modules

`checkModU m` runs the checker on a whole module: its imports are the handle imports
`env.alloc`, `env.use`, `env.free` (`handleImports`, host codes `0`, `1`, `2` in the spec's
allocation `prepOf`), the store is its instantiated store `storeOf m`, the functions are all
function addresses of that store, and the roots are the function exports of the instance
(`modAddrsU m`). The untyped instance of a module is `modU m`: one export per function export of
the instance, at its address.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Resource.Client Silmaril.Wasm.Resource.ExternExamples
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Verify (RefIn closure rootsB avoidsB isHost)

/-! ## Source code without dynamic calls -/

mutual

/-- The instruction (nested bodies included) has no `call_ref`, `call_indirect`,
`return_call_ref` or `return_call_indirect`. -/
def noDynI : Instr → Bool
  | .callRef _ => false
  | .callIndirect _ _ => false
  | .returnCallRef _ => false
  | .returnCallIndirect _ _ => false
  | .block _ b => noDynL b
  | .loop _ b => noDynL b
  | .tryTable _ _ b => noDynL b
  | .if_ _ b₁ b₂ => noDynL b₁ && noDynL b₂
  | _ => true

/-- The sequence has no dynamic call. -/
def noDynL : List Instr → Bool
  | [] => true
  | i :: is => noDynI i && noDynL is

end

/-! ## Call targets of administrative code -/

/-- **Call targets in `T`.** `Tight T pr p l`: `pr` says that only values precede, in the
sequence, the rest `l`, and `p` that the last of them is a reference into `T`. A call
instruction needs both, every source instruction has no dynamic call, and nested bodies start
afresh. -/
def Tight (T : Nat → Prop) : Bool → Prop → List Admin → Prop
  | _, _, [] => True
  | pr, _, .ref r :: l => Tight T pr (RefIn T r) l
  | pr, p, .callRefType _ :: l => pr = true ∧ p ∧ Tight T false False l
  | pr, p, .returnCallRefType _ :: l => pr = true ∧ p ∧ Tight T false False l
  | pr, _, .plain i :: l =>
    noDynI i = true ∧ Tight T (pr && (Admin.plain i).val?.isSome) False l
  | _, _, .trap :: l => Tight T false False l
  | _, _, .label _ k b :: l => noDynL k = true ∧ Tight T true False b ∧ Tight T false False l
  | _, _, .handler _ _ b :: l => Tight T true False b ∧ Tight T false False l
  | _, _, .frame _ _ b :: l => Tight T true False b ∧ Tight T false False l

/-! ## The sentence -/

/-- Answers to the allocator have one value when they are values (Core's host contract for
`[] → [h]`). -/
def AllocArity {ι : Type} (ha : Nat) : Move UImp (untypedSig ι) → Prop
  | .inl (.ans e a) => e.target = ha → ∀ ws, a.result = .values ws → ws.length = 1
  | _ => True

/-- **The client sentence for references, for an environment keeping the instance and answering
the allocator with one value.** -/
noncomputable def keptSpecA {ι : Type} (S₀ : Store Nat) (G : Nat → Prop) (ha hu hf : Nat) :
    Protocol (Option (Option (List Val))) (Move UImp (untypedSig ι)) :=
  (uClientSpec ha hu hf).guardO (fun m => EnvKeeps S₀ G m ∧ AllocArity ha m)

/-! ## The checker -/

/-- The configuration of the analysis: no handle pairs. -/
def cfgU (S₀ : Store Nat) (fs : List Nat) (ia iu if_ : Nat) : Cfg :=
  cfgOf S₀ fs ia iu if_ []

/-- The reachable functions other than the three imports. -/
def reachU (S₀ : Store Nat) (fs addrs : List Nat) (ia iu if_ : Nat) : List Nat :=
  (closure S₀ fs addrs).filter fun a => !isBadC S₀ ia iu if_ a

/-- The host functions of the three imports. -/
def badU (S₀ : Store Nat) (ia iu if_ : Nat) : List Nat :=
  (List.range S₀.funcs.length).filter (isBadC S₀ ia iu if_)

/-- **The guard set**: the reachable functions and the host functions of the imports. -/
def guardU (S₀ : Store Nat) (fs addrs : List Nat) (ia iu if_ : Nat) : List Nat :=
  reachU S₀ fs addrs ia iu if_ ++ badU S₀ ia iu if_

/-- The function at address `a` passes the client check and has no dynamic call. -/
def funcOkU (S₀ : Store Nat) (fs R : List Nat) (ia iu if_ : Nat) (a : Nat) : Bool :=
  funcOkC S₀ fs R ia iu if_ [] a && match S₀.funcs[a]? with
    | some fi => match fi.code with
      | .wasm code => noDynL code.body
      | .host _ => true
    | none => true

/-- The host function at `a` of one of the imports has the arity of its import. -/
def hostTyB (S₀ : Store Nat) (ia iu if_ a : Nat) : Bool :=
  match S₀.funcs[a]? with
  | some fi => match fi.type.expand? with
    | some (.func ps _) =>
      (!isHost S₀ ia a || ps.length == 0) && (!(isHost S₀ iu a || isHost S₀ if_ a) || ps.length == 1)
    | _ => false
  | none => false

/-- **The `externref` client check** on an instantiated store. -/
def checkU (S₀ : Store Nat) (fs addrs : List Nat) (ia iu if_ : Nat) : Bool :=
  let R := reachU S₀ fs addrs ia iu if_
  ia != iu && ia != if_ && iu != if_ && R.all (funcOkU S₀ fs R ia iu if_) && rootsB R addrs &&
    avoidsB S₀ R ia && avoidsB S₀ R iu && avoidsB S₀ R if_ &&
    (badU S₀ ia iu if_).all (hostTyB S₀ ia iu if_)

/-! ## Whole modules -/

/-- The function addresses of the function exports of a module's instance, in export order. -/
def modAddrsU (m : Module) : List Nat := exportFuncAddrs (prepOf m).1.frame.module

/-- **The untyped instance of a module**: its function exports, at their addresses. -/
def modU (m : Module) : UInstance := ⟨Fin (modAddrsU m).length, fun j => (modAddrsU m)[j]⟩

/-- All function addresses of a module's instantiated store. -/
def modFuncsU (m : Module) : List Nat := List.range (storeOf m).funcs.length

/-- The guard set of a module: `guardU` on its instantiated store, all its functions and its
export roots, for the host codes `0`, `1`, `2` of `alloc`, `use`, `free`. -/
def modGuardU (m : Module) : List Nat := guardU (storeOf m) (modFuncsU m) (modAddrsU m) 0 1 2

/-- **The `externref` client check on a whole module**: the imports are `env.alloc`, `env.use`,
`env.free`, and `checkU` passes on the instantiated store with all functions and the export
roots. -/
def checkModU (m : Module) : Bool :=
  m.imports == handleImports && checkU (storeOf m) (modFuncsU m) (modAddrsU m) 0 1 2

end Silmaril.Wasm.Resource.ExternClient
