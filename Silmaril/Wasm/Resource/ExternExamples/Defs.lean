module

public import Silmaril.Wasm.Resource.Extern.Defs
public import Silmaril.Wasm.Verify.Reach.Defs

@[expose] public section

/-!
# Real `externref` clients for the reference handle sentence

Two real Core 3.0 modules with the same reference-typed handle imports

* `env.alloc : [] → [externref]` (import `0`, host code `0`),
* `env.use : [externref] → []` (import `1`, host code `1`),
* `env.free : [externref] → []` (import `2`, host code `2`),

and one export `run`, the function at store address `3`:

* `exUse`: `run : [externref] → []` is `local.get 0; call $use`. It uses a reference the
  environment passed but never allocated.
* `exAlloc`: `run : [] → [externref]` is `call $alloc`. It allocates and hands the handle back.
  It never reaches `use` or `free`.

Both untyped instances are `⟨Unit, fun _ => 3⟩` (`exUseU`, `exAllocU`): an untyped instance
records only export addresses, and in the untyped game **Opponent supplies the store** of every
export question and every answer. So `uClientSpec` alone cannot tell the two modules apart.
`exUse`'s bad play, with `exUse`'s store, is also a play of `exAllocU`.

The sentence for clients that sit in a known instance therefore assumes that the environment
keeps the instance. `Protocol.guardO ok π` sends an Opponent move violating `ok` to an absorbing
accepting state; this is the blame discipline of the handle protocols, applied to the stores and
references the environment hands over. `EnvKeeps S₀ G`, for a set `G` of function addresses,
says:

* every store the environment hands over agrees with the instantiated store `S₀` on the
  functions in `G` and holds only references to functions in `G` (`Keeps`, with silmaril-lean's
  `StoreIn` of `Silmaril.Wasm.Verify.Reach`);
* export arguments and answer results contain only references to functions in `G`.

`keptSpec S₀ G ha hu hf` is `uClientSpec ha hu hf` under this guard.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.ExternExamples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.UntypedExample Silmaril.Wasm.Verify
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-! ### The modules -/

/-- The types: `0 = [] → [externref]`, `1 = [externref] → []`. -/
def handleTypes : List RecType :=
  [⟨[⟨true, [], .func ⟨[], [externRef]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[externRef], []⟩⟩]⟩]

/-- The imports `env.alloc`, `env.use`, `env.free`. -/
def handleImports : List Import :=
  [⟨"env", "alloc", .func ⟨0⟩⟩, ⟨"env", "use", .func ⟨1⟩⟩, ⟨"env", "free", .func ⟨1⟩⟩]

/-- **The bad client**: `run : [externref] → []` is `local.get 0; call $use`. -/
def exUse : Module where
  types := handleTypes
  imports := handleImports
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- **The allocating client**: `run : [] → [externref]` is `call $alloc`. -/
def exAlloc : Module where
  types := handleTypes
  imports := handleImports
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- The validated type of a module. -/
def mtOf (m : Module) : CModuleType := (validate? m).getD ⟨[], []⟩

/-- The store providing the imports of a module: one host function per import, host code `j`
for import `j`. -/
def impStoreOf (m : Module) : Store Nat := importStore (CExternType.funcs (mtOf m).imports)

/-- The spec's allocation of a module against its imports. -/
def prepOf (m : Module) : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (impStoreOf m) m (importAddrs (mtOf m))).getD (⟨{}, {}, []⟩, none)

/-- The instantiated store of a module. -/
def storeOf (m : Module) : Store Nat := (prepOf m).1.store

/-- The instantiated store of `exUse`. -/
abbrev exUseS : Store Nat := storeOf exUse

/-- The instantiated store of `exAlloc`. -/
abbrev exAllocS : Store Nat := storeOf exAlloc

/-- The untyped instance of `exUse`: the export `run` at address `3`. -/
def exUseU : UInstance := ⟨Unit, fun _ => 3⟩

/-- The untyped instance of `exAlloc`: the export `run` at address `3`. -/
def exAllocU : UInstance := ⟨Unit, fun _ => 3⟩

/-- An opaque host reference, the handle the environment passes. -/
def hnd : Val := .ref (.extern (.host 7))

/-- The bad play of `exUse`: the environment calls `run hnd` in the instantiated store, and the
module calls `use hnd` without any allocation. -/
def badPlay : List (Move UImp (untypedSig Unit)) :=
  [.inr (.ask ⟨(), exUseS, [hnd]⟩), .inl (.ask ⟨1, exUseS, [hnd]⟩)]

/-- A play of `exAlloc`: the environment calls `run` in the instantiated store, and the module
calls `alloc`. -/
def allocPlay : List (Move UImp (untypedSig Unit)) :=
  [.inr (.ask ⟨(), exAllocS, []⟩), .inl (.ask ⟨0, exAllocS, []⟩)]

/-! ### Environments that keep the instance -/

/-- The store `s` agrees with `S₀` on the functions in `G` and holds only references into `G`. -/
def Keeps (S₀ : Store Nat) (G : Nat → Prop) (s : Store Nat) : Prop :=
  (∀ a, G a → s.funcs[a]? = S₀.funcs[a]?) ∧ StoreIn G s

/-- The environment keeps the instance `S₀` (functions `G`): the stores it hands over keep it,
and its export arguments and answer results contain only references into `G`. -/
def EnvKeeps {ι : Type} (S₀ : Store Nat) (G : Nat → Prop) : Move UImp (untypedSig ι) → Prop
  | .inr (.ask f) => Keeps S₀ G f.store ∧ ∀ r, Val.ref r ∈ f.args → RefIn G r
  | .inl (.ans _ a) => Keeps S₀ G a.store ∧ ∀ x ∈ codeRefs a.result.toAdmin, RefIn G x
  | _ => True

open Classical in
/-- **The guard**: an Opponent move violating `ok` is an environment fault, to the absorbing
state `none` (which accepts everything). -/
noncomputable def _root_.Silmaril.Wasm.Resource.Protocol.guardO {S : Type} {E F : Sig.{0}}
    (ok : Move E F → Prop) (π : Protocol S (Move E F)) : Protocol (Option S) (Move E F) where
  init := some π.init
  step
    | none, _ => some none
    | some q, m => if Move.IsO m ∧ ¬ ok m then some none else (π.step q m).map some

/-- **The client sentence for references, for an environment keeping the instance.** -/
noncomputable def keptSpec {ι : Type} (S₀ : Store Nat) (G : Nat → Prop) (ha hu hf : Nat) :
    Protocol (Option (Option (List Val))) (Move UImp (untypedSig ι)) :=
  (uClientSpec ha hu hf).guardO (EnvKeeps S₀ G)

/-- The functions `exAlloc` may reach: `alloc` (address `0`) and `run` (address `3`). -/
def allocG : List Nat := [0, 3]

/-- All functions of `exUse`. -/
def useG : List Nat := [0, 1, 2, 3]

end Silmaril.Wasm.Resource.ExternExamples
