module

public import Silmaril.Wasm.Component.Algebra.Ops.Defs
public import Silmaril.Wasm.Component.Streams.Proc.Defs

/-!
# Stream pipelines in the component algebra

Stream transformers as components of the component IR (`Silmaril.Wasm.Component`), so that the
pipeline laws can be stated with the component algebra (`Silmaril.Wasm.Component.Algebra`:
`CompEquiv`, plugging `seq`, `seq_congr`, `denU_seq`, `seq_assoc`).

* `TCode`: transformer codes (`map`, `filter`, `take`, `id`, `lines`, `rechunk`, composition), the
  core modules of stage components; `TCode.tr` gives the transformer of the specification
  (`Silmaril.Wasm.Component.Streams.Spec`), `TCode.run` its whole output.
* `stage a`: the component with one import `src` and one export `src` whose core module is `a`;
  `pipe [a₁, …, aₖ]`: the stages plugged in order (`seq`), `aₖ` outermost.
* `batchSem`: the **batch semantics** of the codes: a stage's core instance, when called, pulls
  its whole input stream with one call of its import and answers `a.run` of it. This is the
  synchronous component IR's view of a stream (the IR has no async built-ins; the concurrent view
  is `Silmaril.Wasm.Component.Streams.Pipes`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Alg

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams
open scoped Silmaril.Wasm.Component.Streams.Tr

/-- Transformer codes. -/
inductive TCode where
  | id
  | map (f : Val → Val)
  | filter (p : Val → Bool)
  | take (n : Nat)
  | lines (sep : Val → Bool)
  | rechunk (n : Nat)
  | comp (a b : TCode)

/-- The whole output of a code: `run` of its transformer. -/
def TCode.run : TCode → List Val → List Val
  | .id => (Tr.id : Tr Unit Val Val).run
  | .map f => (Tr.map f).run
  | .filter p => (Tr.filter p).run
  | .take n => (Tr.take n : Tr Nat Val Val).run
  | .lines sep => (Proc.linesV sep).run
  | .rechunk n => (Proc.rechunkV n).run
  | .comp a b => fun xs => b.run (a.run xs)

/-- The function type of `src` (the batch view: the stream as one list value). -/
def ftS : FuncTy := ⟨[], []⟩

/-- Every code is a core module with one import and one export. -/
instance : CoreModule TCode := ⟨fun _ => [("src", ⟨[], []⟩)], fun _ => [("src", ⟨[], []⟩)]⟩

/-- **A stage component**: imports `src`, exports `src`, its core module is `a`. -/
def stage (a : TCode) : Comp TCode :=
  .mk [("src", ftS)] [.core a [Impl.fwd 0]] [⟨"src", ftS, Impl.fwd 1⟩]

/-- **A pipeline**: the stages plugged in order. -/
def pipe : List TCode → Comp TCode
  | [] => ident [("src", ftS)]
  | [a] => stage a
  | a :: as => seq (stage a) (pipe as)

/-- The answer of a stage to a pull: `f` of the whole input. -/
def pullAns (f : List Val → List Val) : Option Payload → Option Payload
  | some (.vals xs) => some (.vals (f xs))
  | _ => none

/-- **The batch semantics**: pull the whole input with one call of the import, answer `run`. -/
def batchSem : CoreSem TCode where
  sem a := Strategy.ofHandler fun _ =>
    .call ((⟨0, by decide⟩ : Fin 1), Payload.vals []) fun r => .pure (pullAns a.run r)

/-- The fused code of a nonempty pipeline (the stages composed in order); `[]` gives `id`. -/
def fuse : List TCode → TCode
  | [] => .id
  | [a] => a
  | a :: as => .comp a (fuse as)

end Silmaril.Wasm.Component.Streams.Alg
