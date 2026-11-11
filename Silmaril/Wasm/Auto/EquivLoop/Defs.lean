module

public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# Loop equivalence under a state invariant: definitions

`CEquiv.loop`/`CEquiv.loopT` (`Silmaril.Wasm.Auto.Equiv`, `Silmaril.Wasm.Auto.EquivLoop.Thms`)
relate loops whose bodies are equivalent on frames with typed locals. Bodies that read and write
**globals and memory** are only equivalent in stores where those exist and are typed
(`SegEquivX`'s `XCtx.Ok`). This module parameterises the loop congruence by an invariant on the
store and the frame:

* `SInv`: an invariant of stores and frames (for every host type);
* `BodyEquivI I a b`: `a` and `b` have the same weakest precondition (both readings, every
  profile, host relation and postcondition) from every state satisfying `I`, on an empty stack;
* `InvBr0 I Q`, `KeepsBr0I I a`: every branch of `a` to the label right around it (a loop's back
  edge) reaches a state satisfying `I`;
* `LoopEquivI I bt a b`: the loops `loop bt a` and `loop bt b` have the same weakest
  precondition from every state satisfying `I`, with any values below (not ending in a function
  reference) and any code after;
* `XInv lt gt mem`: the invariant of the extended checker: some typed context
  (`XCtx.Ok lt [] gt mem`) has this store and frame;
* `brIfBodyOkX lt gt mem c`: a decidable check that `c` runs symbolically from such a context,
  keeps the types of the locals and globals, and leaves an `i32` on top (so `c ++ [br_if l]`
  keeps `XInv` at its back edges).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivLoop

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (NoFuncTop)
open Silmaril.Wasm.Auto.Equiv

/-- An invariant of stores and frames, for every host type. -/
abbrev SInv := ∀ {H : Type}, Store H → Frame → Prop

/-- **Body equivalence under an invariant.** -/
def BodyEquivI (I : SInv) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (Q : Post H), I s f → (Wp m P host s f (expression a) Q ↔ Wp m P host s f (expression b) Q)

/-- The postcondition `Q`, and every branch to the innermost label reaches a state of `I`. -/
def InvBr0 (I : SInv) {H : Type} (Q : Post H) : Post H := fun s F o =>
  Q s F o ∧ ∀ vs, o = .br 0 vs → I s F

/-- **The invariant at loop back edges.** -/
def KeepsBr0I (I : SInv) (a : List Instr) : Prop :=
  ∀ (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame) (Q : Post H),
    I s f → HWP P host s f (expression a) Q → HWP P host s f (expression a) (InvBr0 I Q)

/-- **Loop equivalence under an invariant.** -/
def LoopEquivI (I : SInv) (bt : BlockType) (a b : List Instr) : Prop :=
  ∀ (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) (Q : Post H), I s f → NoFuncTop us →
    (Wp m P host s f (vals us ++ [.plain (.loop bt a)] ++ rest) Q ↔
      Wp m P host s f (vals us ++ [.plain (.loop bt b)] ++ rest) Q)

/-- The invariant of the extended checker: a typed context with this store and frame. -/
def XInv (lt gt : List IntType) (mem : Bool) : SInv := fun {H} s f =>
  ∃ c : XCtx H, c.Ok lt [] gt mem ∧ c.s = s ∧ c.f = f

/-- A `do … while` body `c ++ [br_if l]` whose straight-line part runs symbolically, keeps the
types of the locals and globals and leaves an `i32` on top. -/
def brIfBodyOkX (lt gt : List IntType) (mem : Bool) (c : List Instr) : Bool :=
  match xsexec mem (initX lt [] gt) c with
  | some A => decide (A.locals.map Prod.fst = lt) && decide (A.globs.map Prod.fst = gt) &&
      decide ((A.stack.map Prod.fst).head? = some .i32)
  | none => false

/-! ## Notions of the soundness statements -/

section
variable {H : Type}

/-- One step back: `d` is a successor of `c`. -/
def StepBack (P : Profile) (host : HostSemantics H) (d c : Config H) : Prop := Step P host c d

/-- The inputs given by the values of slots. -/
def envOfSlots (ρ : Env) (B0 : ByteArray) (l : List (IntType × XT)) : Env := fun t n =>
  match l[n]? with
  | some p => if h : p.1 = t then h ▸ evX ρ B0 p.1 p.2 else 0
  | none => 0

/-- The context of the state after a symbolic run. -/
def _root_.Silmaril.Wasm.Auto.Equiv.XCtx.rebase (c : XCtx H) (mem : Bool) (A : XState) : XCtx H where
  s := c.storeOf mem A
  f := c.frameOf A
  ρ := envOfSlots c.ρ c.mi.bytes (A.locals ++ A.globs)
  ga := c.ga
  ma := c.ma
  mi := { c.mi with bytes := evM c.ρ c.mi.bytes A.mem }

end

end Silmaril.Wasm.Auto.EquivLoop
