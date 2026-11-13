module

public import Silmaril.Wasm.Models.FunCloGame.Defs
public import Silmaril.Wasm.Models.FunRefCloCompile.Defs

/-!
# FunRefClo observed at first-order function type: closures that share cells

The closure game of FunClo (`Silmaril.Wasm.Models.FunCloGame`) for FunRefClo, FunClo with ML
references. A closure may capture cells, so its answers depend on the calls made before: the
game observes state that the ground reading (`funRefCloModel`, one call of `main`) cannot.

* `Ty.FO`, `Prog.GOk` (in `FunRefClo`): first-order result types (`int`, `bool`,
  `arr int τ`), and the programs the game reading accepts.
* The signature, plays and Wasm-side answers are FunCloGame's: `Op` (`main n`, `call h m`),
  `Ans` (`fn`, `word w`), `cloSig`, `toPlay`, `readAns`, `wpush`, `invokeOf`, `Returns`, `WRun`.
* `SrcStep`, `SrcRun`, `srcStrat p`: the **source strategy**. A source run threads the heap
  through the questions: every question runs from the heap the previous one left, so cells
  captured by closures persist between calls (a `main n` question cannot reach older cells, but
  it allocates after them).
* `mainRFunc p`, `mainRInst p`, `storeG p`: the harness, as for FunClo: `storeOf p` with `mainR`
  (the program's code returning the reference to its result) at address `2`, sharing `apply`'s
  type and module instance.
* `wasmStrat P host p`: the **compiled strategy**: FunCloGame's Wasm runs from `storeG p`.

`Thms.wasmStrat_eq`: for every program that `Prog.GOk` accepts, at every profile and host,
`wasmStrat P host p = srcStrat p`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefClo

/-- **First-order types**: ground types, and functions from `int` to a first-order type. -/
def Ty.FO : Ty → Prop
  | .int | .bool => True
  | .arr .int τ => Ty.FO τ
  | _ => False

/-- A program the game reading accepts: its body has a first-order type in `[int]`, and it is
within the compiler's limits. -/
def Prog.GOk (p : Prog) : Prop := HasTy [.int] p.body p.res ∧ p.res.FO ∧ p.Fits

end Silmaril.Wasm.Models.FunRefClo

namespace Silmaril.Wasm.Models.FunRefCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Games
open Silmaril.Wasm.Models.FunRefClo (Tm Ty Prog Heap HasTy eval obsWord)
open Silmaril.Wasm.Models.FunRefCloCompile (compile instOf mainInst applyInst)
open Silmaril.Wasm.Models.FunCloCompile (dApply)
open Silmaril.Wasm.Models.FunCompile (anyref)
open Silmaril.Wasm.Models.FunCloGame (Op Ans cloSig toPlay WRun)

/-! ## The source strategy -/

/-- The answer of a source value. -/
def ansOf : FunRefClo.Val → Ans
  | .clo _ _ => .fn
  | v => .word (obsWord v)

/-- The handles after answering with `v`: a closure gets the next handle. -/
def push (H : List FunRefClo.Val) : FunRefClo.Val → List FunRefClo.Val
  | .clo b ρ => H ++ [.clo b ρ]
  | _ => H

/-- **One source step** from the heap `σ` with the handles `H`: the value and the final heap. -/
def SrcStep (p : Prog) (σ : Heap) (H : List FunRefClo.Val) : Op → FunRefClo.Val → Heap → Prop
  | .main n, v, σ' => ∃ k, eval k σ [.int n] p.body = some (v, σ')
  | .call h m, v, σ' => ∃ b ρ k, H[h]? = some (.clo b ρ) ∧
      eval k σ (.int m :: .clo b ρ :: ρ) b = some (v, σ')

/-- **Source runs** from the heap `σ` and the handles `H`. -/
inductive SrcRun (p : Prog) : Heap → List FunRefClo.Val → List (Op × Ans) → Prop
  | nil (σ : Heap) (H : List FunRefClo.Val) : SrcRun p σ H []
  | cons {σ σ' : Heap} {H : List FunRefClo.Val} {o : Op} {v : FunRefClo.Val}
      {t : List (Op × Ans)} :
      SrcStep p σ H o v σ' → SrcRun p σ' (push H v) t → SrcRun p σ H ((o, ansOf v) :: t)

/-- The plays of the source runs from the empty heap and no handles. -/
def srcPlays (p : Prog) : Set (List (Move Sig.empty cloSig)) :=
  {s | ∃ t, SrcRun p [] [] t ∧ s = toPlay t}

/-- **The source strategy** of a program. -/
def srcStrat (p : Prog) : Strategy Sig.empty cloSig := Strategy.generate (srcPlays p)

/-! ## The harness and the compiled strategy -/

/-- **The harness function** `mainR` (type index `3`, `apply`'s type): the program's code at depth
`1` on the second parameter, returning the reference to the result. -/
def mainRFunc (p : Prog) : Func :=
  ⟨⟨3⟩, List.replicate p.body.depth anyref, compile p.table 1 p.body⟩

/-- The function instance of `mainR`, in the module instance of the compiled module. -/
def mainRInst (p : Prog) : FuncInst Nat := ⟨dApply, instOf, .wasm (mainRFunc p)⟩

/-- **The store of the game**: `storeOf p` with `mainR` at address `2`. -/
def storeG (p : Prog) : Store Nat := { funcs := [mainInst p, applyInst p, mainRInst p] }

/-- The plays of the Wasm runs from `storeG p` with no handles. -/
def wasmPlays (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) :
    Set (List (Move Sig.empty cloSig)) :=
  {s | ∃ t, WRun P host (storeG p) [] t ∧ s = toPlay t}

/-- **The compiled strategy** of a program. -/
def wasmStrat (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) :
    Strategy Sig.empty cloSig :=
  Strategy.generate (wasmPlays P host p)

end Silmaril.Wasm.Models.FunRefCloGame
