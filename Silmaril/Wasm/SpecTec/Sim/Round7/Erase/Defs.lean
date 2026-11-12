module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Defs

/-!
# Round 7, the export swap: the evaluator layer, first-order fragment (round 3, pass 1)

Item 1 of the plan for `Round7.Swap.Task.stepErase` relates evaluation at a scope `ρ` with
evaluation at the erased scope `eraseScope ρ`, on scopes in the swap set (`ScopeIn Q ρ`). This
header names the scope operations and a first fragment of the syntax:

* `eraseScope ρ`: `ρ` with `Round7.Swap.eraseV` applied to every term binding.
* `ScopeIn Q ρ`: every term binding of `ρ` is `AllIn Q`.
* `EOK Q r r'`: `r'` is `r` with its answer erased, and that answer is `AllIn Q`.
* `FO e` (with `FOs`, `FOf`): `e` is first order: no definition call, iteration, record update or
  extension, or composition, and no atom `EXPORTS`. These are the forms whose evaluation calls no
  other member of the evaluator block than `evalExp`, `evalExps` and `evalExpFields`.
* `FOp p`: a path whose index and slice bounds are first order and with no step `.EXPORTS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Erase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV AllIn)

/-- **The erased scope**: `eraseV` on every term binding. -/
def eraseScope (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.map fun p => (p.1, eraseV p.2) }

/-- **The scope is in the swap set**: every term binding is `AllIn Q`. -/
def ScopeIn (Q : Value → Prop) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.vals, AllIn Q p.2

/-- `r'` is `r` with its answer erased, and every answer of `r` is `AllIn Q`. -/
def EOK (Q : Value → Prop) (r r' : Res Value) : Prop :=
  r' = eraseV <$> r ∧ ∀ v, r = .ok v → AllIn Q v

mutual
/-- **First-order expressions**: no call, iteration, update, extension or composition, and no
atom `EXPORTS`. -/
inductive FO : Exp → Prop where
  | varE (x : IL.Id) : FO (.varE x)
  | boolE (b : Bool) : FO (.boolE b)
  | numE (m : Num) : FO (.numE m)
  | textE (t : Text) : FO (.textE t)
  | unE {op : UnOp} {t : OpTyp} {e : Exp} : FO e → FO (.unE op t e)
  | binE {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.binE op t e₁ e₂)
  | cmpE {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.cmpE op t e₁ e₂)
  | tupE {es : List Exp} : FOs es → FO (.tupE es)
  | projE {e : Exp} {i : Int} : FO e → FO (.projE e i)
  | caseE {op : MixopS} {e : Exp} : FO e → FO (.caseE op e)
  | uncaseE {e : Exp} {op : MixopS} : FO e → FO (.uncaseE e op)
  | optNone : FO (.optE none)
  | optSome {e : Exp} : FO e → FO (.optE (some e))
  | theE {e : Exp} : FO e → FO (.theE e)
  | strE {fs : List ExpField} : FOf fs → FO (.strE fs)
  | dotE {e : Exp} {a : AtomS} : a ≠ "EXPORTS" → FO e → FO (.dotE e a)
  | listE {es : List Exp} : FOs es → FO (.listE es)
  | liftE {e : Exp} : FO e → FO (.liftE e)
  | memE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.memE e₁ e₂)
  | lenE {e : Exp} : FO e → FO (.lenE e)
  | catE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.catE e₁ e₂)
  | idxE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.idxE e₁ e₂)
  | sliceE {e₁ e₂ e₃ : Exp} : FO e₁ → FO e₂ → FO e₃ → FO (.sliceE e₁ e₂ e₃)
  | cvtE {e : Exp} {t₁ t₂ : NumTyp} : FO e → FO (.cvtE e t₁ t₂)
  | subE {e : Exp} {t₁ t₂ : Typ} : FO e → FO (.subE e t₁ t₂)

/-- `FO` on a list. -/
inductive FOs : List Exp → Prop where
  | nil : FOs []
  | cons {e : Exp} {es : List Exp} : FO e → FOs es → FOs (e :: es)

/-- `FO` on record fields, none named `EXPORTS`. -/
inductive FOf : List ExpField → Prop where
  | nil : FOf []
  | cons {a : AtomS} {e : Exp} {fs : List ExpField} : a ≠ "EXPORTS" → FO e → FOf fs →
      FOf (.mk a e :: fs)
end

/-- **First-order paths**: index and slice bounds are first order and no step is `.EXPORTS`. -/
inductive FOp : Path → Prop where
  | rootP : FOp .rootP
  | idxP {p : Path} {e : Exp} : FOp p → FO e → FOp (.idxP p e)
  | sliceP {p : Path} {e₁ e₂ : Exp} : FOp p → FO e₁ → FO e₂ → FOp (.sliceP p e₁ e₂)
  | dotP {p : Path} {a : AtomS} : FOp p → a ≠ "EXPORTS" → FOp (.dotP p a)

end Silmaril.Wasm.SpecTec.Sim.Round7.Erase
