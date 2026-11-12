module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.All
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Upd

/-!
# Round 7, the whole-evaluator erasure: updates written only at the root (unrefined)

The bodies of `$with_tableinst` and `$with_meminst` update `$sof(z)[.TABLES[i] = ti]` and
`$sof(z)[.MEMS[i] = mi]`. Their paths fail `updOk`, but their only field write is at the root
(`rootOnly`). `step_updRoot`: such an update commutes with erasure and keeps the swap set whenever
the root it evaluates to is not a record with an `EXPORTS` field. For `$sof(z)` that holds when
`z` is a real state, whose store has no `EXPORTS` field; it fails when the "store" is a module
image (`Roots.not_allIn_QC_tables`), which is why the two definitions are left out of the checked
part and must be handled at `Step`'s call sites.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Roots (IsWrite)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env} {n : Nat}

/-- Every field step of the path is at the root: `.a`, `.a[e]`, `.a[e₁:e₂]`, … -/
def rootOnly : Path → Bool
  | .rootP => true
  | .idxP p _ => rootOnly p
  | .sliceP p _ _ => rootOnly p
  | .dotP .rootP _ => true
  | .dotP _ _ => false

theorem isWrite_rootOnly {q : Path} {a : AtomS} : ∀ {p : Path}, IsWrite q a p →
    rootOnly p = true → q = .rootP
  | .rootP, h, _ => by cases h
  | .idxP p e, h, hr => by
    cases h with
    | idx h => exact isWrite_rootOnly h (by simpa [rootOnly] using hr)
  | .sliceP p e₁ e₂, h, hr => by
    cases h with
    | slice h => exact isWrite_rootOnly h (by simpa [rootOnly] using hr)
  | .dotP p b, h, hr => by
    cases p
    case rootP =>
      cases h with
      | here => rfl
      | dot h' => cases h'
    all_goals simp [rootOnly] at hr

/-- **An update written only at a root without `EXPORTS`**, one step. -/
theorem step_updRoot (ih : EraseAt Q gr gd env n) {ρ : VarEnv} {e₁ e₂ : Exp} {p : Path}
    (hρ : SG Q gd ρ) (h₁ : xExp gr gd e₁ = true) (hp : xPath gr gd p = true)
    (hr : rootOnly p = true) (h₂ : xExp gr gd e₂ = true)
    (hroot : ∀ v₁, evalExp n env ρ e₁ = .ok v₁ → ∀ gs, v₁ = .struct gs → hasExp gs = false) :
    ER eraseV (AllIn Q) (evalExp (n + 1) env ρ (.updE e₁ p e₂))
      (evalExp (n + 1) env (eraseScope ρ) (.updE e₁ p e₂)) := by
  simp only [evalExp]
  refine ER.bind (ih.exp ρ e₁ hρ h₁) fun v₁ hv₁e hv₁ =>
    ER.bind (ih.exp ρ e₂ hρ h₂) fun v₂ _ hv₂ => ?_
  refine ⟨ih.pathSet ρ v₁ p v₂ hρ hp hv₁, fun u hu => ?_⟩
  refine allIn_pathSet_of hv₁ p n v₂ u hv₂ (fun q a hq m' gs hg he x _ => ?_) hu
  have hq0 := isWrite_rootOnly hq hr
  subst hq0
  rcases m' with _ | m'
  · simp [pathGet] at hg
  · simp only [pathGet, Except.ok.injEq] at hg
    rw [hroot v₁ hv₁e gs hg] at he
    cases he

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
