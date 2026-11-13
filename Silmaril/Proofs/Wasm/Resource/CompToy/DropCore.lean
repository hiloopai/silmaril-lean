module

public import Silmaril.Proofs.Wasm.Resource.CompToy.DropRun

/-!
# The toy resource component: the core function `drop` in the program logic

`drop` (core function `4`, body `local.get 0; call $drop`) under the import context in which
`res.drop` (core function `1`, the canon built-in `resource.drop`) is called on `i32 w` and
answers `[]`, keeping the core store:

* `dropSpec w`, `Γdrop w`, `Hdrop w`: that import specification, context and host relation;
* `dropFSpec c w`: from the toy's core store with counter `c` on `[i32 w]`, `drop` returns
  `[]` in the same store;
* **`dropSpec_valid`**: `drop` meets `dropFSpec c w` under `Hdrop w`.

New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable (P : Silmaril.Wasm.Numerics.Profile)

/-- `resource.drop` called on `i32 w`, answering `[]` and keeping the core store. -/
def dropSpec (w : BitVec 32) : FSpec (CanonHost (E3 P)) where
  pre _ args := args = [.i32 w]
  post s _ s' o := s' = s ∧ o = .normal []

/-- The import context of `drop`: only `resource.drop` (address `1`). -/
def Γdrop (w : BitVec 32) : Ctx (CanonHost (E3 P)) :=
  fun a => if a = 1 then some (dropSpec P w) else none

/-- The host relation of `drop`'s core phase. -/
abbrev Hdrop (w : BitVec 32) : HostSemantics (CanonHost (E3 P)) :=
  specHost (toyBind P) (Γdrop P w)

/-- **The specification of `drop`** (core function `4`): from the core store with counter `c`
on `[i32 w]`, it returns `[]` in the same store. -/
def dropFSpec (c : ℕ) (w : BitVec 32) : FSpec (CanonHost (E3 P)) where
  pre s args := s = toyCs P c ∧ args = [.i32 w]
  post _ _ s' o := s' = toyCs P c ∧ o = .normal []

theorem toyCore_drop_code : ((toyInst P).store.core.funcs[4]?).map FuncInst.code =
    some (.wasm ⟨⟨1⟩, [], [.localGet ⟨0⟩, .call ⟨1⟩]⟩) := by kernel_rfl

theorem toyCore_drop_type : ((toyInst P).store.core.funcs[4]?).map
    (fun fi => decide (Expand fi.type
      (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], []⟩))) = some true := by kernel_rfl

theorem toyCore_drop_module : ((toyInst P).store.core.funcs[4]?).map
    (fun fi => fi.module.funcs[1]?) = some (some 1) := by
  kernel_rfl

theorem toyCore_dropH_code : ((toyInst P).store.core.funcs[1]?).map FuncInst.code =
    some (.host (dropH P)) := by kernel_rfl

theorem toyCore_dropH_type : ((toyInst P).store.core.funcs[1]?).map
    (fun fi => decide (Expand fi.type
      (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], []⟩))) = some true := by
  kernel_rfl

variable {P}

/-- The call of `res.drop` in `drop`. -/
theorem drop_call {c : ℕ} {w : BitVec 32} {F f : Frame} {fi₁ : FuncInst (CanonHost (E3 P))}
    {vs₀ : List Execution.Core.Val} {k nr : ℕ} (hnr : nr = 0)
    (hx : F.module.funcs[1]? = some 1) (hf₁ : (toyInst P).store.core.funcs[1]? = some fi₁)
    (hcode : fi₁.code = .host (dropH P))
    (he : Expand fi₁.type (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], []⟩)) :
    HWP P (Hdrop P w) (toyCs P c) F (vals [.i32 w] ++ [.plain (.call ⟨1⟩)])
      (bodyPostK P (Hdrop P w) nr f vs₀
        (callPost f vs₀ ((dropFSpec P c w).post (toyCs P c) [.i32 w])) k)
  | 0 => trivial
  | n + 1 => by
    have hS : Γdrop P w (toyBind P (dropH P)) = some (dropSpec P w) := by
      rw [toyBind_drop]
      rfl
    have hpre : (stubSpec 1 (dropH P) (dropSpec P w)).pre (toyCs P c) [.i32 w] :=
      ⟨⟨fi₁, _, _, hf₁, hcode, he, rfl⟩, rfl⟩
    refine Safe.callIdx (vs₀ := []) hx hf₁ (FSpecAt.stub hS n) hpre fun s' o hc => ?_
    rcases hc with ⟨-, ⟨res, rfl, hs', hres⟩ | ⟨rfl, -, he'⟩ | ⟨a, rfl, -, he'⟩⟩
    · cases hres
      subst hs'
      exact Safe.of_exits (o := .normal []) rfl ⟨by simp [hnr], rfl, .inl ⟨_, rfl, rfl, rfl⟩⟩
    · cases he'
    · cases he'

/-- **`drop` meets its specification** under the import context of `resource.drop`. -/
theorem dropSpec_valid (c : ℕ) (w : BitVec 32) : FSpecValid P (Hdrop P w) 4 (dropFSpec P c w)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    have hcode := toyCore_drop_code P
    have ht := toyCore_drop_type P
    have hmod := toyCore_drop_module P
    have hc₁ := toyCore_dropH_code P
    have ht₁ := toyCore_dropH_type P
    cases hf : (toyInst P).store.core.funcs[4]? with
    | none => simp [hf] at hcode
    | some fi =>
    cases hf₁ : (toyInst P).store.core.funcs[1]? with
    | none => simp [hf₁] at hc₁
    | some fi₁ =>
      simp only [hf, Option.map_some, Option.some.injEq, decide_eq_true_eq] at hcode ht hmod
      simp only [hf₁, Option.map_some, Option.some.injEq, decide_eq_true_eq] at hc₁ ht₁
      refine FSpecAt.of_body (fi := fi) (fun s args h => by rw [h.1]; exact hf) hcode ht
        (fun s args h => by rw [h.2]; rfl) ?_
      rintro s args ⟨rfl, rfl⟩ f vs₀
      have hv : (Frame.forCall fi.module [.i32 w] []).local? ⟨0⟩ = some (some (.i32 w)) := rfl
      exact Wp.localGet (m := .part) (us := []) (rest := [.plain (.call ⟨1⟩)]) hv
        (drop_call (F := Frame.forCall fi.module [.i32 w] []) (by rfl) hmod hf₁ hc₁ ht₁) n

end Silmaril.Wasm.Resource.CompToy
