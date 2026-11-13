module

public import Silmaril.Wasm.Models.FunRefCloGame.Defs
public import Silmaril.Wasm.Models.FunRefCloDiv.Thms
public import Silmaril.Wasm.Models.FunCloGame.Thms

/-!
# The closure game of FunRefClo: the harness

* `frameR`, `frameR_ok`, `env_frameR`: the frame of `mainR` on `n`; the argument is the
  environment at depth `1`.
* `mainRSpec`, `mainR_tspec`: `mainR` on `n` from a store representing the heap `σ` returns a
  representation of the program's value in an extended store representing the final heap (from
  FunRefCloCompile's `spec_all`).
* `mainR_div`: `mainR` never returns on an argument on which the program diverges from `σ` (from
  FunRefCloDiv's `div_all`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Models.FunRefCloGame
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap Ty HasTy ValTy EnvTy HeapTy)
open Silmaril.Wasm.Models.FunCompile (lx anyref dBox dMain)
open Silmaril.Wasm.Models.FunCloCompile (dApply)
open Silmaril.Wasm.Models.FunRefCompile (dCell)
open Silmaril.Proofs.Wasm.Models.FunCompile (bodyPostT_normal)
open Silmaril.Proofs.Wasm.Models.FunRefCloCompile (Rep Ext FOK EnvRep HeapRep spec_all)
open Silmaril.Proofs.Wasm.Models.FunRefCloDiv (div_all SDiv Typed)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## The frame of `mainR` -/

/-- The frame of `mainR` on `n`. -/
def frameR (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instOf [.ref (.i31 0), .ref (.i31 n)] (mainRFunc p).locals

theorem frameR_len (p : Prog) (n : BitVec 31) :
    (frameR p n).locals.length = p.body.depth + 2 := by
  simp [frameR, Frame.forCall, mainRFunc]

theorem frameR_ok (hfit : p.Fits) (n : BitVec 31) : FOK (frameR p n) :=
  ⟨⟨⟨[dMain, dCell, dApply], rfl⟩, by rw [frameR_len]; exact Nat.le_of_lt hfit.1⟩, rfl, rfl⟩

/-- The argument is the environment `[int n]` at depth `1`. -/
theorem env_frameR (μ : List Nat) (s : Store Nat) (n : BitVec 31) :
    EnvRep p.table μ s (frameR p n) 1 [.int n] := by
  refine ⟨rfl, fun i u hi => ?_⟩
  have hi0 : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  subst hi0
  have hu : u = .int n := by simpa using hi.symm
  subst hu
  exact ⟨_, by simp [frameR, Frame.forCall], rfl⟩

theorem mainR_code (p : Prog) :
    vals [] ++ (expression (compile p.table 1 p.body) ++ []) = expression (mainRFunc p).body := by
  simp [mainRFunc, vals]

/-! ## `mainR` on a terminating program -/

/-- The precondition of `mainR` on `n` from the heap `σ` (cells `μ`). -/
def mainRPre (p : Prog) (n : BitVec 31) (σ : Heap) (μ : List Nat) (s : Store Nat)
    (args : List Val) : Prop :=
  s.funcs[2]? = some (mainRInst p) ∧ s.funcs[1]? = some (applyInst p) ∧
    HeapRep p.table μ s σ ∧ args = [.ref (.i31 0), .ref (.i31 n)]

/-- The specification of `mainR` on `n` from the heap `σ` (cells `μ`), for a program returning
`v` in the heap `σ'`. -/
def mainRSpec (p : Prog) (n : BitVec 31) (σ : Heap) (μ : List Nat) (v : FunRefClo.Val)
    (σ' : Heap) : FSpec Nat :=
  ⟨mainRPre p n σ μ,
    fun s _ s' o => ∃ w μ', o = .normal [w] ∧ Ext s s' ∧ μ <+: μ' ∧ HeapRep p.table μ' s' σ' ∧
      Rep p.table μ' s' v w⟩

/-- **`mainR` is totally correct**: it returns a representation of the program's value. -/
theorem mainR_tspec (hfit : p.Fits) {n : BitVec 31} {k : Nat} {σ σ' : Heap}
    {v : FunRefClo.Val} (hv : eval k σ [.int n] p.body = some (v, σ')) (μ : List Nat) :
    TFSpecAt P host 2 (mainRSpec p n σ μ v σ') := by
  refine TFSpecAt.of_body (fi := mainRInst p) (code := mainRFunc p) (fun _ _ h => h.1) rfl
    ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, -, -, rfl⟩
    rfl
  · rintro s args ⟨-, hfn, hh, rfl⟩ f vs₀
    have h' := spec_all (P := P) (host := host) hfit k 1 p.body σ [.int n] v σ' hv μ s
      (frameR p n) (frameR_ok hfit n) hfn (by rw [frameR_len]; omega) (env_frameR μ s n) hh
      (fun _ hx => hx) [] []
      (bodyPostT P host 1 f vs₀ (callPost f vs₀ ((mainRSpec p n σ μ v σ').post s
        [.ref (.i31 0), .ref (.i31 n)])))
      fun μ' s' F' w hμ hs _ hh' hw => by
        simpa using Wp.of_vals (m := .total) (vs := [w])
          (bodyPostT_normal (P := P) (host := host) rfl ⟨w, μ', rfl, hs, hμ, hh', hw⟩)
    exact mainR_code p ▸ h'

/-! ## `mainR` on a diverging program -/

/-- The specification of `mainR` on `n` for a program diverging from `σ`: it never returns. -/
def divMainRSpec (p : Prog) (n : BitVec 31) (σ : Heap) (μ : List Nat) : FSpec Nat :=
  ⟨mainRPre p n σ μ, fun _ _ _ _ => False⟩

/-- **`mainR` never returns on a diverging program**, at every step index. -/
theorem mainR_div (hfit : p.Fits) {τ : Ty} (ht : HasTy [.int] p.body τ) {n : BitVec 31}
    {σ : Heap} (hT : Typed [.int] σ [.int n]) (hdv : SDiv σ [.int n] p.body) (μ : List Nat) :
    FSpecValid P host 2 (divMainRSpec p n σ μ)
  | 0 => by unfold FSpecAt; intros; exact trivial
  | m + 1 => by
    refine FSpecAt.of_body (fi := mainRInst p) (code := mainRFunc p) (fun _ _ h => h.1) rfl
      ⟨rfl⟩ ?_ ?_
    · rintro s args ⟨-, -, -, rfl⟩
      rfl
    · rintro s args ⟨-, hfn, hh, rfl⟩ f vs₀
      have h' := (div_all (P := P) (host := host) hfit m).2 1 p.body [.int] τ σ [.int n] ht hT
        hdv μ s (frameR p n) (frameR_ok hfit n) hfn (by rw [frameR_len]; omega)
        (env_frameR μ s n) hh (fun _ hx => hx) [] []
        (bodyPostK P host 1 f vs₀ (callPost f vs₀ ((divMainRSpec p n σ μ).post s
          [.ref (.i31 0), .ref (.i31 n)])) m)
      exact mainR_code p ▸ h'

end Silmaril.Proofs.Wasm.Models.FunRefCloGame
