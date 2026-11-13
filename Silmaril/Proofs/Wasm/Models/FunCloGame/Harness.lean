module

public import Silmaril.Wasm.Models.FunCloGame.Defs
public import Silmaril.Wasm.Models.FunCloDiv.Thms

/-!
# The closure game of FunClo: the harness and single invocations

* `frameR`, `frameR_ok`, `env_frameR`: the frame of `mainR` on `n` and its invariants: the
  argument `n` is the environment at depth `1`, as in `main` after its prologue.
* `mainRSpec`, `mainR_tspec`: `mainR` on `n` returns a representation of the program's value in
  an extended store, if the program returns it (total correctness, from FunCloCompile's
  `spec_all`).
* `mainR_div`: `mainR` never returns on an argument on which the program diverges (from
  FunCloDiv's `div_all`).
* `returns_of_tspec`: a function with a total specification whose postcondition only allows
  returning one value has a run (`Returns`) that returns a value meeting the postcondition.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile Silmaril.Wasm.Models.FunCloGame
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunClo (Tm eval Prog Ty HasTy ValTy EnvTy)
open Silmaril.Wasm.Models.FunCompile (lx anyref dBox dMain)
open Silmaril.Proofs.Wasm.Models.FunCompile (bodyPostT_normal invoke_exit)
open Silmaril.Proofs.Wasm.Models.FunCloCompile (Rep Ext FOK EnvRep spec_all)
open Silmaril.Proofs.Wasm.Models.FunCloDiv (div_all SDiv)
open Silmaril.Wasm.Logic.Core (Post Outcome)

variable {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}

/-! ## The frame of `mainR` -/

/-- The frame of `mainR` on `n`. -/
def frameR (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instOf [.ref (.i31 0), .ref (.i31 n)] (mainRFunc p).locals

theorem frameR_len (p : Prog) (n : BitVec 31) :
    (frameR p n).locals.length = p.body.depth + 2 := by
  simp [frameR, Frame.forCall, mainRFunc]

theorem frameR_ok (hfit : p.Fits) (n : BitVec 31) : FOK (frameR p n) :=
  ⟨⟨⟨[dMain, dApply], rfl⟩, by rw [frameR_len]; exact Nat.le_of_lt hfit.1⟩, rfl⟩

/-- The argument is the environment `[int n]` at depth `1`. -/
theorem env_frameR (s : Store Nat) (n : BitVec 31) :
    EnvRep p.table s (frameR p n) 1 [.int n] := by
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

/-- The specification of `mainR` on `n` for a program returning `v`. -/
def mainRSpec (p : Prog) (n : BitVec 31) (v : FunClo.Val) : FSpec Nat :=
  ⟨fun s args => s.funcs[2]? = some (mainRInst p) ∧ s.funcs[1]? = some (applyInst p) ∧
      args = [.ref (.i31 0), .ref (.i31 n)],
    fun s _ s' o => ∃ w, o = .normal [w] ∧ Ext s s' ∧ Rep p.table s' v w⟩

/-- **`mainR` is totally correct**: it returns a representation of the program's value. -/
theorem mainR_tspec (hfit : p.Fits) {n : BitVec 31} {k : Nat} {v : FunClo.Val}
    (hv : eval k [.int n] p.body = some v) : TFSpecAt P host 2 (mainRSpec p n v) := by
  refine TFSpecAt.of_body (fi := mainRInst p) (code := mainRFunc p) (fun _ _ h => h.1) rfl
    ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, -, rfl⟩
    rfl
  · rintro s args ⟨-, hfn, rfl⟩ f vs₀
    have h' := spec_all (P := P) (host := host) hfit k 1 p.body [.int n] v hv s (frameR p n)
      (frameR_ok hfit n) hfn (by rw [frameR_len]; omega) (env_frameR s n) (fun _ hx => hx) [] []
      (bodyPostT P host 1 f vs₀ (callPost f vs₀ ((mainRSpec p n v).post s
        [.ref (.i31 0), .ref (.i31 n)])))
      fun s' F' w hs _ hw => by
        simpa using Wp.of_vals (m := .total) (vs := [w])
          (bodyPostT_normal (P := P) (host := host) rfl ⟨w, rfl, hs, hw⟩)
    exact mainR_code p ▸ h'

/-! ## `mainR` on a diverging program -/

/-- The specification of `mainR` on `n` for a diverging program: it never returns. -/
def divMainRSpec (p : Prog) (n : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[2]? = some (mainRInst p) ∧ s.funcs[1]? = some (applyInst p) ∧
      args = [.ref (.i31 0), .ref (.i31 n)],
    fun _ _ _ _ => False⟩

/-- **`mainR` never returns on a diverging program**, at every step index. -/
theorem mainR_div (hfit : p.Fits) {τ : Ty} (ht : HasTy [.int] p.body τ) {n : BitVec 31}
    (hdv : SDiv [.int n] p.body) : FSpecValid P host 2 (divMainRSpec p n)
  | 0 => by unfold FSpecAt; intros; exact trivial
  | m + 1 => by
    refine FSpecAt.of_body (fi := mainRInst p) (code := mainRFunc p) (fun _ _ h => h.1) rfl
      ⟨rfl⟩ ?_ ?_
    · rintro s args ⟨-, -, rfl⟩
      rfl
    · rintro s args ⟨-, hfn, rfl⟩ f vs₀
      have h' := (div_all (P := P) (host := host) hfit m).2 1 p.body [.int] τ [.int n] ht
        (.cons (.int n) .nil) hdv s (frameR p n) (frameR_ok hfit n) hfn
        (by rw [frameR_len]; omega) (env_frameR s n) (fun _ hx => hx) [] []
        (bodyPostK P host 1 f vs₀ (callPost f vs₀ ((divMainRSpec p n).post s
          [.ref (.i31 0), .ref (.i31 n)])) m)
      exact mainR_code p ▸ h'

/-! ## Runs of single invocations -/

/-- **A run returning one value** of a function with a total specification whose postcondition
only allows returning one value. -/
theorem returns_of_tspec {a : Nat} {S : FSpec Nat} {s : Store Nat} {args : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → ∃ w, o = .normal [w]) :
    ∃ s' w, Returns P host s a args s' w ∧ S.post s args s' (.normal [w]) := by
  obtain ⟨⟨s', f', code⟩, hs, o, he, hq⟩ := invoke_exit h hpre
  rcases hq.2 with ⟨res', rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨b, rfl, hp⟩
  · obtain ⟨w, hw⟩ := hpost _ _ hp
    have hres : res' = [w] := by injection hw
    subst hres
    have hcode : code = vals ([] ++ [w]) := he
    exact ⟨s', w, ⟨f', by simpa [hcode] using hs⟩, hp⟩
  · obtain ⟨w, hw⟩ := hpost _ _ hp
    exact absurd hw (by simp)
  · obtain ⟨w, hw⟩ := hpost _ _ hp
    exact absurd hw (by simp)

end Silmaril.Proofs.Wasm.Models.FunCloGame
