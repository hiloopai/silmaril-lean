module

public import Silmaril.Proofs.Wasm.Models.FunRefCompile.Cases
public import Silmaril.Wasm.Models.FunRef.Thms

/-!
# Compiling FunRef: the compiled function and its behaviours

`main_tspec`: `main` meets its total specification; `behaviours_main`: its behaviours in
`storeOf p` are exactly the return of the program's word (through
`Silmaril.Proofs.Wasm.Models.FunCompile.behaviours_eq_of_tspec`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRef (Tm eval Heap Prog ValTy obsWord)
open Silmaril.Wasm.Models.FunCompile (dBox dMain lx unbox)
open Silmaril.Proofs.Wasm.Models.FunCompile (Agree twp_unbox twp_box twp_localGet twp_localSet
  setWidth_31_32 len_setLocal setLocal_get lt_lim bodyPostT_normal behaviours_eq_of_tspec)
open Silmaril.Wasm.Logic.Core (Post Outcome)

/-- The specification of `main` on `n`, returning the word `k`. -/
def mainSpec (p : Prog) (n k : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInst p) ∧ args = [.i32 (n.setWidth 32)],
    fun _ _ _ o => o = .normal [.i32 (k.setWidth 32)]⟩

/-- A ground value is represented by the `i31` of its word. -/
theorem rep_ground {H : Type} {μ : List Nat} {s : Store H} {Ψ : List FunRef.Ty} {v : FunRef.Val}
    {τ : FunRef.Ty} (ht : ValTy Ψ v τ) (hg : τ.Ground) {w : Val} (hw : Rep μ s v w) :
    w = .ref (.i31 (obsWord v)) := by
  cases ht with
  | int n => exact hw
  | bool b => exact hw
  | pair => exact hg.elim
  | inl => exact hg.elim
  | inr => exact hg.elim
  | loc => exact hg.elim

/-- The frame of `main` on `n`. -/
def frame0 (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instOf [.i32 (n.setWidth 32)] (funcOf p).locals

theorem frame0_len (p : Prog) (n : BitVec 31) : (frame0 p n).locals.length = p.body.depth + 2 := by
  simp [frame0, Frame.forCall, funcOf]

theorem frame0_ok {p : Prog} (hfit : p.Fits) (n : BitVec 31) : FrameR (frame0 p n) :=
  ⟨rfl, by rw [frame0_len]; exact Nat.le_of_lt hfit⟩

theorem frame0_arg (p : Prog) (n : BitVec 31) :
    (frame0 p n).locals[0]? = some (some (.i32 (n.setWidth 32))) := by
  simp [frame0, Frame.forCall]

theorem env_prologue {H : Type} {p : Prog} (hfit : p.Fits) (s : Store H) (n : BitVec 31) :
    EnvRep [] s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) 1 [.int n] := by
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  refine ⟨rfl, fun i u hi => ?_⟩
  have hi0 : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  subst hi0
  have hu : u = .int n := by simpa using hi.symm
  exact ⟨_, setLocal_get _ hlt (lt_lim (frame0_ok hfit n).ok hlt), hu ▸ rfl⟩

theorem heap_empty {H : Type} (s : Store H) : HeapRep [] s [] :=
  ⟨rfl, List.nodup_nil, fun _ _ h => absurd h (by simp)⟩

theorem mainBody_code (p : Prog) :
    expression (mainBody p) = vals [] ++ .plain (.localGet (lx 0)) :: .plain .refI31 ::
      .plain (.localSet (lx 1)) :: (expression (compile 1 p.body) ++ (expression unbox ++ [])) := by
  simp [mainBody, expression]

/-- **The body of `main` is totally correct.** -/
theorem body_twp {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog} (hp : p.WellTyped)
    (hfit : p.Fits) {n : BitVec 31} {v : FunRef.Val} {σ : Heap} (hv : p.run n = some (v, σ))
    (s : Store Nat) (f : Frame) (vs₀ : List Val) :
    TWP P host s (frame0 p n) (expression (mainBody p))
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  obtain ⟨v', σ'', Ψ, hv', hty⟩ := p.run_sound hp n
  have hvv : v' = v := (Prod.mk.inj (Option.some.inj (hv'.symm.trans hv))).1
  have hok := frame0_ok hfit n
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  have hd : 1 + p.body.depth < ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frame0_len]; omega
  have hk : Cont P host 1 [] s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) v σ []
      (expression unbox ++ [])
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
    intro μ' s' f' w _ _ _ _ hw
    rw [rep_ground (hvv ▸ hty) hp.2 hw]
    have hb : bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)])) s' f'
        (.normal [.i32 ((obsWord v).setWidth 32)]) := bodyPostT_normal rfl rfl
    have hw' : TWP P host s' f' (vals [.i32 ((obsWord v).setWidth 32)]) _ :=
      Wp.of_vals (m := .total) hb
    exact twp_unbox (by simpa using hw')
  rw [mainBody_code]
  refine twp_localGet hok.ok (frame0_arg p n) (twp_box ?_)
  rw [setWidth_31_32]
  exact twp_localSet hok.ok hlt (spec_compile p.body 1 [] [.int n] v σ hv [] s _
    (hok.setLocal _ _) hd (env_prologue hfit s n) (heap_empty s) [] _ _ hk)

/-- **`main` meets its total specification**, at every profile and for every host. -/
theorem main_tspec {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog} (hp : p.WellTyped)
    (hfit : p.Fits) {n : BitVec 31} {v : FunRef.Val} {σ : Heap} (hv : p.run n = some (v, σ)) :
    TFSpecAt P host 0 (mainSpec p n (obsWord v)) := by
  refine TFSpecAt.of_body (fi := mainInst p) (code := funcOf p) (fun _ _ h => h.1) rfl ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, rfl⟩
    rfl
  · rintro s args ⟨-, rfl⟩ f vs₀
    exact body_twp hp hfit hv s f vs₀

/-- **The behaviours of the compiled program**, at every profile and for every host. -/
theorem behaviours_main (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) (n : BitVec 31) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} := by
  obtain ⟨v, σ, -, hv, -⟩ := p.run_sound hp n
  have hw : p.word n = obsWord v := by simp [Prog.word, hv]
  rw [hw]
  exact behaviours_eq_of_tspec (main_tspec hp hfit hv) ⟨rfl, rfl⟩ fun _ _ h => h

end Silmaril.Proofs.Wasm.Models.FunRefCompile
