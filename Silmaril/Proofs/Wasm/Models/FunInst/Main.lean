module

public import Silmaril.Wasm.Models.FunInst.Defs
public import Silmaril.Wasm.Models.FunCompile.Thms
public import Silmaril.Wasm.Models.FunRefCompile.Thms

/-!
# The instantiated stores of the FunLang and FunRef compilers: behaviours

`main` meets its total specification in the instance `instX` that instantiation produces, as in
`instOf`: the proofs of `Silmaril.Proofs.Wasm.Models.FunCompile.Main` and
`Silmaril.Proofs.Wasm.Models.FunRefCompile.Main` use only the defined types of the instance, which
are the same. `behaviours_mainX` (FunCompile) and `behaviours_mainRX` (FunRefCompile) are the
behaviours of `main` in the instantiated stores `storeX p`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunInst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunCompile (dBox dMain lx unbox)
open Silmaril.Proofs.Wasm.Models.FunCompile (Agree twp_unbox twp_box twp_localGet twp_localSet
  setWidth_31_32 len_setLocal setLocal_get lt_lim bodyPostT_normal behaviours_eq_of_tspec)

/-! ## FunLang -/

section FunLang

open Silmaril.Wasm.Models.FunCompile (instX mainInstX storeX funcOf mainBody compile)
open Silmaril.Wasm.Models.FunLang (Prog obsWord)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK EnvRep Cont spec_compile rep_ground mainSpec)

/-- The frame of `main` on `n` in `instX`. -/
def frameX (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instX [.i32 (n.setWidth 32)] (funcOf p).locals

theorem frameX_len (p : Prog) (n : BitVec 31) : (frameX p n).locals.length = p.body.depth + 2 := by
  simp [frameX, Frame.forCall, funcOf]

theorem frameX_ok {p : Prog} (hfit : p.Fits) (n : BitVec 31) : FrameOK (frameX p n) :=
  ⟨⟨[dMain], rfl⟩, by rw [frameX_len]; exact Nat.le_of_lt hfit⟩

theorem frameX_arg (p : Prog) (n : BitVec 31) :
    (frameX p n).locals[0]? = some (some (.i32 (n.setWidth 32))) := by
  simp [frameX, Frame.forCall]

theorem envX_prologue {H : Type} {p : Prog} (hfit : p.Fits) (s : Store H) (n : BitVec 31) :
    EnvRep s ((frameX p n).setLocal (lx 1) (.ref (.i31 n))) 1 [.int n] := by
  have hlt : 1 < (frameX p n).locals.length := by rw [frameX_len]; omega
  refine ⟨rfl, fun i u hi => ?_⟩
  obtain rfl : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  have hu : u = .int n := by simpa using hi.symm
  exact ⟨_, setLocal_get _ hlt (lt_lim (frameX_ok hfit n) hlt), hu ▸ rfl⟩

/-- The continuation of `main`'s body: unbox the result and return it. -/
theorem contX {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog} (hp : p.WellTyped)
    {n : BitVec 31} {v : FunLang.Val} (hty : FunLang.ValTy v p.res) (s : Store Nat)
    (f : Frame) (vs₀ : List Val) :
    Cont P host 1 s ((frameX p n).setLocal (lx 1) (.ref (.i31 n))) v []
      (expression unbox ++ [])
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  intro s' f' w _ _ hw
  have hw₀ : w = .ref (.i31 (obsWord v)) := rep_ground hty hp.2 hw
  have hb : bodyPostT P host 1 f vs₀
      (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)])) s' f'
      (.normal [.i32 ((obsWord v).setWidth 32)]) := bodyPostT_normal rfl rfl
  have hw' : TWP P host s' f' (vals [.i32 ((obsWord v).setWidth 32)]) _ :=
    Wp.of_vals (m := .total) hb
  rw [hw₀]
  exact twp_unbox (by simpa using hw')

/-- The body of `main` in `instX` is totally correct. -/
theorem body_twpX {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} {v : FunLang.Val} (hv : p.run n = some v)
    (s : Store Nat) (f : Frame) (vs₀ : List Val) :
    TWP P host s (frameX p n) (expression (mainBody p))
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  obtain ⟨v', hv', hty⟩ := p.run_sound hp n
  have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
  have hok := frameX_ok hfit n
  have hlt : 1 < (frameX p n).locals.length := by rw [frameX_len]; omega
  have hd : 1 + p.body.depth < ((frameX p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frameX_len]; omega
  rw [Silmaril.Proofs.Wasm.Models.FunCompile.mainBody_code]
  refine twp_localGet hok (frameX_arg p n) (twp_box ?_)
  rw [setWidth_31_32]
  exact twp_localSet hok hlt (spec_compile p.body 1 [.int n] v hv s _ (hok.setLocal _ _) hd
    (envX_prologue hfit s n) [] _ _ (contX hp (hvv ▸ hty) s f vs₀))

/-- The specification of `main` in `storeX p`. -/
def mainSpecX (p : Prog) (n k : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInstX p) ∧ args = [.i32 (n.setWidth 32)],
    fun _ _ _ o => o = .normal [.i32 (k.setWidth 32)]⟩

/-- **The behaviours of `main` in the instantiated store** of a FunLang program. -/
theorem behaviours_mainX (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) (n : BitVec 31) :
    behaviours P host (storeX p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} := by
  obtain ⟨v, hv, -⟩ := p.run_sound hp n
  have hw : p.word n = obsWord v := by simp [Prog.word, hv]
  have hspec : TFSpecAt P host 0 (mainSpecX p n (obsWord v)) := by
    refine TFSpecAt.of_body (fi := mainInstX p) (code := funcOf p) (fun _ _ h => h.1) rfl ⟨rfl⟩
      ?_ ?_
    · rintro s args ⟨-, rfl⟩
      rfl
    · rintro s args ⟨-, rfl⟩ f vs₀
      exact body_twpX hp hfit hv s f vs₀
  rw [hw]
  exact behaviours_eq_of_tspec hspec ⟨rfl, rfl⟩ fun _ _ h => h

end FunLang

/-! ## FunRef -/

section FunRef

open Silmaril.Wasm.Models.FunRefCompile (instX mainInstX storeX funcOf mainBody compile)
open Silmaril.Wasm.Models.FunRef (Prog obsWord Heap)
open Silmaril.Proofs.Wasm.Models.FunRefCompile (FrameR EnvRep Cont spec_compile rep_ground
  heap_empty)

/-- The frame of `main` on `n` in `instX`. -/
def frameRX (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instX [.i32 (n.setWidth 32)] (funcOf p).locals

theorem frameRX_len (p : Prog) (n : BitVec 31) :
    (frameRX p n).locals.length = p.body.depth + 2 := by
  simp [frameRX, Frame.forCall, funcOf]

theorem frameRX_ok {p : Prog} (hfit : p.Fits) (n : BitVec 31) : FrameR (frameRX p n) :=
  ⟨rfl, by rw [frameRX_len]; exact Nat.le_of_lt hfit⟩

theorem frameRX_arg (p : Prog) (n : BitVec 31) :
    (frameRX p n).locals[0]? = some (some (.i32 (n.setWidth 32))) := by
  simp [frameRX, Frame.forCall]

theorem envRX_prologue {H : Type} {p : Prog} (hfit : p.Fits) (s : Store H) (n : BitVec 31) :
    EnvRep [] s ((frameRX p n).setLocal (lx 1) (.ref (.i31 n))) 1 [.int n] := by
  have hlt : 1 < (frameRX p n).locals.length := by rw [frameRX_len]; omega
  refine ⟨rfl, fun i u hi => ?_⟩
  obtain rfl : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  have hu : u = .int n := by simpa using hi.symm
  exact ⟨_, setLocal_get _ hlt (lt_lim (frameRX_ok hfit n).ok hlt), hu ▸ rfl⟩

/-- The continuation of `main`'s body: unbox the result and return it. -/
theorem contRX {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}
    (hp : p.WellTyped) {n : BitVec 31} {v : FunRef.Val} {σ : Heap} {Ψ : List FunRef.Ty}
    (hty : FunRef.ValTy Ψ v p.res) (s : Store Nat) (f : Frame) (vs₀ : List Val) :
    Cont P host 1 [] s ((frameRX p n).setLocal (lx 1) (.ref (.i31 n))) v σ []
      (expression unbox ++ [])
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  intro μ' s' f' w _ _ _ _ hw
  have hw₀ : w = .ref (.i31 (obsWord v)) := rep_ground hty hp.2 hw
  have hb : bodyPostT P host 1 f vs₀
      (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)])) s' f'
      (.normal [.i32 ((obsWord v).setWidth 32)]) := bodyPostT_normal rfl rfl
  have hw' : TWP P host s' f' (vals [.i32 ((obsWord v).setWidth 32)]) _ :=
    Wp.of_vals (m := .total) hb
  rw [hw₀]
  exact twp_unbox (by simpa using hw')

/-- The body of `main` in `instX` is totally correct. -/
theorem body_twpRX {P : Numerics.Profile} {host : HostSemantics Nat} {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) {n : BitVec 31} {v : FunRef.Val} {σ : Heap}
    (hv : p.run n = some (v, σ)) (s : Store Nat) (f : Frame) (vs₀ : List Val) :
    TWP P host s (frameRX p n) (expression (mainBody p))
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  obtain ⟨v', σ'', Ψ, hv', hty⟩ := p.run_sound hp n
  have hvv : v' = v := (Prod.mk.inj (Option.some.inj (hv'.symm.trans hv))).1
  have hok := frameRX_ok hfit n
  have hlt : 1 < (frameRX p n).locals.length := by rw [frameRX_len]; omega
  have hd : 1 + p.body.depth <
      ((frameRX p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frameRX_len]; omega
  rw [Silmaril.Proofs.Wasm.Models.FunRefCompile.mainBody_code]
  refine twp_localGet hok.ok (frameRX_arg p n) (twp_box ?_)
  rw [setWidth_31_32]
  exact twp_localSet hok.ok hlt (spec_compile p.body 1 [] [.int n] v σ hv [] s _
    (hok.setLocal _ _) hd (envRX_prologue hfit s n) (heap_empty s) [] _ _
    (contRX hp (hvv ▸ hty) s f vs₀))

/-- The specification of `main` in `storeX p`. -/
def mainSpecRX (p : Prog) (n k : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInstX p) ∧ args = [.i32 (n.setWidth 32)],
    fun _ _ _ o => o = .normal [.i32 (k.setWidth 32)]⟩

/-- **The behaviours of `main` in the instantiated store** of a FunRef program. -/
theorem behaviours_mainRX (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) (n : BitVec 31) :
    behaviours P host (storeX p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} := by
  obtain ⟨v, σ, -, hv, -⟩ := p.run_sound hp n
  have hw : p.word n = obsWord v := by simp [Prog.word, hv]
  have hspec : TFSpecAt P host 0 (mainSpecRX p n (obsWord v)) := by
    refine TFSpecAt.of_body (fi := mainInstX p) (code := funcOf p) (fun _ _ h => h.1) rfl ⟨rfl⟩
      ?_ ?_
    · rintro s args ⟨-, rfl⟩
      rfl
    · rintro s args ⟨-, rfl⟩ f vs₀
      exact body_twpRX hp hfit hv s f vs₀
  rw [hw]
  exact behaviours_eq_of_tspec hspec ⟨rfl, rfl⟩ fun _ _ h => h

end FunRef

end Silmaril.Proofs.Wasm.Models.FunInst
