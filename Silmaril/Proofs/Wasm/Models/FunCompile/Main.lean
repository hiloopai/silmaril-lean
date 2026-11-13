module

public import Silmaril.Proofs.Wasm.Models.FunCompile.Cases
public import Silmaril.Wasm.Models.FunLang.Thms

/-!
# Compiling FunLang: the compiled function and its behaviours

* `tsafe_exists_exit`: a totally correct configuration has a run to an exit satisfying the
  postcondition;
* `behaviours_eq_of_tspec`: the behaviours of `$invoke` of a function with a total specification
  whose postcondition only allows returning `res` are exactly `{returns res}`;
* `main_tspec`: `main` meets its total specification `mainSpec p n k` (it returns the `i32` of
  the word `k` of the program's value);
* `behaviours_main`: the behaviours of `main` in `storeOf p`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunLang (Tm eval Prog ValTy obsWord)
open Silmaril.Wasm.Logic.Core (Post Outcome)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Behaviours of a totally specified function -/

/-- A totally correct configuration has a run to an exit satisfying the postcondition. -/
theorem tsafe_exists_exit {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∃ c', Steps P host c c' ∧ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, .refl, o, he, hq⟩
  | step hp _ ih =>
    obtain ⟨c₁, hst⟩ := hp
    obtain ⟨c', hs, o, he, hq⟩ := ih c₁ hst
    exact ⟨c', .head hst hs, o, he, hq⟩

/-- A run of `$invoke` to an exit of a function with a total specification. -/
theorem invoke_exit {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args) :
    ∃ c', Steps P host (invoke s a args) c' ∧ ∃ o, Exits o c'.code ∧
      callPost {} [] (S.post s args) c'.store c'.frame o := by
  have ht : TSafe P host (callPost {} [] (S.post s args)) (invoke s a args) := by
    rw [invoke_code]
    exact h s args hpre {} [] _ trivial
  exact tsafe_exists_exit ht

/-- The returned values of a function whose postcondition only allows `res` are in its
behaviours. -/
theorem returns_mem {a : Nat} {S : FSpec H} {s : Store H} {args res : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal res) :
    Behaviour.returns res ∈ behaviours P host s a args := by
  obtain ⟨⟨s', f', code⟩, hs, o, he, hq⟩ := invoke_exit h hpre
  rcases hq.2 with ⟨res', rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨b, rfl, hp⟩
  · have hres : Outcome.normal res' = .normal res := hpost _ _ hp
    have hcode : code = vals ([] ++ res') := he
    have hres' : res' = res := by injection hres
    exact returns_mem_behavioursOf hs (by rw [hcode, ← hres']; rfl)
  · exact absurd (hpost _ _ hp) (by simp)
  · exact absurd (hpost _ _ hp) (by simp)

/-- Every behaviour of a function whose postcondition only allows `res` returns `res`. -/
theorem behaviours_subset {a : Nat} {S : FSpec H} {s : Store H} {args res : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal res) {b : Behaviour Val}
    (hb : b ∈ behaviours P host s a args) : b = .returns res := by
  rcases hb with ⟨⟨s', f', code⟩, r, hs, hc, rfl⟩ | ⟨-, hd⟩
  · show r.toBehaviour = .returns res
    cases r with
    | values vs =>
      have hc' : code = vals vs := hc
      have hv : S.post s args s' (.normal vs) := h.invoke_vals hpre (hc' ▸ hs)
      have hvs : Outcome.normal vs = .normal res := hpost _ _ hv
      have hvs' : vs = res := by injection hvs
      exact hvs' ▸ rfl
    | trap =>
      have hc' : code = [.trap] := hc
      have hv : S.post s args s' .trap := h.valid.invoke_trap hpre (hc' ▸ hs)
      exact absurd (hpost _ _ hv) (by simp)
    | throw x =>
      show Result.toBehaviour (.throw x) = .returns res
      have hc' : code = throwing x := hc
      have hs' : Steps P host ⟨s, {}, (invoke s a args).code⟩ ⟨s', f', throwing x⟩ := hc' ▸ hs
      have hv : callPost {} [] (S.post s args) s' f' (.throw x) :=
        (h.valid.hwp_invoke hpre).sound_throw hs'
      rcases hv.2 with ⟨_, he, -⟩ | ⟨he, -⟩ | ⟨y, he, hp⟩
      · exact absurd he (by simp)
      · exact absurd he (by simp)
      · exact absurd (hpost _ _ hp) (by simp)
  · exact absurd hd (h.invoke_terminates hpre)

/-- **The behaviours of a totally specified function** whose postcondition only allows
returning `res`. -/
theorem behaviours_eq_of_tspec {a : Nat} {S : FSpec H} {s : Store H} {args res : List Val}
    (h : TFSpecAt P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal res) :
    behaviours P host s a args = {.returns res} :=
  Set.eq_singleton_iff_unique_mem.2
    ⟨returns_mem h hpre hpost, fun _ hb => behaviours_subset h hpre hpost hb⟩

/-! ## The compiled function -/

/-- The specification of `main` on `n`, returning the word `k`. -/
def mainSpec (p : Prog) (n k : BitVec 31) : FSpec Nat :=
  ⟨fun s args => s.funcs[0]? = some (mainInst p) ∧ args = [.i32 (n.setWidth 32)],
    fun _ _ _ o => o = .normal [.i32 (k.setWidth 32)]⟩

/-- A ground value is represented by the `i31` of its word. -/
theorem rep_ground {s : Store H} {v : FunLang.Val} {τ : FunLang.Ty} (ht : ValTy v τ)
    (hg : τ.Ground) {w : Val} (hw : Rep s v w) : w = .ref (.i31 (obsWord v)) := by
  cases ht with
  | int n => exact hw
  | bool b => exact hw
  | pair => exact hg.elim
  | inl => exact hg.elim
  | inr => exact hg.elim

/-- A function body returning `res` meets the call postcondition `callPost f vs₀ R` if `R`
holds of the returned values. -/
theorem bodyPostT_normal {n : Nat} {s : Store H} {f F : Frame} {vs₀ res : List Val}
    {R : Store H → Outcome → Prop} (hlen : res.length = n) (h : R s (.normal res)) :
    bodyPostT P host n f vs₀ (callPost f vs₀ R) s F (.normal res) := by
  show framePostT P host n f vs₀ (callPost f vs₀ R) s F (.normal ([] ++ res))
  exact ⟨by simpa using hlen, rfl, .inl ⟨res, rfl, h⟩⟩

/-- The frame of `main` on `n`. -/
def frame0 (p : Prog) (n : BitVec 31) : Frame :=
  Frame.forCall instOf [.i32 (n.setWidth 32)] (funcOf p).locals

theorem frame0_len (p : Prog) (n : BitVec 31) : (frame0 p n).locals.length = p.body.depth + 2 := by
  simp [frame0, Frame.forCall, funcOf]

theorem frame0_ok {p : Prog} (hfit : p.Fits) (n : BitVec 31) : FrameOK (frame0 p n) :=
  ⟨⟨[dMain], rfl⟩, by rw [frame0_len]; exact Nat.le_of_lt hfit⟩

theorem frame0_arg (p : Prog) (n : BitVec 31) :
    (frame0 p n).locals[0]? = some (some (.i32 (n.setWidth 32))) := by
  simp [frame0, Frame.forCall]

/-- The environment after the prologue: the boxed argument in local `1`. -/
theorem env_prologue {p : Prog} (hfit : p.Fits) (s : Store H) (n : BitVec 31) :
    EnvRep s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) 1 [.int n] := by
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  refine ⟨rfl, fun i u hi => ?_⟩
  have hi0 : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp at hi
  subst hi0
  have hu : u = .int n := by simpa using hi.symm
  exact ⟨_, setLocal_get _ hlt (lt_lim (frame0_ok hfit n) hlt), hu ▸ rfl⟩

theorem mainBody_code (p : Prog) :
    expression (mainBody p) = vals [] ++ .plain (.localGet (lx 0)) :: .plain .refI31 ::
      .plain (.localSet (lx 1)) :: (expression (compile 1 p.body) ++ (expression unbox ++ [])) := by
  simp [mainBody, expression]

/-- **The body of `main` is totally correct**: it returns the word of the program's value. -/
theorem body_twp {host : HostSemantics Nat} {p : Prog} (hp : p.WellTyped) (hfit : p.Fits)
    {n : BitVec 31} {v : FunLang.Val} (hv : p.run n = some v) (s : Store Nat) (f : Frame)
    (vs₀ : List Val) :
    TWP P host s (frame0 p n) (expression (mainBody p))
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
  obtain ⟨v', hv', hty⟩ := p.run_sound hp n
  have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
  have hok := frame0_ok hfit n
  have hlt : 1 < (frame0 p n).locals.length := by rw [frame0_len]; omega
  have hd : 1 + p.body.depth < ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))).locals.length := by
    rw [len_setLocal, frame0_len]; omega
  have hk : Cont P host 1 s ((frame0 p n).setLocal (lx 1) (.ref (.i31 n))) v []
      (expression unbox ++ [])
      (bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)]))) := by
    intro s' f' w _ _ hw
    rw [rep_ground (hvv ▸ hty) hp.2 hw]
    have hb : bodyPostT P host 1 f vs₀
        (callPost f vs₀ (fun _ o => o = .normal [.i32 ((obsWord v).setWidth 32)])) s' f'
        (.normal [.i32 ((obsWord v).setWidth 32)]) := bodyPostT_normal rfl rfl
    have hw' : TWP P host s' f' (vals [.i32 ((obsWord v).setWidth 32)]) _ :=
      Wp.of_vals (m := .total) hb
    exact twp_unbox (by simpa using hw')
  rw [mainBody_code]
  refine twp_localGet hok (frame0_arg p n) (twp_box ?_)
  rw [setWidth_31_32]
  exact twp_localSet hok hlt (spec_compile p.body 1 [.int n] v hv s _ (hok.setLocal _ _) hd
    (env_prologue hfit s n) [] _ _ hk)

/-- **`main` meets its total specification**, at every profile and for every host. -/
theorem main_tspec {host : HostSemantics Nat} {p : Prog} (hp : p.WellTyped) (hfit : p.Fits)
    {n : BitVec 31} {v : FunLang.Val} (hv : p.run n = some v) :
    TFSpecAt P host 0 (mainSpec p n (obsWord v)) := by
  refine TFSpecAt.of_body (fi := mainInst p) (code := funcOf p) (fun _ _ h => h.1) rfl ⟨rfl⟩ ?_ ?_
  · rintro s args ⟨-, rfl⟩
    rfl
  · rintro s args ⟨-, rfl⟩ f vs₀
    exact body_twp hp hfit hv s f vs₀

/-- **The behaviours of the compiled program**: `main` on `n` returns the word the program
computes on `n`, at every profile and for every host. -/
theorem behaviours_main (P : Numerics.Profile) (host : HostSemantics Nat) {p : Prog}
    (hp : p.WellTyped) (hfit : p.Fits) (n : BitVec 31) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} := by
  obtain ⟨v, hv, -⟩ := p.run_sound hp n
  have hw : p.word n = obsWord v := by simp [Prog.word, hv]
  rw [hw]
  exact behaviours_eq_of_tspec (main_tspec hp hfit hv) ⟨rfl, rfl⟩ fun _ _ h => h

end Silmaril.Proofs.Wasm.Models.FunCompile
