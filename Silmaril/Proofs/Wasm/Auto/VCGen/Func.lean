module

public import Silmaril.Proofs.Wasm.Auto.VCGen.Sound
public import Silmaril.Wasm.Examples.Common.Thms

/-!
# The reflective VC generator: function specifications

`genFunc_sound`: valid conditions `AllValid F (genFunc S code fuel)` give the every-run function
specification `fspec F S a fi` (`Silmaril.Wasm.Logic.Hoare.FSpecValid`), for every profile and
host relation. The body is started from `initSt` (`rel_init`), `gen_sound` gives its every-run
weakest precondition, and `bodyPostK_of_postOf` reads the outcomes the generator allows (falling
through with exactly the results, or `return`) as the caller's postcondition.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP FSpecValid FSpecAt bodyPostK callPost)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}

/-! ## Arguments and results -/

theorem agree_of_args {ρ ρ' : Env} (h : argsOf S ρ = argsOf S ρ') : Agree S.params ρ ρ' := by
  intro i t hi
  have hi' := (List.getElem?_eq_some_iff.mp hi)
  have := congrArg (·[i]?) h
  simp only [argsOf, List.getElem?_mapIdx, hi, Option.map_some, Option.some.injEq,
    Val.num.injEq] at this
  exact numVal_inj this

theorem valEnv_dens (ρ : Env) (ls : List SV) :
    valEnv (dens F ρ ls) = locEnv F ρ ρ ls := (locEnv_eq_valEnv ρ ρ ls).symm

/-- The postcondition from its condition at the top `n` values of the stack, for every
environment of the same arguments. -/
theorem post_of_vc (hS : S.wellScoped = true) {ρ ρ₀ : Env} {ls : List SV}
    (hag : Agree S.params ρ ρ₀) (hv : (S.post.subst ls).den F ρ ρ) :
    ∀ ρ', argsOf S ρ₀ = argsOf S ρ' → S.post.den F ρ' (valEnv (dens F ρ ls)) := by
  intro ρ' hargs
  have hsc : S.post.scoped S.params = true := by
    simp only [FnSpec.wellScoped, Bool.and_eq_true] at hS
    exact hS.1
  rw [Fm.den_subst] at hv
  rw [valEnv_dens]
  exact (Fm.den_scoped (Agree.trans hag (agree_of_args hargs)) _ _ hsc).mp hv

/-! ## The initial state -/

theorem intTys?_eq {ts : List ValType} {lts : List IntType} (h : intTys? ts = some lts) :
    ts = lts.map fun t => .num (.int t) := by
  induction ts generalizing lts with
  | nil =>
    simp only [intTys?, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | cons t ts ih =>
    simp only [intTys?, List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨u, hu, us, hus, rfl⟩ := h
    rw [ih hus]
    rcases t with (u' | _) | _ | _ <;> simp only [intTy?, Option.some.injEq, reduceCtorEq] at hu
    subst hu
    rfl

theorem defaultVal_int (ts : List Validation.CTypeUse) :
    ∀ t : IntType, defaultVal? ((Validation.liftVal (.num (.int t))).substAll ts) =
      some (.num ⟨.int t, 0⟩)
  | .i32 => rfl
  | .i64 => rfl

theorem rel_init {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) (hpre : S.pre.den F ρ₀ ρ₀) :
    Rel F S (S.params ++ lts) ρ₀ s mi ρ₀ (initSt S lts) s
      (Frame.forCall mi (argsOf S ρ₀) code.locals) [] := by
  refine ⟨rfl, rfl, ?_, rfl, ?_, Agree.refl _ _, ?_⟩
  · simp only [Frame.forCall, initSt, locs, List.map_append, intTys?_eq hl, List.map_map]
    congr 1
    · apply List.ext_getElem (by simp [argsOf])
      intro j h₁ h₂
      simp [argsOf, SV.den_of, Tm.den]
    · apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply, defaultVal_int, SV.den_of, Tm.den]
      cases t <;> rfl
  · simp only [initSt, List.map_append, List.map_map]
    congr 1
    · apply List.ext_getElem (by simp)
      intro j h₁ h₂
      simp [SV.ty_of]
    · simp [Function.comp_def, SV.ty_of]
  · simpa [initSt] using hpre

/-! ## Outcomes -/

section Outcomes

variable {lt : List IntType} {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {a : Nat}
  {fi : FuncInst H} {n k : Nat} {f : Frame} {vs₀ : List Val} {s' : Store H} {F' : Frame}

/-- Falling through at the end of the body. -/
theorem bodyPostK_normal (hS : S.wellScoped = true) (hn : S.results.length = n) {vs : List Val}
    (h : Kc F S lt ρ₀ s mi (endVC S) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.normal vs) := by
  obtain ⟨ρ, σ, hR, hv⟩ := h
  unfold endVC at hv
  split at hv
  next hlen =>
    have hv' : AllValid F [vc σ (S.post.subst (σ.stack.take S.results.length).reverse)] := by
      simpa only [retVC, hlen, le_refl, ↓reduceIte] using hv
    obtain ⟨hs, -, -, hrs, -, hag, hpc⟩ := hR
    have hvs : vs = dens F ρ σ.stack.reverse := by
      rw [← List.reverse_reverse vs, hrs]
      simp [dens, List.map_reverse]
    have hpost := post_of_vc hS hag (vc_holds hv'.1 hpc)
    rw [← hlen, List.take_length, ← hvs] at hpost
    have hl : vs.length = S.results.length := by simp [hvs, dens, hlen]
    exact ⟨by simpa [hn] using hl, rfl, .inl ⟨vs, rfl, hs, vs, rfl, hl, hpost⟩⟩
  next => exact (not_bad hv (Rel.pc hR)).elim

/-- A `return`. -/
theorem bodyPostK_ret (hS : S.wellScoped = true) (hn : S.results.length = n) {vs : List Val}
    (h : Kc F S lt ρ₀ s mi (retVC S) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.ret vs) := by
  obtain ⟨ρ, σ, hR, hv⟩ := h
  unfold retVC at hv
  split at hv
  next hle =>
    obtain ⟨hs, -, -, hrs, -, hag, hpc⟩ := hR
    have hpost := post_of_vc hS hag (vc_holds hv.1 hpc)
    have hsplit : [] ++ vs = dens F ρ (σ.stack.drop S.results.length).reverse ++
        dens F ρ (σ.stack.take S.results.length).reverse := by
      rw [List.nil_append, ← List.reverse_reverse vs, hrs, dens, ← List.map_append,
        ← List.reverse_append, List.take_append_drop]
      simp [List.map_reverse]
    have hl : (dens F ρ (σ.stack.take S.results.length).reverse).length = S.results.length := by
      simp [dens, Nat.min_eq_left hle]
    exact ⟨_, _, hsplit, hn ▸ hl, rfl, .inl ⟨_, rfl, hs, _, rfl, hl, hpost⟩⟩
  next => exact (not_bad hv (Rel.pc hR)).elim

theorem bodyPostK_of_postOf (hS : S.wellScoped = true) (hn : S.results.length = n) {o : Outcome}
    (h : postOf F S lt ρ₀ s mi [] (endVC S) s' F' o) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F' o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact bodyPostK_normal hS hn h
  · simp [postOf] at h
  · exact bodyPostK_ret hS hn h
  all_goals exact h.elim

end Outcomes

/-! ## The theorem -/

/-- The body of a well-scoped specification, from the initial state. -/
theorem body_hwp {fuel : Nat} {fi : FuncInst H} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) (hS : S.wellScoped = true)
    (hvc : AllValid F (gen S (S.params ++ lts) fuel [] (endVC S) 0 code.body (initSt S lts)))
    {s : Store H} {ρ₀ : Env} (hp : S.pre.den F ρ₀ ρ₀) :
    HWP P host s (Frame.forCall fi.module (argsOf S ρ₀) code.locals) (expression code.body)
      (postOf F S (S.params ++ lts) ρ₀ s fi.module [] (endVC S)) := by
  have hb := gen_sound (P := P) (host := host) (ρ₀ := ρ₀) (s₀ := s) (m := fi.module) hS
    fuel [] (endVC S) 0 code.body (initSt S lts) ρ₀ s _ [] (rel_init hl hp) hvc
  simpa only [List.reverse_nil, vals, List.map_nil, List.nil_append] using hb

/-- **Soundness of the reflective generator for functions.** Valid conditions give the every-run
specification `fspec`: at every profile and for every host relation, a call with arguments
satisfying the precondition returns results satisfying the postcondition, without trapping and
leaving the store unchanged. -/
theorem genFunc_sound {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) :
    FSpecValid P host a (fspec F S a fi) := by
  have hff : ¬ AllValid F [.ff] := fun h => h.1 ⟨fun _ => 0, fun _ => 0⟩
  unfold genFunc at hvc
  split at hvc
  next lts hl =>
    split at hvc
    next hS =>
      intro n
      cases n with
      | zero => intro _ _ _ _ _ _ _; trivial
      | succ n =>
        refine FSpecAt.of_body (fun s args hpre => hpre.1) hcode he (fun s args hpre => ?_)
          fun s args hpre f vs₀ => ?_
        · obtain ⟨-, ρ₀, rfl, -⟩ := hpre
          simp [argsOf, hps]
        · obtain ⟨-, ρ₀, rfl, hp⟩ := hpre
          exact (body_hwp hl hS hvc hp n).post_mono fun _ _ _ h => bodyPostK_of_postOf hS hrs h
    next => exact (hff hvc).elim
  next => exact (hff hvc).elim

end Silmaril.Proofs.Wasm.Auto.VCGen