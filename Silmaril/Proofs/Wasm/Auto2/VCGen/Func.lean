module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Sound
public import Silmaril.Wasm.Auto.VCGen.Thms
public import Silmaril.Wasm.Examples.Common.Thms

/-!
# The VC generator with SSA names, memory and variants: function specifications

`genFunc_sound`: valid conditions `AllValid F (genFunc S code fuel)` give the every-run function
specification `fspec F S a fi` (`Silmaril.Wasm.Logic.Hoare.FSpecValid`), for every profile and
host relation; `genFunc_tsound`: with `S.total` (variant conditions) they give it for total
correctness (`Silmaril.Wasm.Logic.Hoare.TFSpecAt`). The body is started from `initSt` (`rel_init`: the entry environment `ρ₀` gives
the arguments and the memory at entry), `gen_sound` gives its every-run weakest precondition,
and `bodyPostK_of_postOf` reads the outcomes the generator allows as the caller's
postcondition (the final memory is the current memory variable).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP FSpecValid FSpecAt bodyPostK callPost Wp Corr TFSpecAt TSafe bodyPostT)
open Silmaril.Wasm.Auto.VCGen (numVal_inj intTy? intTys? intTys?_eq defaultVal_int)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec} {c : Corr}

/-! ## Arguments, memory and results -/

theorem agree_of_args {ρ ρ' : Env} (h : argsOf S ρ = argsOf S ρ') :
    ∀ i t, S.params[i]? = some t → ρ.get t i = ρ'.get t i := by
  intro i t hi
  have := congrArg (·[i]?) h
  simp only [argsOf, List.getElem?_mapIdx, hi, Option.map_some, Option.some.injEq,
    Val.num.injEq] at this
  exact numVal_inj this

theorem memOk_unique {s : Store H} {mi : ModuleInst} {B B' : ByteArray} (h : MemOk S s mi B)
    (h' : MemOk S s mi B') : B = B' := by
  by_cases hmem : S.mem = true
  · simp only [MemOk, hmem, ↓reduceIte] at h h'
    obtain ⟨ma, x, hm, hs, rfl⟩ := h
    obtain ⟨ma', x', hm', hs', rfl⟩ := h'
    rw [hm] at hm'
    cases hm'
    rw [hs] at hs'
    cases hs'
    rfl
  · simp only [MemOk, hmem, Bool.false_eq_true, ↓reduceIte] at h h'
    rw [h, h']

/-- Two environments of the same globals at entry agree on their variables. -/
theorem agree_of_globOk {s : Store H} {mi : ModuleInst} {ρ ρ' : Env} (h : GlobOk S s mi ρ)
    (h' : GlobOk S s mi ρ') :
    ∀ g t, S.globals[g]? = some t →
      ρ.get t (S.params.length + g) = ρ'.get t (S.params.length + g) := by
  intro g t hg
  obtain ⟨a, gi, ha, hs, hv⟩ := h.2 g t hg
  obtain ⟨a', gi', ha', hs', hv'⟩ := h'.2 g t hg
  have : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst this
  have : gi' = gi := Option.some.inj (hs'.symm.trans hs)
  subst this
  exact numVal_inj (Val.num.inj (hv.symm.trans hv'))

/-- Two environments of the same arguments, memory and globals at entry agree on the entry
variables. -/
theorem agree_ents {s : Store H} {mi : ModuleInst} {ρ ρ' : Env} (hargs : argsOf S ρ = argsOf S ρ')
    (hm : MemOk S s mi (ρ.mem 0)) (hm' : MemOk S s mi (ρ'.mem 0)) (hg : GlobOk S s mi ρ)
    (hg' : GlobOk S s mi ρ') : Agree S.ents ρ ρ' := by
  refine ⟨fun i t hi => ?_, memOk_unique hm hm'⟩
  rcases Nat.lt_or_ge i S.params.length with hlt | hge
  · rw [FnSpec.ents, List.getElem?_append_left hlt] at hi
    exact agree_of_args hargs i t hi
  · rw [FnSpec.ents, List.getElem?_append_right hge] at hi
    have := agree_of_globOk hg hg' (i - S.params.length) t hi
    rwa [Nat.add_sub_cancel' hge] at this

/-- The postcondition from its condition at the top values of the stack and the current
memory, for every environment of the same arguments, memory and globals at entry. -/
theorem post_of_vc (hS : S.wellScoped = true) {ρ ρ₀ : Env} {ls : List SV} {cm : Nat}
    {s : Store H} {mi : ModuleInst} (hag : Agree S.ents ρ ρ₀) (hm₀ : MemOk S s mi (ρ₀.mem 0))
    (hg₀ : GlobOk S s mi ρ₀) (hv : (S.post.subst ls cm).den F ρ ρ) :
    ∀ ρ', argsOf S ρ₀ = argsOf S ρ' → MemOk S s mi (ρ'.mem 0) → GlobOk S s mi ρ' →
      S.post.den F ρ' (valEnv (dens F ρ ls) (ρ.mem cm)) := by
  intro ρ' hargs hm' hg'
  have hsc : S.post.scoped S.ents = true := wellScoped_post hS
  rw [Fm.den_subst, locEnv_eq_valEnv] at hv
  exact (Fm.den_scoped (hag.trans (agree_ents hargs hm₀ hm' hg₀ hg')) _ _ hsc).mp hv

/-! ## The initial state -/

theorem upd_init' {s : Store H} {mi : ModuleInst} {B : ByteArray} (h : MemOk S s mi B) :
    s = upd S s mi B := by
  unfold MemOk at h
  unfold upd
  split at h
  next hm =>
    obtain ⟨ma, x, hma, hs, rfl⟩ := h
    simp only [hm, ↓reduceIte, setM_some hma hs]
    exact (setMem_self hs).symm
  next hm => simp [hm]

/-- The symbolic locals of the initial state: parameters and declared locals, then globals. -/
theorem initSt_locals (lts : List IntType) :
    (initSt S lts).locals = (S.params.mapIdx (fun i t => SV.of t (.var t i)) ++
      lts.map (fun t => SV.of t (.lit t 0))) ++
      S.globals.mapIdx (fun g t => SV.of t (.var t (S.params.length + g))) := rfl

theorem nl_init (lts : List IntType) :
    S.nl (S.params ++ lts ++ S.globals) = (S.params ++ lts).length := by
  simp only [FnSpec.nl, List.length_append]
  omega

theorem take_initSt (lts : List IntType) :
    (initSt S lts).locals.take (S.nl (S.params ++ lts ++ S.globals)) =
      S.params.mapIdx (fun i t => SV.of t (.var t i)) ++ lts.map (fun t => SV.of t (.lit t 0)) := by
  rw [initSt_locals, nl_init, List.take_left' (by simp)]

theorem drop_initSt (lts : List IntType) :
    (initSt S lts).locals.drop (S.nl (S.params ++ lts ++ S.globals)) =
      S.globals.mapIdx (fun g t => SV.of t (.var t (S.params.length + g))) := by
  rw [initSt_locals, nl_init, List.drop_left' (by simp)]

/-- The globals at entry, as values. -/
theorem upd_init {s : Store H} {mi : ModuleInst} {B : ByteArray} {ρ₀ : Env} {lts : List IntType}
    (h : MemOk S s mi B) (hg : GlobOk S s mi ρ₀) :
    s = setGs (upd S s mi B) mi
      (dens F ρ₀ ((initSt S lts).locals.drop (S.nl (S.params ++ lts ++ S.globals)))) := by
  rw [← upd_init' h, drop_initSt]
  refine (setGs_self fun g hg' => ?_).symm
  have hgl : g < S.globals.length := by simpa [dens] using hg'
  obtain ⟨a, gi, ha, hs, hv⟩ := hg.2 g S.globals[g] (List.getElem?_eq_getElem hgl)
  refine ⟨a, gi, ha, hs, ?_⟩
  simp [dens, hv, SV.den_of, Tm.den]

theorem locs_initSt {ρ₀ : Env} {mi : ModuleInst} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) :
    (Frame.forCall mi (argsOf S ρ₀) code.locals).locals =
      locs F ρ₀ ((initSt S lts).locals.take (S.nl (S.params ++ lts ++ S.globals))) := by
  rw [take_initSt]
  simp only [Frame.forCall, locs, List.map_append, intTys?_eq hl, List.map_map]
  congr 1
  · apply List.ext_getElem (by simp [argsOf])
    intro j h₁ h₂
    simp [argsOf, SV.den_of, Tm.den]
  · apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, defaultVal_int, SV.den_of, Tm.den]
    cases t <;> rfl

theorem types_initSt (lts : List IntType) :
    (initSt S lts).locals.map SV.ty = S.params ++ lts ++ S.globals := by
  simp only [initSt, List.map_append, List.map_map]
  congr 1
  · congr 1
    · apply List.ext_getElem (by simp)
      intro j h₁ h₂
      simp [SV.ty_of]
    · simp [Function.comp_def, SV.ty_of]
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp [SV.ty_of]

theorem locals_vlt_initSt (lts : List IntType) :
    ∀ v ∈ (initSt S lts).locals, v.vlt (initSt S lts).nv = true := by
  intro v hv
  have hv' : (v ∈ S.params.mapIdx (fun i t => SV.of t (.var t i)) ∨
      ∃ t ∈ lts, SV.of t (.lit t 0) = v) ∨
      v ∈ S.globals.mapIdx (fun g t => SV.of t (.var t (S.params.length + g))) := by
    simpa [initSt, or_assoc] using hv
  rcases hv' with (hv' | ⟨t, -, rfl⟩) | hv'
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv'
    have hj' : j < S.params.length := by simpa using hj
    simp only [List.getElem_mapIdx, SV.vlt_of, Tm.vlt, initSt, FnSpec.ents, List.length_append,
      decide_eq_true_eq]
    omega
  · simp [SV.vlt_of, Tm.vlt]
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv'
    have hj' : j < S.globals.length := by simpa using hj
    simp only [List.getElem_mapIdx, SV.vlt_of, Tm.vlt, initSt, FnSpec.ents, List.length_append,
      decide_eq_true_eq]
    omega

theorem fresh_initSt (hS : S.wellScoped = true) (lts : List IntType) :
    (initSt S lts).fresh = true := by
  have hpre : S.pre.scoped S.ents = true := wellScoped_pre hS
  have hpc : ∀ φ ∈ (initSt S lts).pc, φ.vlt (initSt S lts).nv = true := by
    intro φ hφ
    have hφ' : φ = S.preF := by simpa [initSt] using hφ
    rw [hφ']
    exact Fm.vlt_subst (by simp [initSt]) (by simp [initSt]) (by simp [initSt]) (by simp) _ hpre
  exact (fresh_iff _).mpr ⟨locals_vlt_initSt lts, by simp [initSt], hpc, by simp [initSt]⟩

theorem rel_init {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {code : Func} {lts : List IntType}
    (hS : S.wellScoped = true) (hl : intTys? code.locals = some lts)
    (hm : MemOk S s mi (ρ₀.mem 0)) (hg : GlobOk S s mi ρ₀) (hpre : S.preF.den F ρ₀ ρ₀) :
    Rel F S (S.params ++ lts ++ S.globals) ρ₀ s mi ρ₀ (initSt S lts) s
      (Frame.forCall mi (argsOf S ρ₀) code.locals) [] where
  store := upd_init hm hg
  memOk := hm
  globOk := hg
  glen := by simp only [List.length_append]; omega
  modl := rfl
  locals := locs_initSt hl
  stack := rfl
  types := types_initSt lts
  agree := Agree.refl _ _
  pc := by simpa [initSt] using hpre
  fresh := fresh_initSt hS lts
  pnv := by simp [initSt]
  pre := hpre

/-! ## Outcomes -/

section Outcomes

variable {lt : List IntType} {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {a : Nat}
  {fi : FuncInst H} {n k : Nat} {f : Frame} {vs₀ : List Val} {s' : Store H} {F' : Frame}

/-- The types of the globals of a related state. -/
theorem globs_valTy {ρ : Env} {σ : SSt} {s' : Store H} {F' : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s mi ρ σ s' F' rs) (hlt : lt.drop (S.nl lt) = S.globals) :
    (globs F S lt ρ σ).map valTy = S.globals.map some := by
  rw [← hlt, ← hR.types, ← List.map_drop]
  simp only [globs, dens, List.map_map]
  exact List.map_congr_left fun v _ => valTy_den ρ ρ v

/-- What a valid `retVC` gives at a related state. -/
theorem retVC_holds {ρ : Env} {σ : SSt} {s' : Store H} {F' : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s mi ρ σ s' F' rs) (hv : AllValid F (retVC S lt σ)) :
    S.results.length ≤ σ.stack.length ∧
      (dens F ρ (σ.stack.take S.results.length).reverse).map valTy = S.results.map some ∧
      (S.post.subst ((σ.stack.take S.results.length).reverse ++ σ.locals.drop (S.nl lt))
        σ.mem).den F ρ ρ := by
  unfold retVC at hv
  split at hv
  next hc =>
    refine ⟨hc.1, ?_, vc_holds hv.1 hR.pc⟩
    have hmap : ∀ l : List SV, (dens F ρ l).map valTy = (l.map SV.ty).map some := fun l => by
      simp only [dens, List.map_map]
      exact List.map_congr_left fun v _ => valTy_den ρ ρ v
    rw [hmap, hc.2]
  next => exact (not_bad hv hR.pc).elim

/-- The postcondition at a related state from a valid `retVC`, with the results (the top of the
stack) and the final globals. -/
theorem post_of_ret (hS : S.wellScoped = true) (hm₀ : MemOk S s mi (ρ₀.mem 0))
    (hg₀ : GlobOk S s mi ρ₀) {ρ : Env} {σ : SSt} {s' : Store H} {F' : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s mi ρ σ s' F' rs)
    (hv' : (S.post.subst ((σ.stack.take S.results.length).reverse ++ σ.locals.drop (S.nl lt))
        σ.mem).den F ρ ρ) :
    ∀ ρ', argsOf S ρ₀ = argsOf S ρ' → MemOk S s mi (ρ'.mem 0) → GlobOk S s mi ρ' →
      S.post.den F ρ' (valEnv (dens F ρ (σ.stack.take S.results.length).reverse ++
        globs F S lt ρ σ) (ρ.mem σ.mem)) := by
  intro ρ' ha hm hg
  have h := post_of_vc hS hR.agree hm₀ hg₀ hv' ρ' ha hm hg
  simpa only [dens, List.map_append] using h

/-- Falling through at the end of the body. -/
theorem bodyPostK_normal (hS : S.wellScoped = true) (hn : S.results.length = n)
    (hmi : fi.module = mi) (hm₀ : MemOk S s mi (ρ₀.mem 0)) (hg₀ : GlobOk S s mi ρ₀)
    (hlt : lt.drop (S.nl lt) = S.globals) {vs : List Val}
    {ρ : Env} {N : Nat} (h : Kc F S lt ρ₀ s mi ρ N (endVC S lt) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.normal vs) := by
  obtain ⟨ρ, σ, hR, -, -, hv⟩ := h
  unfold endVC at hv
  split at hv
  next hlen =>
    obtain ⟨-, htys, hv'⟩ := retVC_holds hR hv
    have hvs : vs = dens F ρ σ.stack.reverse := by
      rw [← List.reverse_reverse vs, hR.stack]
      simp [dens, List.map_reverse]
    have hpost := post_of_ret hS hm₀ hg₀ hR hv'
    rw [← hlen, List.take_length, ← hvs] at hpost
    rw [← hlen, List.take_length, ← hvs] at htys
    have hl : vs.length = S.results.length := by simp [hvs, dens, hlen]
    exact ⟨by simpa [hn] using hl, rfl,
      .inl ⟨vs, rfl, _, _, by rw [hmi]; exact hR.store, globs_valTy hR hlt, vs, rfl, hl, htys,
        by rw [hmi]; exact hpost⟩⟩
  next => exact (not_bad hv hR.pc).elim

/-- A `return`. -/
theorem bodyPostK_ret (hS : S.wellScoped = true) (hn : S.results.length = n)
    (hmi : fi.module = mi) (hm₀ : MemOk S s mi (ρ₀.mem 0)) (hg₀ : GlobOk S s mi ρ₀)
    (hlt : lt.drop (S.nl lt) = S.globals) {vs : List Val}
    {ρ : Env} {N : Nat} (h : Kc F S lt ρ₀ s mi ρ N (retVC S lt) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.ret vs) := by
  obtain ⟨ρ, σ, hR, -, -, hv⟩ := h
  obtain ⟨hle, htys, hv'⟩ := retVC_holds hR hv
  have hpost := post_of_ret hS hm₀ hg₀ hR hv'
  have hsplit : [] ++ vs = dens F ρ (σ.stack.drop S.results.length).reverse ++
      dens F ρ (σ.stack.take S.results.length).reverse := by
    rw [List.nil_append, ← List.reverse_reverse vs, hR.stack, dens, ← List.map_append,
      ← List.reverse_append, List.take_append_drop]
    simp [List.map_reverse]
  have hl : (dens F ρ (σ.stack.take S.results.length).reverse).length = S.results.length := by
    simp [dens, Nat.min_eq_left hle]
  exact ⟨_, _, hsplit, hn ▸ hl, rfl,
    .inl ⟨_, rfl, _, _, by rw [hmi]; exact hR.store, globs_valTy hR hlt, _, rfl, hl, htys,
      by rw [hmi]; exact hpost⟩⟩

theorem bodyPostK_of_postOf (hS : S.wellScoped = true) (hn : S.results.length = n)
    (hmi : fi.module = mi) (hm₀ : MemOk S s mi (ρ₀.mem 0)) (hg₀ : GlobOk S s mi ρ₀)
    (hlt : lt.drop (S.nl lt) = S.globals) {o : Outcome} {ρ : Env} {N : Nat}
    (h : postOf F S lt ρ₀ s mi c ρ N [] (endVC S lt) s' F' o) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F' o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · exact bodyPostK_normal hS hn hmi hm₀ hg₀ hlt h
  · simp [postOf] at h
  · exact bodyPostK_ret hS hn hmi hm₀ hg₀ hlt h
  all_goals exact h.elim

/-- The same outcomes, seen through the total-correctness body postcondition. -/
theorem bodyPostT_of_postOf (hS : S.wellScoped = true) (hn : S.results.length = n)
    (hmi : fi.module = mi) (hm₀ : MemOk S s mi (ρ₀.mem 0)) (hg₀ : GlobOk S s mi ρ₀)
    (hlt : lt.drop (S.nl lt) = S.globals) {o : Outcome} {ρ : Env} {N : Nat}
    (h : postOf F S lt ρ₀ s mi c ρ N [] (endVC S lt) s' F' o) :
    bodyPostT P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) s' F' o := by
  have h' := bodyPostK_of_postOf (P := P) (host := host) (a := a) (f := f) (vs₀ := vs₀) (k := 0)
    hS hn hmi hm₀ hg₀ hlt h
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · simpa [bodyPostT, bodyPostK, Silmaril.Wasm.Logic.Hoare.labelPostT,
      Silmaril.Wasm.Logic.Hoare.labelPostK, Silmaril.Wasm.Logic.Hoare.framePostT,
      Silmaril.Wasm.Logic.Hoare.framePostK] using h'
  · simp [postOf] at h
  · simpa [bodyPostT, bodyPostK, Silmaril.Wasm.Logic.Hoare.labelPostT,
      Silmaril.Wasm.Logic.Hoare.labelPostK, Silmaril.Wasm.Logic.Hoare.framePostT,
      Silmaril.Wasm.Logic.Hoare.framePostK] using h'
  all_goals exact h.elim

end Outcomes

/-! ## The theorem -/

/-- The body of a well-scoped specification, from the initial state. -/
theorem body_wp {fuel : Nat} {fi : FuncInst H} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) (hS : S.wellScoped = true)
    (hT : c = .total → S.total = true)
    (hvc : AllValid F (gen S (S.params ++ lts ++ S.globals) fuel []
      (endVC S (S.params ++ lts ++ S.globals)) 0 code.body (initSt S lts)))
    {s : Store H} {ρ₀ : Env} (hC : CallsOK c P host F S s fi.module)
    (hm : MemOk S s fi.module (ρ₀.mem 0)) (hg : GlobOk S s fi.module ρ₀)
    (hp : S.preF.den F ρ₀ ρ₀) :
    Wp c P host s (Frame.forCall fi.module (argsOf S ρ₀) code.locals) (expression code.body)
      (postOf F S (S.params ++ lts ++ S.globals) ρ₀ s fi.module c ρ₀ (initSt S lts).nv []
        (endVC S (S.params ++ lts ++ S.globals))) := by
  have hb := gen_sound (P := P) (host := host) (ρ₀ := ρ₀) (s₀ := s) (m := fi.module) hS hT hC
    fuel [] (endVC S (S.params ++ lts ++ S.globals)) 0 code.body (initSt S lts) ρ₀ s _ []
    (rel_init hS hl hm hg hp)
    (fun _ _ _ _ _ _ h => by simp at h) hvc
  simpa only [List.reverse_nil, vals, List.map_nil, List.nil_append] using hb

/-- The callees' specifications hold (for every instance running their code), in reading `c`:
the hypothesis of `genFunc_sound` and `genFunc_tsound` (vacuous without callees). -/
def CalleesValid (c : Corr) (P : Profile) (host : HostSemantics H) (F : Fns) (S : FnSpec) :
    Prop :=
  ∀ e ∈ S.calls, ∀ a' (fi' : FuncInst H) (ps' rs' : Ty (.list .val)), fi'.code = .wasm e.2.2 →
    Expand fi'.type (.func ps' rs') → e.2.1.params.length = ps'.length →
    e.2.1.results.length = rs'.length → SpecOK c P host a' (fspec F e.2.1 a' fi')

theorem callsOK_of {fi : FuncInst H} {s : Store H} (hC : CalleesValid c P host F S)
    (h : Callees S fi s) : CallsOK c P host F S s fi.module := by
  intro e he
  obtain ⟨a', fi', ps', rs', hx, hf, hcode, hmod, hE, hp, hr⟩ := h e he
  exact ⟨a', fi', hx, hf, hmod, (hC e he a' fi' ps' rs' hcode hE hp hr).fspecIn s⟩

theorem drop_lt_init (lts : List IntType) :
    (S.params ++ lts ++ S.globals).drop (S.nl (S.params ++ lts ++ S.globals)) = S.globals := by
  rw [nl_init, List.drop_left' rfl]

theorem not_allValid_ff : ¬ AllValid F [.ff] := fun h => h.1 ⟨fun _ => 0, fun _ => 0, fun _ => .empty⟩

/-- **Soundness of the generator for functions.** Valid conditions give the every-run
specification `fspec`: at every profile and for every host relation, a call with arguments and
memory satisfying the precondition returns results (of the declared types) and a final memory
satisfying the postcondition, without trapping; the store changes only in memory `0`'s bytes
(partial correctness). The callees' specifications are assumed (`CalleesValid .part`; for a
function without callees, `by simp`). -/
theorem genFunc_sound {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) (hC : CalleesValid .part P host F S) :
    FSpecValid P host a (fspec F S a fi) := by
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
        · obtain ⟨-, -, ρ₀, rfl, -⟩ := hpre
          simp [argsOf, hps]
        · obtain ⟨-, hcs, ρ₀, rfl, hm, hg, hp⟩ := hpre
          exact (body_wp (c := .part) hl hS (fun h => by cases h) hvc (callsOK_of hC hcs) hm hg hp
            n).post_mono fun _ _ _ h => bodyPostK_of_postOf hS hrs rfl hm hg (drop_lt_init lts) h
    next => exact (not_allValid_ff hvc).elim
  next => exact (not_allValid_ff hvc).elim

/-- **Total correctness.** With the variant conditions (`S.total`), valid conditions give `fspec`
for total correctness: every run of the call terminates, with the outcome `genFunc_sound`
describes. The callees' specifications are assumed for total correctness
(`CalleesValid .total`). -/
theorem genFunc_tsound {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hT : S.total = true) (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) (hC : CalleesValid .total P host F S) :
    TFSpecAt P host a (fspec F S a fi) := by
  unfold genFunc at hvc
  split at hvc
  next lts hl =>
    split at hvc
    next hS =>
      refine Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body (fun s args hpre => hpre.1) hcode he
        (fun s args hpre => ?_) fun s args hpre f vs₀ => ?_
      · obtain ⟨-, -, ρ₀, rfl, -⟩ := hpre
        simp [argsOf, hps]
      · obtain ⟨-, hcs, ρ₀, rfl, hm, hg, hp⟩ := hpre
        exact TSafe.post_mono (body_wp (c := .total) hl hS (fun _ => hT) hvc (callsOK_of hC hcs)
          hm hg hp) fun _ _ _ h => bodyPostT_of_postOf hS hrs rfl hm hg (drop_lt_init lts) h
    next => exact (not_allValid_ff hvc).elim
  next => exact (not_allValid_ff hvc).elim

end Silmaril.Wasm.Auto2.VCGen
