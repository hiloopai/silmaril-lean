module

public import Silmaril.Proofs.Wasm.Component.Reference.MapBack

/-!
# Shared runs from an image are images of part runs

The importer of a `Linked2` runs in its own store `u`; its image in the shared store `σ` is
`linkC s₀ ρ σ` (relocation past the exporter's store `s₀`, then the renaming `ρ` of GC
addresses, `SplitLink`). `step_link` is the forward simulation. This file proves the backward
one, for every profile, by confluence as in `Linking.Split.GameSub`:

* `decompose?_link`: a host-call redex of the part is a redex of the image (callee shifted
  past `s₀`, same host code, arguments and context mapped), given that the relocated part's
  functions are functions of the shared store (`FnPre`);
* `LinkSt s₀ ρ O x y`: the shared thread `y` (store and thread) is the image of the part thread
  `x`, related by `ImpRel`, with `FnPre`;
* `part_cases`: a typed part thread has returned values, trapped, stopped at a host call, or
  has an internal step (`statusP_ne_stuck`; uncaught exceptions are impossible in the split
  fragment);
* `internal_link_back`: when the part has an internal step, every internal step of the image
  is the image of an internal step of the part (the forward image by `step_link`, or a `Soft`
  step, `Choice.eq_or_soft`, replayed by `link_soft_back`);
* `reach_link_back`: every host-free run of the shared store from the image of a typed part
  thread is the image of a host-free run of the part, the renaming and ownership grown along
  it (`Grow`) and the shared store touched only at what the part owns (`Touch`);
* `link_values`, `link_trap`, `link_callout`, `link_running`: the image of a finished, trapped,
  stopped or running part is finished, trapped, stopped (at the mapped redex) or running;
  conversely (`values_back`, `trap_back`, `callout_back`) for the image of a typed part.

The exporter's part is the case of the empty prefix (`s₀ = {}`): the identity shift.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch noHost)
open Silmaril.Wasm.Game (InternalP statusP)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Contexts -/

namespace CMap

variable (M : CMap)

/-- The map of an evaluation context. -/
def ctx : Ctx → Ctx
  | .top pre rest => .top (pre.map M.val) (M.code rest)
  | .label pre n cont E rest => .label (pre.map M.val) n cont (ctx E) (M.code rest)
  | .handler pre n cs E rest => .handler (pre.map M.val) n cs (ctx E) (M.code rest)
  | .frame pre n f E rest => .frame (pre.map M.val) n (M.frame f) (ctx E) (M.code rest)

theorem code_fill (xs : List Admin) : ∀ E : Ctx, M.code (E.fill xs) = (M.ctx E).fill (M.code xs)
  | .top pre rest => by simp [Ctx.fill, ctx]
  | .label pre n cont E rest => by simp [Ctx.fill, ctx, code_fill xs E]
  | .handler pre n cs E rest => by simp [Ctx.fill, ctx, code_fill xs E]
  | .frame pre n f E rest => by simp [Ctx.fill, ctx, code_fill xs E]

theorem code_callRef {c : Admin} (hc : c.IsCallRef) (l : List Admin) :
    M.code (c :: l) = c :: M.code l := by
  cases c <;> simp_all [Admin.IsCallRef]

end CMap

/-! ## The importer's map -/

/-- The importer's code map into the shared store: the relocation past `s₀`, then `ρ`. -/
def linkMap (s₀ : Store H) (ρ : Ren) : CMap := (renMap ρ).comp (shiftMap (sh s₀))

theorem linkC_eq (s₀ : Store H) (ρ : Ren) (σ : Store H) (c : Config H) :
    linkC s₀ ρ σ c = ⟨σ, (linkMap s₀ ρ).frame c.frame, (linkMap s₀ ρ).code c.code⟩ := by
  simp only [linkC, linkMap, CMap.code_comp, ← code_ren, ← code_shift]
  rfl

theorem linkMap_func (s₀ : Store H) (ρ : Ren) (a : Nat) :
    (linkMap s₀ ρ).ref (.func a) = .func (s₀.funcs.length + a) := rfl

/-- **The functions of the relocated part are functions of the shared store.** -/
def FnPre (s₀ σ u : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H), (reloc s₀ u).funcs[a]? = some fi → σ.funcs[a]? = some fi

theorem fnPre_refl (s₀ u : Store H) : FnPre s₀ (reloc s₀ u) u := fun _ _ h => h

theorem FnPre.congr {s₀ σ σ' u u' : Store H} (h : FnPre s₀ σ u) (hσ : σ'.funcs = σ.funcs)
    (hu : u'.funcs = u.funcs) : FnPre s₀ σ' u' := by
  intro a fi ha
  rw [hσ]
  exact h a fi (by simpa [hu] using ha)

/-- **Host-call redexes of the part are redexes of the image.** -/
theorem decompose?_link {s₀ σ u : Store H} (ρ : Ren) (hF : FnPre s₀ σ u) {X : List Admin}
    {E : Ctx} {a : Nat} {h : H} {args : List Val} (hd : decompose? u X = some (E, a, h, args)) :
    decompose? σ ((linkMap s₀ ρ).code X) =
      some ((linkMap s₀ ρ).ctx E, s₀.funcs.length + a, h, args.map (linkMap s₀ ρ).val) := by
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, rfl⟩ := decompose?_sound hd
  have hf' : σ.funcs[s₀.funcs.length + a]? = some ((sh s₀).finst fi) :=
    hF _ _ (funcs_reloc_of s₀ hf)
  have hfill : (linkMap s₀ ρ).code (E.fill (vals args ++ [.ref (.func a), yy])) =
      ((linkMap s₀ ρ).ctx E).fill (vals (args.map (linkMap s₀ ρ).val) ++
        [.ref (.func (s₀.funcs.length + a)), yy]) := by
    rw [CMap.code_fill, CMap.code_append, CMap.code_vals, CMap.code_ref,
      CMap.code_callRef _ hyy, CMap.code_nil, linkMap_func]
  rw [hfill]
  exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ hyy hf' he (by simpa using hn) hcode

/-! ## Related threads -/

/-- **The shared thread `y` is the image of the part thread `x`**: its configuration is
`linkC` of the part's, the part is related by `ImpRel` along `ρ` for `O`, and the relocated
part's functions are functions of the shared store. -/
structure LinkSt (s₀ : Store H) (ρ : Ren) (O : Own) (x y : Store H × Thread) : Prop where
  cfg : y.2.config y.1 = linkC s₀ ρ y.1 (x.2.config x.1)
  rel : ImpRel s₀ ρ O y.1 (x.2.config x.1)
  fn : FnPre s₀ y.1 x.1

section Thread

variable {P : Profile} {s₀ : Store H} {ρ : Ren} {O : Own} {x y : Store H × Thread}

theorem LinkSt.code (hL : LinkSt s₀ ρ O x y) :
    (y.2.config y.1).code = (linkMap s₀ ρ).code (x.2.config x.1).code := by
  rw [hL.cfg, linkC_eq]

/-- The image of a finished part is finished. -/
theorem link_values (hL : LinkSt s₀ ρ O x y) {vs : List Val}
    (h : (x.2.config x.1).code = vals vs) :
    (y.2.config y.1).code = vals (vs.map (linkMap s₀ ρ).val) := by
  rw [hL.code, h, CMap.code_vals]

/-- The image of a trapped part is trapped. -/
theorem link_trap (hL : LinkSt s₀ ρ O x y) (h : (x.2.config x.1).code = [.trap]) :
    (y.2.config y.1).code = [.trap] := by
  rw [hL.code, h]
  simp

/-- The image of a part stopped at a host call is stopped at the mapped redex. -/
theorem link_callout (hL : LinkSt s₀ ρ O x y) {E : Ctx} {a : Nat} {h : H} {args : List Val}
    (hd : decompose? x.1 (x.2.config x.1).code = some (E, a, h, args)) :
    decompose? y.1 (y.2.config y.1).code =
      some ((linkMap s₀ ρ).ctx E, s₀.funcs.length + a, h, args.map (linkMap s₀ ρ).val) := by
  rw [hL.code]
  exact decompose?_link ρ hL.fn hd

/-- An internal step of a related part is an internal step of the image. -/
theorem internal_link (hL : LinkSt s₀ ρ O x y) {x₁ : Store H × Thread}
    (hx : InternalP P x x₁) :
    ∃ y₁ ρ' O', InternalP P y y₁ ∧ LinkSt s₀ ρ' O' x₁ y₁ ∧ Grow ρ O ρ' O' y.1 ∧
      Touch ρ O y.1 y₁.1 := by
  obtain ⟨f₁, c₁, hx₁, hst⟩ := hx
  have hst' : Step P noHost (x.2.config x.1) ⟨x₁.1, f₁, c₁⟩ := hst
  obtain ⟨ρ', O', σ', hs, hR', hg, ht⟩ := step_link s₀ hst' hL.rel
  have hc₁ : x₁.2.config x₁.1 = ⟨x₁.1, f₁, c₁⟩ := by rw [hx₁]; rfl
  have hfx : x₁.1.funcs = x.1.funcs := Silmaril.Proofs.Wasm.Game.InternalP.funcs_prefix (P := P) (s := x.1) (t := x.2)
    (t' := x₁.2) ⟨f₁, c₁, hx₁, hst⟩
  refine ⟨(σ', .active ((linkC s₀ ρ' σ' ⟨x₁.1, f₁, c₁⟩).frame)
      (linkC s₀ ρ' σ' ⟨x₁.1, f₁, c₁⟩).code), ρ', O', ⟨_, _, rfl, ?_⟩, ⟨?_, ?_, ?_⟩, hg, ht⟩
  · rw [hL.cfg]
    exact hs
  · rw [hc₁]
    rfl
  · rw [hc₁]
    exact hR'
  · exact hL.fn.congr ht.funcs hfx

end Thread

/-! ## Progress of the part -/

/-- **A typed part thread is finished, trapped, stopped at a host call or running** (an
uncaught exception would need an exception reference in good code). -/
theorem part_cases {P : Profile} {s₀ : Store H} {ρ : Ren} {O : Own} {x y : Store H × Thread}
    (hL : LinkSt s₀ ρ O x y) {ts : List CValType} (hs : StoreOk x.1) (ht : ThreadOk x.1 x.2 ts) :
    (∃ vs, (x.2.config x.1).code = vals vs) ∨ (x.2.config x.1).code = [.trap] ∨
      (∃ E a h args, decompose? x.1 (x.2.config x.1).code = some (E, a, h, args)) ∨
      ∃ x₁, InternalP P x x₁ := by
  have hns : statusP P x.1 x.2 ≠ .stuck := Silmaril.Proofs.Wasm.Game.statusP_ne_stuck hs ht
  cases hstat : statusP P x.1 x.2 with
  | returned cr =>
    cases cr with
    | values vs => exact .inl ⟨vs, Silmaril.Proofs.Wasm.Game.statusP_returned_values hstat⟩
    | trap =>
      rcases Silmaril.Proofs.Wasm.Game.statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact .inr (.inl h)
      · exfalso
        obtain ⟨ρ₀, O₀, σ₀, -, -, hc₀⟩ := hL.rel.good
        exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.not_codeGood_throwing (a := a) hc₀
          (by rw [h]; simp [throwing])
  | stuck => exact absurd hstat hns
  | running => exact .inr (.inr (.inr (Silmaril.Proofs.Wasm.Game.statusP_running_inv hstat)))
  | callout h args =>
    obtain ⟨E, a, hd⟩ := Silmaril.Proofs.Wasm.Game.statusP_callout_inv hstat
    exact .inr (.inr (.inl ⟨E, a, h, args, hd⟩))

/-! ## The backward simulation -/

section Back

variable {P : Profile} {s₀ : Store H}

/-- A `Soft` internal step of the image goes back to an internal step of the part, in the same
shared store, with the same renaming and ownership. -/
theorem internal_soft_back {ρ : Ren} {O : Own} {x y y' : Store H × Thread}
    (hL : LinkSt s₀ ρ O x y) {f' : Frame} {code' : List Admin} (hy' : y'.2 = .active f' code')
    (hsoft : Silmaril.Proofs.Wasm.Game.Choice.Soft P (linkC s₀ ρ y.1 (x.2.config x.1)) ⟨y'.1, f', code'⟩) :
    ∃ x', InternalP P x x' ∧ LinkSt s₀ ρ O x' y' ∧ y'.1 = y.1 := by
  obtain ⟨X', hX', hd, hR'⟩ := link_soft_back s₀ hL.rel hsoft
  have hstep : Step P noHost (x.2.config x.1) ⟨x.1, (x.2.config x.1).frame, X'⟩ := by
    simpa only [Thread.config_store] using hX'.step
  have hσ : y'.1 = y.1 := congrArg Config.store hd
  have hcfg : (x.1, Thread.active (x.2.config x.1).frame X').2.config x.1 =
      ⟨(x.2.config x.1).store, (x.2.config x.1).frame, X'⟩ := by
    rw [Thread.config_store]
    rfl
  have hy'c : y'.2.config y'.1 = ⟨y'.1, f', code'⟩ := by rw [hy']; rfl
  have hlk : linkC s₀ ρ y.1 ⟨(x.2.config x.1).store, (x.2.config x.1).frame, X'⟩ =
      linkC s₀ ρ y'.1 ⟨(x.2.config x.1).store, (x.2.config x.1).frame, X'⟩ := by rw [hσ]
  have hR'' : ImpRel s₀ ρ O y'.1 ⟨(x.2.config x.1).store, (x.2.config x.1).frame, X'⟩ := by
    rw [hσ]
    exact hR'
  refine ⟨(x.1, .active (x.2.config x.1).frame X'), ⟨_, _, rfl, hstep⟩, ⟨?_, ?_, ?_⟩, hσ⟩
  · rw [hcfg]
    exact hy'c.trans (hd.trans hlk)
  · rw [hcfg]
    exact hR''
  · rw [hσ]
    exact hL.fn

/-- **An internal step of the image of a running part is the image of an internal step of the
part.** -/
theorem internal_link_back {ρ : Ren} {O : Own} {x y y' : Store H × Thread}
    (hL : LinkSt s₀ ρ O x y) {x₁ : Store H × Thread} (hx : InternalP P x x₁)
    (hy : InternalP P y y') :
    ∃ x' ρ' O', InternalP P x x' ∧ LinkSt s₀ ρ' O' x' y' ∧ Grow ρ O ρ' O' y.1 ∧
      Touch ρ O y.1 y'.1 := by
  obtain ⟨y₁, ρ₁, O₁, hy₁, hL₁, hg₁, ht₁⟩ := internal_link hL hx
  obtain ⟨f', code', hy', hst⟩ := hy
  obtain ⟨f₁, code₁, hy₁', hst₁⟩ := hy₁
  rcases Silmaril.Proofs.Wasm.Game.Choice.eq_or_soft hst₁ hst with he | hsoft
  · have hyy : y' = y₁ := by
      obtain ⟨h1, h2, h3⟩ := Config.mk.inj he
      exact Prod.ext h1 (by rw [hy', hy₁', h2, h3])
    exact ⟨x₁, ρ₁, O₁, hx, hyy ▸ hL₁, hg₁, hyy ▸ ht₁⟩
  · have hsoft' : Silmaril.Proofs.Wasm.Game.Choice.Soft P (linkC s₀ ρ y.1 (x.2.config x.1)) ⟨y'.1, f', code'⟩ :=
      hL.cfg ▸ hsoft
    obtain ⟨x', hx', hL', hσ⟩ := internal_soft_back hL hy' hsoft'
    exact ⟨x', ρ, O, hx', hL', Grow.refl ρ O y.1, hσ ▸ Touch.refl ρ O y.1⟩

/-- Images of finished, trapped or stopped parts take no internal step. -/
theorem link_no_internal {ρ : Ren} {O : Own} {x y y' : Store H × Thread}
    (hL : LinkSt s₀ ρ O x y)
    (hc : (∃ vs, (x.2.config x.1).code = vals vs) ∨ (x.2.config x.1).code = [.trap] ∨
      (∃ E a h args, decompose? x.1 (x.2.config x.1).code = some (E, a, h, args)))
    (hy : InternalP P y y') : False := by
  obtain ⟨f', code', -, hst⟩ := hy
  rcases hc with ⟨vs, h⟩ | h | ⟨E, a, h, args, hd⟩
  · exact Step.not_quiet hst (by rw [link_values hL h]; exact quiet_vals _)
  · exact Step.not_quiet hst (by rw [link_trap hL h]; exact quiet_trap)
  · have hn := decompose?_none_of_noRedex (Step.noRedex hst)
    rw [Thread.config_store, link_callout hL hd] at hn
    cases hn

/-- **Shared runs from the image of a typed part are images of part runs**: the renaming and
ownership grow along the run (`Grow`), the shared store is touched only at what the part owns
(`Touch`), and the part stays typed. -/
theorem reach_link_back {ts : List CValType} {y y' : Store H × Thread}
    (run : Relation.ReflTransGen (InternalP P) y y') :
    ∀ {x : Store H × Thread} {ρ : Ren} {O : Own}, LinkSt s₀ ρ O x y → StoreOk x.1 →
      ThreadOk x.1 x.2 ts →
      ∃ x' ρ' O', Relation.ReflTransGen (InternalP P) x x' ∧ LinkSt s₀ ρ' O' x' y' ∧
        Grow ρ O ρ' O' y.1 ∧ Touch ρ O y.1 y'.1 ∧ StoreOk x'.1 ∧ ThreadOk x'.1 x'.2 ts := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro x ρ O hL hs ht
    exact ⟨x, ρ, O, .refl, hL, Grow.refl ρ O _, Touch.refl ρ O _, hs, ht⟩
  | @head y y₁ hy _ ih =>
    intro x ρ O hL hs ht
    rcases part_cases (P := P) hL hs ht with h | h | h | ⟨x₁, hx⟩
    · exact (link_no_internal hL (.inl h) hy).elim
    · exact (link_no_internal hL (.inr (.inl h)) hy).elim
    · exact (link_no_internal hL (.inr (.inr h)) hy).elim
    obtain ⟨x₂, ρ₂, O₂, hx₂, hL₂, hg₂, ht₂⟩ := internal_link_back hL hx hy
    have hx₂' : InternalP P (x.1, x.2) (x₂.1, x₂.2) := hx₂
    obtain ⟨hs₂, htc₂, -⟩ := Silmaril.Proofs.Wasm.Game.InternalP.preserves hs ht hx₂'
    obtain ⟨x', ρ', O', hrun, hL', hg', ht', hs', htc'⟩ := ih hL₂ hs₂ htc₂
    exact ⟨x', ρ', O', .head hx₂ hrun, hL', hg₂.trans hg' ht₂.structs_len ht₂.arrays_len,
      ht₂.trans hg₂ ht', hs', htc'⟩

/-! ## Conversely: stopped images come from stopped parts -/

variable {ρ : Ren} {O : Own} {x y : Store H × Thread} {ts : List CValType}

theorem vals_ne_trap' (ws : List Val) : vals ws ≠ [.trap] := fun h =>
  Det.mem_vals (by rw [h]; simp : Admin.trap ∈ vals ws) rfl

/-- A finished image of a typed part is the image of a finished part. -/
theorem values_back (P : Profile) (hL : LinkSt s₀ ρ O x y) (hs : StoreOk x.1) (ht : ThreadOk x.1 x.2 ts)
    {ws : List Val} (h : (y.2.config y.1).code = vals ws) :
    ∃ vs, (x.2.config x.1).code = vals vs ∧ vs.map (linkMap s₀ ρ).val = ws := by
  rcases part_cases (P := P) hL hs ht with ⟨vs, hv⟩ | htr | ⟨E, a, hh, args, hd⟩ | ⟨x₁, hx⟩
  · refine ⟨vs, hv, vals_injective ?_⟩
    rw [← link_values hL hv, h]
  · exact absurd (h.symm.trans (link_trap hL htr)) (vals_ne_trap' ws)
  · have hq : Quiet (y.2.config y.1).code := by rw [h]; exact quiet_vals ws
    have hd' := link_callout hL hd
    rw [h] at hd'
    rw [decompose?_vals_nil] at hd'
    cases hd'
  · obtain ⟨y₁, -, -, hy₁, -, -, -⟩ := internal_link hL hx
    obtain ⟨f', code', -, hst⟩ := hy₁
    exact absurd (by rw [h]; exact quiet_vals ws) (Step.not_quiet hst)

theorem decompose?_trap (s : Store H) : decompose? s [.trap] = none := by
  have hs : splitVals [Admin.trap] = ([], [.trap]) := splitVals_cons_nonval rfl []
  rw [decompose?_of_split hs]
  rfl

/-- A trapped image of a typed part is the image of a trapped part. -/
theorem trap_back (P : Profile) (hL : LinkSt s₀ ρ O x y) (hs : StoreOk x.1)
    (ht : ThreadOk x.1 x.2 ts) (h : (y.2.config y.1).code = [.trap]) :
    (x.2.config x.1).code = [.trap] := by
  rcases part_cases (P := P) hL hs ht with ⟨vs, hv⟩ | htr | ⟨E, a, hh, args, hd⟩ | ⟨x₁, hx⟩
  · exact absurd ((link_values hL hv).symm.trans h) (vals_ne_trap' _)
  · exact htr
  · have hd' := link_callout hL hd
    rw [h, decompose?_trap] at hd'
    cases hd'
  · obtain ⟨y₁, -, -, hy₁, -, -, -⟩ := internal_link hL hx
    obtain ⟨f', code', -, hst⟩ := hy₁
    exact absurd (by rw [h]; exact quiet_trap) (Step.not_quiet hst)

/-- An image of a typed part stopped at a host call is the image of a part stopped at the
corresponding redex. -/
theorem callout_back (P : Profile) (hL : LinkSt s₀ ρ O x y) (hs : StoreOk x.1)
    (ht : ThreadOk x.1 x.2 ts) {E' : Ctx} {a' : Nat} {h : H} {args' : List Val}
    (hd : decompose? y.1 (y.2.config y.1).code = some (E', a', h, args')) :
    ∃ E a args, decompose? x.1 (x.2.config x.1).code = some (E, a, h, args) ∧
      E' = (linkMap s₀ ρ).ctx E ∧ a' = s₀.funcs.length + a ∧
      args' = args.map (linkMap s₀ ρ).val := by
  rcases part_cases (P := P) hL hs ht with ⟨vs, hv⟩ | htr | ⟨E, a, hh, args, hdx⟩ | ⟨x₁, hx⟩
  · rw [link_values hL hv, decompose?_vals_nil] at hd
    cases hd
  · rw [link_trap hL htr, decompose?_trap] at hd
    cases hd
  · have hd' := (link_callout hL hdx).symm.trans hd
    obtain ⟨rfl, rfl, rfl, rfl⟩ : (linkMap s₀ ρ).ctx E = E' ∧ s₀.funcs.length + a = a' ∧ hh = h ∧
        args.map (linkMap s₀ ρ).val = args' := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hd'
    exact ⟨E, a, args, hdx, rfl, rfl, rfl⟩
  · obtain ⟨y₁, -, -, hy₁, -, -, -⟩ := internal_link hL hx
    obtain ⟨f', code', -, hst⟩ := hy₁
    have hn := decompose?_none_of_noRedex (Step.noRedex hst)
    rw [Thread.config_store, hd] at hn
    cases hn

end Back

/-! ## The initial relation -/

/-- **The initial relation**: a typed thread of a good store `u` in the split fragment, its
image in `reloc s₀ u` by the identity renaming. -/
theorem linkSt_init (s₀ : Store H) {u : Store H} (hg : StoreGood u) {f : Frame} {l : List Admin}
    (hf : (ownOf u).FrameGood f) (hc : (ownOf u).CodeGood l) :
    LinkSt s₀ Ren.id (shOwn (sh s₀) (ownOf u)) (u, .active f l)
      (reloc s₀ u, .active (linkC s₀ Ren.id (reloc s₀ u) ⟨u, f, l⟩).frame
        (linkC s₀ Ren.id (reloc s₀ u) ⟨u, f, l⟩).code) where
  cfg := rfl
  rel := impRel_init s₀ hg hf hc
  fn := fnPre_refl s₀ u

/-- Scalar values are fixed by maps fixing numbers and vectors. -/
theorem map_val_scalar (g : Val → Val) (hn : ∀ n, g (.num n) = .num n)
    (hv : ∀ b, g (.vec b) = .vec b) {vs : List Val} (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) :
    vs.map g = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hgv : g v = v := by
      cases v with
      | ref r => exact absurd rfl (hvs _ List.mem_cons_self r)
      | num n => exact hn n
      | vec b => exact hv b
    rw [List.map_cons, hgv, ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw))]

theorem codeGood_scalar {O : Own} {vs : List Val} (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) :
    O.CodeGood (vals vs) := by
  refine O.codeGood_vals.mpr fun v hv => ?_
  cases v with
  | ref r => exact absurd rfl (hvs _ hv r)
  | num => trivial
  | vec => trivial

/-- **The invocation of a function of the part**: the invocation of the shifted function on the
same scalar arguments in the shared store is the image of the part's invocation. -/
theorem linkSt_invoke {s₀ σ u : Store H} {ρ : Ren} {O : Own} (hR : PartRel ρ O (reloc s₀ u) σ)
    (hF : FnPre s₀ σ u) {a : Nat} (ha : a < u.funcs.length) (hO : O.fn (s₀.funcs.length + a))
    {vs : List Val} (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) (hg : SplitGood (invoke u a vs)) :
    LinkSt s₀ ρ O (u, .pending a vs) (σ, .pending (s₀.funcs.length + a) vs) := by
  obtain ⟨fi, hfi⟩ : ∃ fi, u.funcs[a]? = some fi := getElem?_of_lt' ha
  have hσ : σ.funcs[s₀.funcs.length + a]? = some ((sh s₀).finst fi) :=
    hF _ _ (funcs_reloc_of s₀ hfi)
  have hcode : (sh s₀).code (invoke u a vs).code =
      vals vs ++ [.ref (.func (s₀.funcs.length + a)), .callRefType fi.type] := by
    simp only [invoke, hfi, Option.map_some, Option.getD_some, Shift.code_append,
      Shift.code_vals, Shift.code_ref, Shift.code_callRefType, Shift.code_nil, Shift.ref_func,
      sh_fn]
    rw [map_val_scalar (sh s₀).val (fun _ => rfl) (fun _ => rfl) hvs]
  have hframe : (sh s₀).frame (invoke u a vs).frame = {} := rfl
  refine ⟨?_, ⟨hg, hR, ?_, ?_⟩, hF⟩
  · show invoke σ (s₀.funcs.length + a) vs = linkC s₀ ρ σ (invoke u a vs)
    unfold linkC
    rw [hframe, hcode]
    simp only [Ren.code_append, Ren.code_vals, Ren.code_ref, Ren.code_callRefType, Ren.code_nil,
      invoke, hσ, Option.map_some, Option.getD_some]
    rw [map_val_scalar ρ.val (fun _ => rfl) (fun _ => rfl) hvs]
    rfl
  · show O.FrameGood ((sh s₀).frame (invoke u a vs).frame)
    rw [hframe]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩
  · show O.CodeGood ((sh s₀).code (invoke u a vs).code)
    rw [hcode]
    exact O.codeGood_append.mpr ⟨codeGood_scalar hvs,
      Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.cons_ref hO (by simp [Own.CodeGood])⟩

/-! ## The empty prefix: the exporter's part -/

section Empty

/-- The shift past the empty store. -/
abbrev sh0 (H : Type) : Shift := sh ({} : Store H)

theorem sh0_ref : ∀ r : Ref, (sh0 H).ref r = r
  | .struct a => by simp
  | .array a => by simp
  | .func a => by simp
  | .exn a => by simp [Shift.ofStore]
  | .extern r => by simp [sh0_ref r]
  | .i31 _ => rfl
  | .null => rfl
  | .host _ => rfl

theorem sh0_val (v : Val) : (sh0 H).val v = v := by
  cases v <;> simp [Shift.val, sh0_ref]

theorem sh0_fval (v : FieldVal) : (sh0 H).fval v = v := by
  cases v <;> simp [Shift.fval, sh0_val]

theorem sh0_xinst (x : ExportInst) : (sh0 H).xinst x = x := by
  rcases x with ⟨n, a⟩
  cases a <;> simp [Shift.xinst, Shift.xa, Shift.ofStore]

theorem sh0_minst (m : ModuleInst) : (sh0 H).minst m = m := by
  rcases m with ⟨ty, tg, gl, me, ta, fn, da, el, ex⟩
  have hx : ex.map (sh0 H).xinst = ex := by
    conv => rhs; rw [← List.map_id ex]
    exact List.map_congr_left (fun x _ => sh0_xinst x)
  simp only [Shift.minst, hx]
  simp [Shift.ofStore]

theorem sh0_frame (f : Frame) : (sh0 H).frame f = f := by
  rcases f with ⟨ls, m⟩
  have hl : ls.map (Option.map (sh0 H).val) = ls := by
    conv => rhs; rw [← List.map_id ls]
    refine List.map_congr_left (fun o _ => ?_)
    cases o <;> simp [sh0_val]
  simp only [Shift.frame, hl, sh0_minst]

theorem sh0_code : ∀ l : List Admin, (sh0 H).code l = l
  | [] => by simp
  | .ref r :: l => by simp [sh0_ref, sh0_code l]
  | .label n c b :: l => by simp [sh0_code b, sh0_code l]
  | .handler n cs b :: l => by simp [sh0_code b, sh0_code l]
  | .frame n f b :: l => by simp [sh0_code b, sh0_code l, sh0_frame]
  | .plain i :: l => by simp [sh0_code l]
  | .callRefType d :: l => by simp [sh0_code l]
  | .returnCallRefType d :: l => by simp [sh0_code l]
  | .trap :: l => by simp [sh0_code l]

theorem map_id_of {α : Type} {g : α → α} (hg : ∀ x, g x = x) (l : List α) : l.map g = l := by
  conv => rhs; rw [← List.map_id l]
  exact List.map_congr_left (fun x _ => hg x)

theorem reloc_empty (u : Store H) : reloc ({} : Store H) u = u := by
  have hfi : ∀ fi : FuncInst H, (sh0 H).finst fi = fi := fun fi => by
    simp [Shift.finst, sh0_minst]
  have hg : ∀ g : GlobalInst, (sh0 H).ginst g = g := fun g => by simp [Shift.ginst, sh0_val]
  have ht : ∀ t : TableInst, (sh0 H).tinst t = t := fun t => by
    simp [Shift.tinst, map_id_of sh0_ref]
  have he : ∀ e : ElemInst, (sh0 H).einst e = e := fun e => by
    simp [Shift.einst, map_id_of sh0_ref]
  have hs : ∀ si : StructInst, (sh0 H).sinst si = si := fun si => by
    simp [Shift.sinst, map_id_of sh0_fval]
  have ha : ∀ ai : ArrayInst, (sh0 H).ainst ai = ai := fun ai => by
    simp [Shift.ainst, map_id_of sh0_fval]
  have hx : ∀ e : ExnInst, (sh0 H).xninst e = e := fun e => by
    rcases e with ⟨tg, fs⟩
    have hf : fs.map (sh0 H).val = fs := map_id_of sh0_val fs
    simp only [Shift.xninst, hf]
    simp [Shift.ofStore]
  rcases u with ⟨tg, gl, me, ta, fn, da, el, st, ar, ex⟩
  simp only [reloc, Store.app, Shift.store, map_id_of hfi, map_id_of hg, map_id_of ht,
    map_id_of he, map_id_of hs, map_id_of ha, map_id_of hx]
  simp

/-- **The exporter's image**: with the empty prefix, `linkC` is the renaming alone. -/
theorem linkC_empty (ρ : Ren) (σ : Store H) (c : Config H) :
    linkC ({} : Store H) ρ σ c = ⟨σ, ρ.frame c.frame, ρ.code c.code⟩ := by
  simp only [linkC, sh0_frame, sh0_code]

/-- With the empty prefix, `FnPre` says the part's functions are functions of the shared
store. -/
theorem fnPre_empty_iff {σ u : Store H} :
    FnPre ({} : Store H) σ u ↔ ∀ (a : Nat) (fi : FuncInst H), u.funcs[a]? = some fi → σ.funcs[a]? = some fi := by
  simp only [FnPre, reloc_empty]

/-- With the empty prefix, `ImpRel` is the relation of `Linking.Split` for the renaming alone. -/
theorem impRel_empty_iff {ρ : Ren} {O : Own} {σ : Store H} {c : Config H} :
    ImpRel ({} : Store H) ρ O σ c ↔
      SplitGood c ∧ PartRel ρ O c.store σ ∧ O.FrameGood c.frame ∧ O.CodeGood c.code := by
  constructor
  · intro h
    refine ⟨h.good, ?_, ?_, ?_⟩
    · simpa only [reloc_empty] using h.rel
    · simpa only [sh0_frame] using h.frame
    · simpa only [sh0_code] using h.code
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · simpa only [reloc_empty] using h2
    · simpa only [sh0_frame] using h3
    · simpa only [sh0_code] using h4

end Empty

end Silmaril.Proofs.Wasm.Component.Reference
