module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Step
public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Proofs.Wasm.Game.Linking.Callout

/-!
# Instance strategies are invariant under global-address embeddings

`ScalarInstance.dstrategy_emb`: if the store `t` embeds the store `s` along an injective map
`ι` of global addresses (`Emb ι Univ s t`; `t` may hold further globals that no module
instance names), the divergence-observing strategies of any scalar instance at `s` and at `t`
are equal, for every profile `P`; `strategy_emb`: the same for the plain strategies.

Both directions are lock-step divergence-sensitive simulations of the instance's transition
systems (`ScalarInstance.dlts`), related states being equal up to renaming threads by `ι`:

* `s` to `t`: `step` with the domain everything;
* `t` to `s`: `step` with a left inverse `κ` of `ι` on the range of `ι`, which the renamed
  configurations and functions only name (`CfgDom (Img ι)`); the result names only the range
  again, so it is the renaming of a configuration of `s`.

Host-call redexes (`decompose?`), their resumption and results are renamed alike. No typing,
determinism or well-formedness is used. New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Validation
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-! ## Threads and contexts -/

/-- Rename the frames of a thread. -/
def thread (ρ : Nat → Nat) : Thread → Thread
  | .pending a args => .pending a args
  | .active f code => .active (frame ρ f) (admins ρ code)

/-- Rename the frames of a callout context. -/
def ctx (ρ : Nat → Nat) : Ctx → Ctx
  | .top pre rest => .top pre (admins ρ rest)
  | .label pre n cont E rest => .label pre n cont (ctx ρ E) (admins ρ rest)
  | .handler pre n cs E rest => .handler pre n cs (ctx ρ E) (admins ρ rest)
  | .frame pre n f E rest => .frame pre n (frame ρ f) (ctx ρ E) (admins ρ rest)

theorem ctx_fill (ρ : Nat → Nat) (E : Ctx) (xs : List Admin) :
    admins ρ (E.fill xs) = (ctx ρ E).fill (admins ρ xs) := by
  induction E with
  | top pre rest => simp only [Ctx.fill, ctx, admins_append, admins_vals]
  | label pre n cont E rest ih => simp only [Ctx.fill, ctx, admins_append, admins_vals, admins, admin, ih]
  | handler pre n cs E rest ih =>
    simp only [Ctx.fill, ctx, admins_append, admins_vals, admins, admin, ih]
  | frame pre n f E rest ih => simp only [Ctx.fill, ctx, admins_append, admins_vals, admins, admin, ih]

theorem frame_empty (ρ : Nat → Nat) : frame ρ ({} : Frame) = {} := rfl

variable {H : Type}

/-- The configuration of a renamed thread is the renamed configuration. -/
theorem thread_config {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} (h : Emb ρ D s t)
    (th : Thread) : (thread ρ th).config t = config ρ t (th.config s) := by
  cases th with
  | pending a args =>
    simp only [thread, Thread.config, invoke, config, frame_empty, admins_append, admins_vals,
      admins, admin, h.func_types a]
  | active f code => rfl

theorem thread_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) (th : Thread) :
    thread κ (thread ι th) = th := by
  cases th with
  | pending a args => rfl
  | active f code => simp only [thread, frame_inv hκ, admins_inv hκ]

theorem config_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) (c : Config H) {s : Store H}
    (hs : c.store = s) (t : Store H) : config κ s (config ι t c) = c := by
  cases c
  simp only [config, frame_inv hκ, admins_inv hκ]
  rw [← hs]

/-! ## Flipping an embedding -/

theorem flip_globals {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) {s t : Store H}
    (h : Emb ι Univ s t) : ∀ b, Img ι b → s.globals[κ b]? = t.globals[b]? := by
  intro b hb
  obtain ⟨a, ha⟩ := hb
  have e : s.globals[κ (ι a)]? = t.globals[ι a]? := by rw [hκ, h.globals a trivial]
  rwa [ha] at e

theorem flip_inj {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) :
    ∀ a b, Img ι a → Img ι b → κ a = κ b → a = b := by
  intro _ _ ha hb e
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  have e' : a = b := by rwa [hκ, hκ] at e
  rw [e']

theorem flip_funcs {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) {s t : Store H}
    (h : Emb ι Univ s t) : s.funcs = t.funcs.map (function κ) := by
  have e : function κ ∘ function ι = (id : FuncInst H → FuncInst H) :=
    funext fun fi => function_inv hκ fi
  rw [h.funcs, List.map_map, e, List.map_id]

theorem flip_fdom {ι : Nat → Nat} {s t : Store H} (h : Emb ι Univ s t) :
    ∀ gi ∈ t.funcs, ModDom (Img ι) gi.module := by
  intro gi hg
  have hg' : gi ∈ s.funcs.map (function ι) := h.funcs ▸ hg
  obtain ⟨fi, -, hfi⟩ := List.mem_map.1 hg'
  rw [← hfi]
  exact modDom_img ι fi.module

/-- An embedding along an injective `ι` gives the reverse embedding along a left inverse `κ`,
on the range of `ι`. -/
theorem Emb.flip {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) {s t : Store H} (h : Emb ι Univ s t) :
    Emb κ (Img ι) t s :=
  ⟨flip_globals hκ h, flip_inj hκ, flip_funcs hκ h, flip_fdom h, h.tags.symm, h.mems.symm,
    h.tables.symm, h.datas.symm, h.elems.symm, h.structs.symm, h.arrays.symm, h.exns.symm⟩

/-- The reverse embedding along `κ` on the range of `ι` gives the embedding along `ι`. -/
theorem Emb.unflip {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) {s t : Store H}
    (h : Emb κ (Img ι) t s) : Emb ι Univ s t where
  globals a _ := by
    have e := h.globals (ι a) ⟨a, rfl⟩
    rw [hκ] at e
    exact e.symm
  inj a b _ _ e := by
    have e' : κ (ι a) = κ (ι b) := congrArg κ e
    rwa [hκ, hκ] at e'
  funcs := by
    rw [h.funcs, List.map_map]
    refine ((List.map_congr_left fun gi hg => ?_).trans (List.map_id _)).symm
    simp only [Function.comp_apply, function, id_eq, moduleView_inv' hκ (h.fdom gi hg)]
  fdom _ _ := modDom_univ _
  tags := h.tags.symm
  mems := h.mems.symm
  tables := h.tables.symm
  datas := h.datas.symm
  elems := h.elems.symm
  structs := h.structs.symm
  arrays := h.arrays.symm
  exns := h.exns.symm

/-! ## Machine predicates -/

/-- Host-call redexes are renamed: same callee, host code and arguments. -/
theorem decompose?_emb {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} (h : Emb ρ D s t)
    {code : List Admin} {E : Ctx} {a : Nat} {hc : H} {args : List Val}
    (hd : decompose? s code = some (E, a, hc, args)) :
    decompose? t (admins ρ code) = some (ctx ρ E, a, hc, args) := by
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, rfl⟩ := decompose?_sound hd
  have hfill : admins ρ (E.fill (vals args ++ [.ref (.func a), yy])) =
      (ctx ρ E).fill (vals args ++ [.ref (.func a), yy]) := by
    rw [ctx_fill]
    simp only [admins_append, admins_vals, admins, admin, call_ref_fixed hyy]
  rw [hfill]
  exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill (ctx ρ E) hyy (h.func_lookup hf) he hn
    hcode

variable {ι κ : Nat → Nat} {s t : Store Nat}

theorem decompose?_none {th : Thread} (hκ : ∀ a, κ (ι a) = a) (h : Emb ι Univ s t)
    (hd : decompose? s (th.config s).code = none) :
    decompose? t ((thread ι th).config t).code = none := by
  cases hd' : decompose? t ((thread ι th).config t).code with
  | none => rfl
  | some x =>
    obtain ⟨E, a, hc, args⟩ := x
    have hb := decompose?_emb (h.flip hκ) hd'
    rw [thread_config h, config, admins_inv hκ] at hb
    rw [hd] at hb
    cases hb

theorem calloutAt_emb {th : Thread} {hc : Nat} {args : List Val} (h : Emb ι Univ s t)
    (hco : CalloutAt s th hc args) : CalloutAt t (thread ι th) hc args := by
  obtain ⟨E, a, hd⟩ := hco
  refine ⟨ctx ι E, a, ?_⟩
  rw [thread_config h]
  exact decompose?_emb h hd

theorem calloutAt_back {th : Thread} {hc : Nat} {args : List Val} (hκ : ∀ a, κ (ι a) = a)
    (h : Emb ι Univ s t) (hco : CalloutAt t (thread ι th) hc args) : CalloutAt s th hc args := by
  obtain ⟨E, a, hd⟩ := hco
  refine ⟨ctx κ E, a, ?_⟩
  have hb := decompose?_emb (h.flip hκ) hd
  rw [thread_config h, config, admins_inv hκ] at hb
  exact hb

theorem resultAt_emb {th : Thread} {r : Result} (h : Emb ι Univ s t) (hr : ResultAt s th r) :
    ResultAt t (thread ι th) r := by
  unfold ResultAt at hr ⊢
  rw [thread_config h, config]
  simp only [hr, admins_result]

theorem resultAt_back {th : Thread} {r : Result} (hκ : ∀ a, κ (ι a) = a) (h : Emb ι Univ s t)
    (hr : ResultAt t (thread ι th) r) : ResultAt s th r := by
  unfold ResultAt at hr ⊢
  rw [thread_config h, config] at hr
  have e := congrArg (admins κ) hr
  simpa only [admins_inv hκ, admins_result] using e

theorem resumeResult_emb {th : Thread} (r : Result) (hκ : ∀ a, κ (ι a) = a)
    (h : Emb ι Univ s t) :
    resumeResult t (thread ι th) r = thread ι (resumeResult s th r) := by
  cases hd : decompose? s (th.config s).code with
  | none =>
    have ht := decompose?_none hκ h hd
    simp only [resumeResult, ht, hd]
  | some x =>
    obtain ⟨E, a, hc, args⟩ := x
    have ht : decompose? t ((thread ι th).config t).code = some (ctx ι E, a, hc, args) := by
      rw [thread_config h, config]
      exact decompose?_emb h hd
    have hf : ((thread ι th).config t).frame = frame ι (th.config s).frame := by
      rw [thread_config h]
      rfl
    simp only [resumeResult]
    rw [ht, hd, hf]
    simp only [thread, ctx_fill, admins_result]

/-- Host-free machine steps of `s` are steps of `t`. -/
theorem internal_emb {P : Profile} {s' : Store Nat} {s t : Store Nat} {th th' : Thread}
    (h : Emb ι Univ s t) (hi : InternalP P (s, th) (s', th')) :
    ∃ t', InternalP P (t, thread ι th) (t', thread ι th') ∧ Emb ι Univ s' t' := by
  obtain ⟨f', code', rfl, hs⟩ := hi
  have dom : CfgDom Univ (th.config s) := ⟨modDom_univ _, adminsDom_univ _⟩
  have hst : Emb ι Univ (th.config s).store t := by rwa [Thread.config_store]
  obtain ⟨t', reduced, emb, -⟩ := step hs hst dom
  refine ⟨t', ⟨frame ι f', admins ι code', rfl, ?_⟩, emb⟩
  rw [thread_config h]
  exact reduced

/-- Host-free machine steps of `t` from renamed threads are renamed steps of `s`. -/
theorem internal_back {P : Profile} {t' : Store Nat} {s t : Store Nat} {th : Thread}
    {th₂ : Thread} (hκ : ∀ a, κ (ι a) = a) (h : Emb ι Univ s t)
    (hi : InternalP P (t, thread ι th) (t', th₂)) :
    ∃ s' th', th₂ = thread ι th' ∧ InternalP P (s, th) (s', th') ∧ Emb ι Univ s' t' := by
  obtain ⟨f', code', rfl, hs⟩ := hi
  have hc : (thread ι th).config t = config ι t (th.config s) := thread_config h th
  have dom : CfgDom (Img ι) ((thread ι th).config t) := by
    rw [hc]
    exact ⟨modDom_img ι _, adminsDom_img ι _⟩
  have hst : Emb κ (Img ι) ((thread ι th).config t).store s := by
    rw [Thread.config_store]
    exact h.flip hκ
  obtain ⟨s', reduced, emb, dom'⟩ := step hs hst dom
  refine ⟨s', .active (frame κ f') (admins κ code'), ?_, ⟨_, _, rfl, ?_⟩, emb.unflip hκ⟩
  · simp only [thread, frame, moduleView_inv' hκ dom'.1, admins_inv' hκ code' dom'.2]
  · have e : config κ s ((thread ι th).config t) = th.config s := by
      rw [hc]
      exact config_inv hκ _ (Thread.config_store s th) t
    rw [← e]
    exact reduced

/-! ## The instance's transition systems -/

namespace Strat

variable (I : ScalarInstance) (ι : Nat → Nat)

/-- States of the instance at `s` and at an embedding `t`: equal up to renaming threads. -/
inductive Rel : I.HState → I.HState → Prop where
  | idle {s t : Store Nat} (h : Emb ι Univ s t) : Rel (.idle s) (.idle t)
  | run {f : I.F.Op} {s t : Store Nat} {th : Thread} (h : Emb ι Univ s t) :
      Rel (.running f s th) (.running f t (thread ι th))
  | wait {f : I.F.Op} {s t : Store Nat} {th : Thread} {e : I.E.Op} (h : Emb ι Univ s t) :
      Rel (.waiting f s th e) (.waiting f t (thread ι th) e)

variable {I ι}

/-- Transitions at `s` are transitions at the embedding. -/
theorem fwd_step {P : Profile} (hκ : ∀ a, κ (ι a) = a) {x x' y : I.HState}
    {l : Option (Move I.E I.F)} (hR : Rel I ι x y) (h : I.DTrans P x l x') :
    ∃ y', I.DTrans P y l y' ∧ Rel I ι x' y' := by
  cases h with
  | call s f =>
    cases hR with
    | idle he => exact ⟨_, .call _ f, .run (th := I.initThread f) he⟩
  | tau hi =>
    cases hR with
    | run he =>
      obtain ⟨t', hi', he'⟩ := internal_emb he hi
      exact ⟨_, .tau hi', .run he'⟩
  | ucall callout op =>
    cases hR with
    | run he => exact ⟨_, .ucall (calloutAt_emb he callout) op, .wait he⟩
  | uret v =>
    cases hR with
    | wait he =>
      refine ⟨_, .uret v, ?_⟩
      rw [resumeResult_emb _ hκ he]
      exact .run he
  | oret final answer =>
    cases hR with
    | run he => exact ⟨_, .oret (resultAt_emb he final) answer, .idle he⟩

/-- Transitions at the embedding are transitions at `s`. -/
theorem bwd_step {P : Profile} (hκ : ∀ a, κ (ι a) = a) {x y y' : I.HState}
    {l : Option (Move I.E I.F)} (hR : Rel I ι x y) (h : I.DTrans P y l y') :
    ∃ x', I.DTrans P x l x' ∧ Rel I ι x' y' := by
  cases h with
  | call t f =>
    cases hR with
    | idle he => exact ⟨_, .call _ f, .run (th := I.initThread f) he⟩
  | tau hi =>
    cases hR with
    | run he =>
      obtain ⟨s', th', hth, hi', he'⟩ := internal_back hκ he hi
      refine ⟨_, .tau hi', ?_⟩
      rw [hth]
      exact .run he'
  | ucall callout op =>
    cases hR with
    | run he => exact ⟨_, .ucall (calloutAt_back hκ he callout) op, .wait he⟩
  | uret v =>
    cases hR with
    | @wait f s t th e he =>
      refine ⟨_, .uret v, ?_⟩
      rw [resumeResult_emb _ hκ he]
      exact .run he
  | oret final answer =>
    cases hR with
    | run he => exact ⟨_, .oret (resultAt_back hκ he final) answer, .idle he⟩

/-- The empty measure. -/
def noLt {α : Type} : α → α → Prop := fun _ _ => False

theorem noLt_wf {α : Type} : WellFounded (noLt (α := α)) := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

/-- `s` to its embedding `t`, divergence-sensitive. -/
def fwdSim (P : Profile) (hκ : ∀ a, κ (ι a) = a) {s t : Store Nat} (h : Emb ι Univ s t) :
    LTS.DivSimulation (I.dlts P s) (I.dlts P t) where
  R := Rel I ι
  init := .idle h
  step hR hs := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hκ hR hs
    exact ⟨y', LTS.Run.of_step (L := I.dlts P t) hy', hR'⟩
  lt := noLt
  wf := noLt_wf
  tau hR hs := by
    obtain ⟨y', hy', hR'⟩ := fwd_step hκ hR hs
    exact .inl ⟨y', .single hy', hR'⟩

/-- The embedding `t` back to `s`, divergence-sensitive. -/
def bwdSim (P : Profile) (hκ : ∀ a, κ (ι a) = a) {s t : Store Nat} (h : Emb ι Univ s t) :
    LTS.DivSimulation (I.dlts P t) (I.dlts P s) where
  R y x := Rel I ι x y
  init := .idle h
  step hR hs := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hκ hR hs
    exact ⟨x', LTS.Run.of_step (L := I.dlts P s) hx', hR'⟩
  lt := noLt
  wf := noLt_wf
  tau hR hs := by
    obtain ⟨x', hx', hR'⟩ := bwd_step hκ hR hs
    exact .inl ⟨x', .single hx', hR'⟩

end Strat

/-- **Divergence-observing strategies are invariant under global embeddings**, every
profile. -/
theorem dstrategy_emb (I : ScalarInstance) (P : Profile) {ι : Nat → Nat}
    (hinj : Function.Injective ι) {s t : Store Nat} (h : Emb ι Univ s t) :
    I.dstrategy P s = I.dstrategy P t := by
  have hκ : ∀ a, Function.invFun ι (ι a) = a := Function.leftInverse_invFun hinj
  exact le_antisymm (Strat.fwdSim P hκ h).ofLTS_le (Strat.bwdSim P hκ h).ofLTS_le

end Silmaril.Proofs.Wasm.Game.SpecGlobals
