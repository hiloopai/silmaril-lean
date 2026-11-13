module

public import Silmaril.Wasm.Logic.Iris.Heap.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Iris.ProgramLogic.Lifting

/-!
# The Iris logic of Wasm Core 3.0: lifting lemmas

`wp_run` is the lifting lemma of the language `IExpr P host`: to prove a weakest
precondition of running code, show (after opening the state interpretation)
that the code can step or has exited, and, a later, handle every Core 3.0 step
and every exit. Every other rule is derived from it.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (Exits)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic
open _root_.Iris.ProgramLogic.Language.Notation

variable {H : Type} {P : Profile} {host : HostSemantics H} {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- The code steps or has exited. -/
def Progress (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (c : List Admin) :
    Prop :=
  (∃ c', Step P host ⟨s, f, c⟩ c') ∨ ∃ o, Exits o c

theorem reducible_of_progress {s : Store H} {f : Frame} {c : List Admin}
    (h : Progress P host s f c) :
    PrimStep.Reducible ((IExpr.run c : IExpr P host), ((s, f) : IState H)) := by
  rcases h with ⟨⟨s', f', c'⟩, hs⟩ | ⟨o, he⟩
  · exact ⟨[], .run c', (s', f'), [], rfl, rfl, .step hs⟩
  · exact ⟨[], .done ⟨s, f, o⟩, (s, f), [], rfl, rfl, .exit he⟩

/-- **The lifting lemma.** -/
theorem wp_run {E : CoPset} {c : List Admin} {Φ : Res H → IProp GF} :
    (∀ s f, wasmInterp (s, f) ={E,∅}=∗ ⌜Progress P host s f c⌝ ∗
      ▷ ((∀ s' f' c', ⌜Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩⌝ ={∅,E}=∗
          wasmInterp (s', f') ∗ WP (IExpr.run c' : IExpr P host) @ E {{ Φ }}) ∧
        (∀ o, ⌜Exits o c⌝ ={∅,E}=∗ wasmInterp (s, f) ∗ Φ ⟨s, f, o⟩)))
    ⊢ WP (IExpr.run c : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  rcases σ with ⟨s, f⟩
  imod H $$ %s %f Hσ with ⟨%Hp, H⟩
  isplitr
  · ipureintro
    exact reducible_of_progress Hp
  imodintro
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨-, heq, hs⟩ : obs = [] ∧ eₜ = [] ∧ IStep (.run c) (s, f) e₂ σ₂ := Hstep
  rw [heq]
  simp only [List.length_nil, Algebra.BigOpL.bigOpL_nil]
  cases hs with
  | step hs =>
    icases H with ⟨H, -⟩
    imod H $$ %_ %_ %_ %hs with ⟨Hσ, Hwp⟩
    imodintro
    iframe
  | exit he =>
    icases H with ⟨-, H⟩
    imod H $$ %_ %he with ⟨Hσ, HΦ⟩
    ihave HΦ := wp_value' (s := .NotStuck) (E := E) $$ HΦ
    imodintro
    iframe

/-! ## Exits -/

/-- The outcome of an exit is determined by its code. -/
theorem Exits.unique {o o' : Outcome} {c : List Admin} (he : Exits o c) (he' : Exits o' c) :
    o' = o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hc : c = vals vs := he
    exact Hoare.exits_vals_inv (hc ▸ he')
  · obtain ⟨x, rest, rfl, rfl⟩ := he
    exact Hoare.exits_br_inv he'
  · obtain ⟨rest, rfl⟩ := he
    exact Hoare.exits_ret_inv he'
  · obtain ⟨vs, rest, rfl⟩ := he
    exact Hoare.exits_trap_inv he'
  · obtain ⟨vs, rest, rfl⟩ := he
    exact Hoare.exits_throw_inv he'
  · obtain ⟨hr, rest, rfl⟩ := he
    exact Hoare.exits_tail_inv hr he'

/-- One step of `wp_exit`, given the rule for shorter exits. -/
theorem wp_exit_of {E : CoPset} {c : List Admin} {o : Outcome} {Φ : Res H → IProp GF}
    (he : Exits o c)
    (ih : ∀ c', Sim.codeSize c' < Sim.codeSize c → Exits o c' →
      (∀ s f, wasmInterp (s, f) ={E}=∗ wasmInterp (s, f) ∗ Φ ⟨s, f, o⟩)
      ⊢ WP (IExpr.run c' : IExpr P host) @ E {{ Φ }}) :
    (∀ s f, wasmInterp (s, f) ={E}=∗ wasmInterp (s, f) ∗ Φ ⟨s, f, o⟩)
    ⊢ WP (IExpr.run c : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_run
  iintro %s %f Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact .inr ⟨o, he⟩
  inext
  isplit
  · iintro %s' %f' %c' %hs
    obtain ⟨hs', hf', he', hlt⟩ : s' = s ∧ f' = f ∧ Exits o c' ∧ Sim.codeSize c' < Sim.codeSize c :=
      Hoare.Exits.step he hs
    rw [hs', hf']
    imod Hclose
    imodintro
    iframe Hσ
    iapply ih c' hlt he' $$ H
  · iintro %o' %he'
    have ho : o' = o := Exits.unique he he'
    rw [ho]
    imod Hclose
    iapply H $$ Hσ

/-- **Exits.** Code that has left with outcome `o` (possibly still bubbling a trap or
an exception out of a sequence) satisfies `Φ` at `o`, if `Φ` holds of the final
state. -/
theorem wp_exit {E : CoPset} {c : List Admin} {o : Outcome} {Φ : Res H → IProp GF}
    (he : Exits o c) :
    (∀ s f, wasmInterp (s, f) ={E}=∗ wasmInterp (s, f) ∗ Φ ⟨s, f, o⟩)
    ⊢ WP (IExpr.run c : IExpr P host) @ E {{ Φ }} := by
  induction hn : Sim.codeSize c using Nat.strong_induction_on generalizing c with
  | _ n ih => exact wp_exit_of he fun c' hlt he' => ih _ (hn ▸ hlt) he' rfl

/-! ## Plain instructions -/

/-- Code headed by an inert plain instruction that steps has not exited. -/
theorem not_exits_inert {s : Store H} {f : Frame} {W : List Val} {i : Instr} {rest : List Admin}
    {c' : Config H} (hi : Hoare.Inert i) (hs : Step P host ⟨s, f, vals W ++ .plain i :: rest⟩ c')
    (o : Outcome) : ¬ Exits o (vals W ++ .plain i :: rest) := by
  intro he
  have hok : Hoare.FnvOk o (W, .plain i :: rest) := by
    rw [← Hoare.fnv_vals_cons hi.1]; exact he.fnv
  have hbl : ¬ SingleThreaded.Det.Blocked (Admin.plain i) := fun hb =>
    Hoare.not_step_blocked hb hs
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · cases hok
  · obtain ⟨x, rest', -, hx⟩ := hok
    have hi' : Admin.plain i = .plain (.br x) := (List.cons.inj (Prod.mk.inj hx).2).1
    exact hbl (Or.inl ⟨x, hi'⟩)
  · obtain ⟨rest', hx⟩ := hok
    have hi' : Admin.plain i = .plain .return_ := (List.cons.inj (Prod.mk.inj hx).2).1
    exact hbl (Or.inr (Or.inl hi'))
  · obtain ⟨vs', rest', hx⟩ := hok
    cases (List.cons.inj (Prod.mk.inj hx).2).1
  · obtain ⟨vs', rest', hx⟩ := hok
    have hi' : Admin.plain i = .plain .throwRef := (List.cons.inj (Prod.mk.inj hx).2).1
    exact hi.2.1 (Admin.plain.inj hi')
  · obtain ⟨hr, rest', hx⟩ := hok
    have hi' : Admin.plain i = r := (List.cons.inj (Prod.mk.inj hx).2).1
    rcases hr with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · exact hbl (Or.inr (Or.inr (hi' ▸ trivial)))
    · cases hi'

/-- **The head rule** (after `Silmaril.Wasm.Logic.Hoare.Safe.head`): an inert plain
instruction under the values `W` has a weakest precondition if, in every state,
some head step exists and, a later, every head step
(`Silmaril.Wasm.SingleThreaded.Det.Head`) leads to code with one. -/
theorem wp_head {E : CoPset} {W : List Val} {i : Instr} {rest : List Admin}
    {Φ : Res H → IProp GF} (hi : Hoare.Inert i) :
    (∀ (s : Store H) (f : Frame), wasmInterp (s, f) ={E}=∗
      ⌜∃ (vs args : List Val) (c₀ : Config H), W = vs ++ args ∧
        SingleThreaded.Det.Head P s f args (.plain i) c₀⌝ ∗
      ▷ ∀ (vs args : List Val) (c₀ : Config H),
        ⌜W = vs ++ args ∧ SingleThreaded.Det.Head P s f args (.plain i) c₀⌝ ={E}=∗
        wasmInterp (c₀.store, c₀.frame) ∗
        WP (IExpr.run (vals vs ++ c₀.code ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals W ++ .plain i :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_run
  iintro %s %f Hσ
  imod H $$ %s %f Hσ with ⟨%hp, H⟩
  obtain ⟨vs, args, ⟨s₀, f₀, c₀⟩, rfl, hh⟩ := hp
  have h₁ : Step P host ⟨s, f, vals args ++ [.plain i]⟩ ⟨s₀, f₀, c₀⟩ :=
    Step.of_noHost host hh.toStep
  have h₂ : Step P host ⟨s, f, vals (vs ++ args) ++ .plain i :: rest⟩
      ⟨s₀, f₀, vals vs ++ c₀ ++ rest⟩ := by
    simpa using Sim.Step.append_right (Sim.Step.vals_left h₁ vs) rest
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact .inl ⟨_, h₂⟩
  inext
  isplit
  · iintro %s' %f' %c' %hs
    obtain ⟨vs', args', c₁, hW, hh', hc⟩ := SingleThreaded.inert_head_inv hi.1 hi.2.1 hi.2.2 hs
    obtain ⟨rfl, rfl, rfl⟩ : s' = c₁.store ∧ f' = c₁.frame ∧ c' = vals vs' ++ c₁.code ++ rest := by
      simpa using hc
    imod Hclose
    iapply H $$ %vs' %args' %c₁ %⟨hW, hh'⟩
  · iintro %o %he
    exact (not_exits_inert hi h₂ o he).elim

end Silmaril.Wasm.Logic.IrisWasm
