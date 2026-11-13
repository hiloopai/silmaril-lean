module

public import Silmaril.Wasm.Models.FunCloDiv.Defs
public import Silmaril.Proofs.Wasm.Models.FunCloDiv.Apply

/-!
# Compiling FunClo, diverging programs included: behaviours, embedding, game institution

`Silmaril.Wasm.Models.FunCloCompile.behaviours_compile` characterises the compiled behaviours of a
program that returns. Here the diverging programs are covered too, so the compiler is an
embedding on **every** accepted program.

**Divergence.** `behaviours_div`: if the accepted program `p` diverges on `n` (`DivergesOn`, no
fuel suffices), then **at every profile and for every host relation** the behaviours of `main`
on `n` in `storeOf p` (the instantiated module, `FunCloCompile.instantiate_moduleOf`) are exactly
`{diverges}`: no run ends, in values, a trap or an exception, and an infinite run exists. The
proof (`Silmaril.Proofs.Wasm.Models.FunCloDiv`) is in the step-indexed every-run logic
(`Hoare.Safe`): the code of a diverging well-typed term is safe for `n` steps in any context
with any postcondition, by induction on `n` and then on the term. Parts that return reuse
FunCloCompile's total-correctness statement before the diverging part (`safe_of_twp`), and a
call of `apply` costs the step that the induction on `n` consumes.

**All programs.** `behaviours_compile_all`: for every accepted program and argument, the
behaviours are `{returns [w]}` (`w` the word of the value) or `{diverges}`, as the program
returns or diverges (`conv_or_div`). Typing excludes the third case, a stuck term.

**The model embedding and the game institution.** `funCloAllModel` has every accepted program
in its domain and observes divergence (`obsAll`). `compileEmbAll P` is an equality embedding
into `core|micro functional` (`view_compile_all`), with `compileGameHomAll`,
`compileCoHomAll`, `reduct_compileAll` and `sat_compileAll_iff` as for the terminating
programs.

**Example.** `exLoop`, `(fix f x. f x) x`, diverges on every argument (`exLoop_diverges`), so it
is outside `funCloModel`'s domain; its compiled `main` diverges (`exLoop_behaviours`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunClo (Tm Prog obsWord)
open Silmaril.Wasm.Models.FunCloCompile (storeOf ptOf moduleOf moduleOf_valid ptOf_dom
  behaviours_compile)
open Silmaril.Wasm.Models.FunCompile (callOf readWord valWord valWord_i32 S₀)
open Silmaril.Proofs.Wasm.Models.FunCloDiv (conv_or_div not_div_eval)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Behaviours -/

/-- **The behaviours of a diverging program**: `main` on `n` diverges and does nothing else, at
every profile and for every host. -/
theorem behaviours_div (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    {n : BitVec 31} (hd : DivergesOn p n) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] = {.diverges} :=
  Silmaril.Proofs.Wasm.Models.FunCloDiv.behaviours_div P host hp.1 hp.2 hd

/-- A program returns on `n` or diverges on `n`. -/
theorem eval_or_div (p : Prog) (n : BitVec 31) : (∃ v, p.Eval n v) ∨ DivergesOn p n :=
  (conv_or_div [.int n] p.body).imp (fun ⟨k, v, hv⟩ => ⟨v, k, hv⟩) id

theorem not_div_of_eval {p : Prog} {n : BitVec 31} {v : FunClo.Val} (hv : p.Eval n v) :
    ¬ DivergesOn p n :=
  let ⟨_, hk⟩ := hv
  not_div_eval hk

/-- **The compiled behaviours of every accepted program**: the returned word, or divergence. -/
theorem behaviours_compile_all (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    (n : BitVec 31) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] =
      {b | (∃ v, p.Eval n v ∧ b = .returns [.i32 ((obsWord v).setWidth 32)]) ∨
        (DivergesOn p n ∧ b = .diverges)} := by
  rcases eval_or_div p n with ⟨v, hv⟩ | hd
  · rw [behaviours_compile P host hp hv]
    ext b
    constructor
    · rintro rfl
      exact .inl ⟨v, hv, rfl⟩
    · rintro (⟨v', hv', rfl⟩ | ⟨hd, -⟩)
      · rw [FunClo.Prog.Eval.unique hv' hv]; rfl
      · exact absurd hd (not_div_of_eval hv)
  · rw [behaviours_div P host hp hd]
    ext b
    constructor
    · rintro rfl
      exact .inr ⟨hd, rfl⟩
    · rintro (⟨v, hv, -⟩ | ⟨-, rfl⟩)
      · exact absurd hd (not_div_of_eval hv)
      · rfl

/-! ## Observations -/

theorem obsAll_eval {p : Prog} {n : BitVec 31} {v : FunClo.Val} (hv : p.Eval n v) :
    obsAll p n = {.returns [obsWord v]} := by
  ext b
  constructor
  · rintro (⟨v', hv', rfl⟩ | ⟨hd, -⟩)
    · rw [FunClo.Prog.Eval.unique hv' hv]; rfl
    · exact absurd hd (not_div_of_eval hv)
  · rintro rfl
    exact .inl ⟨v, hv, rfl⟩

theorem obsAll_div {p : Prog} {n : BitVec 31} (hd : DivergesOn p n) :
    obsAll p n = {.diverges} := by
  ext b
  constructor
  · rintro (⟨v, hv, -⟩ | ⟨-, rfl⟩)
    · exact absurd hd (not_div_of_eval hv)
    · rfl
  · rintro rfl
    exact .inr ⟨hd, rfl⟩

/-- A single behaviour, read back. -/
theorem view_of_obs (P : Profile) {p : Prog} {n : BitVec 31} {b : Behaviour Val}
    (hb : (coreModel P Nat S₀).obs (ptOf p) (callOf n) = {b}) :
    (coreModel P Nat S₀).view (some ∘ readWord) (ptOf p) (callOf n) = {readWord b} := by
  ext o
  constructor
  · rintro ⟨b', hb', hr⟩
    have hbe : b' = b := by rw [hb] at hb'; exact hb'
    have ho : some (readWord b') = some o := hr
    rw [hbe] at ho
    exact (Option.some.inj ho).symm
  · intro ho
    have hoe : o = readWord b := ho
    exact ⟨b, by rw [hb]; rfl, by rw [hoe]; rfl⟩

/-- **The observations of the compiled point read back are the program's**, for every accepted
program and argument. -/
theorem view_compile_all (P : Profile) {p : Prog} (hp : p.Ok) (n : BitVec 31) :
    (coreModel P Nat S₀).view (some ∘ readWord) (ptOf p) (callOf n) = obsAll p n := by
  rcases eval_or_div p n with ⟨v, hv⟩ | hd
  · have hb : (coreModel P Nat S₀).obs (ptOf p) (callOf n) =
        {.returns [.i32 ((obsWord v).setWidth 32)]} :=
      behaviours_compile P FunCompile.noHost hp hv
    have hr : readWord (.returns [.i32 ((obsWord v).setWidth 32)]) = .returns [obsWord v] := by
      simp only [readWord, Behaviour.map_returns, List.map_cons, List.map_nil, valWord_i32]
    rw [view_of_obs P hb, obsAll_eval hv, hr]
  · have hb : (coreModel P Nat S₀).obs (ptOf p) (callOf n) = {.diverges} :=
      behaviours_div P FunCompile.noHost hp hd
    rw [view_of_obs P hb, obsAll_div hd]
    rfl

/-! ## The embedding and the game institution -/

/-- **The compiler as an embedding of models** `funCloAllModel → core|micro functional`, of
direction `eq`, on every accepted program. -/
def compileEmbAll (P : Profile) : funCloAllModel.Emb (coreModel P Nat S₀) where
  mod := moduleOf
  valid _ hp := moduleOf_valid hp
  pt := ptOf
  call := callOf
  readback := some ∘ readWord
  dom q _ := ptOf_dom q
  dir := .eq
  sat _ hp n := view_compile_all P hp n

/-- The read-back of the compiler is total. -/
def compileTotalAll (P : Profile) : (compileEmbAll P).Total := ⟨readWord, fun _ => rfl⟩

/-- **The game morphism of the compiler**, diverging programs included. -/
def compileGameHomAll (P : Profile) : funCloAllModel.game ⟶ (coreModel P Nat S₀).game :=
  (compileEmbAll P).gameHom (compileTotalAll P)

/-- **The comorphism of game institutions of the compiler**, diverging programs included. -/
def compileCoHomAll (P : Profile) :
    Inst.CoHom funCloAllModel.ginst (coreModel P Nat S₀).ginst :=
  (compileEmbAll P).ginstCoHom (compileTotalAll P)

/-- **The reduct of the compiled point's strategy is the program's strategy.** -/
theorem reduct_compileAll (P : Profile) {p : Prog} (hp : funCloAllModel.dom p) :
    Game.reduct (compileGameHomAll P) ((coreModel P Nat S₀).strat (ptOf p)) =
      funCloAllModel.strat p :=
  (compileEmbAll P).reduct_eq (compileTotalAll P) rfl hp

/-- **Compatible satisfaction** for every `GInst` sentence, on every accepted program. -/
theorem sat_compileAll_iff (P : Profile) {p : Prog} (hp : funCloAllModel.dom p)
    (φ : GSen funCloAllModel.game.E funCloAllModel.game.F) :
    (Game.senMap (compileGameHomAll P) φ).holds ((coreModel P Nat S₀).strat (ptOf p)) ↔
      φ.holds (funCloAllModel.strat p) :=
  (compileEmbAll P).sat_translate_iff (compileTotalAll P) rfl hp φ

/-! ## A diverging program -/

/-- The body of `fix f x. f x`. -/
def loopBody : Tm := .app (.var 1) (.var 0)

/-- `(fix f x. f x) x`: diverges on every argument. -/
def exLoop : Prog := ⟨.app (.fix loopBody) (.var 0), .int⟩

theorem exLoop_ok : exLoop.Ok :=
  ⟨⟨.app (.fix (.app (.var rfl) (.var rfl))) (.var rfl), trivial⟩, by unfold Prog.Fits; decide⟩

theorem loopBody_div (ρ : List FunClo.Val) (u : FunClo.Val) :
    ∀ k, FunClo.eval k (u :: .clo loopBody ρ :: ρ) loopBody = none
  | 0 => rfl
  | 1 => rfl
  | k + 2 => loopBody_div ρ u (k + 1)

/-- **`exLoop` diverges on every argument.** -/
theorem exLoop_diverges (n : BitVec 31) : DivergesOn exLoop n
  | 0 => rfl
  | 1 => rfl
  | k + 2 => loopBody_div [.int n] (.int n) (k + 1)

/-- `exLoop` is not in the domain of `funCloModel` (terminating programs). -/
theorem exLoop_not_terminates : ¬ exLoop.Terminates := fun h =>
  let ⟨_, hv⟩ := h 0
  not_div_of_eval hv (exLoop_diverges 0)

/-- **The compiled `exLoop` diverges**, at every profile and for every host. -/
theorem exLoop_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exLoop) 0 [.i32 (n.setWidth 32)] = {.diverges} :=
  behaviours_div P host exLoop_ok (exLoop_diverges n)

end Silmaril.Wasm.Models.FunCloDiv
