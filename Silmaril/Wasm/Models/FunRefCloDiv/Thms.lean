module

public import Silmaril.Wasm.Models.FunRefCloDiv.Defs
public import Silmaril.Proofs.Wasm.Models.FunRefCloDiv.Apply

/-!
# Compiling FunRefClo, diverging programs included: behaviours, embedding, game institution

`Silmaril.Wasm.Models.FunRefCloCompile.behaviours_compile` characterises the compiled behaviours of
a FunRefClo program (closures and references) that returns. Here the diverging programs are
covered too, so the references-and-closures compiler is an embedding on **every** accepted
program, as `Silmaril.Wasm.Models.FunCloDiv` does for FunClo.

**Divergence.** `behaviours_div`: if the accepted program `p` diverges on `n` from the empty
heap (`DivergesOn`, no fuel suffices), then **at every profile and for every host relation** the
behaviours of `main` on `n` in `storeOf p` (the instantiated module,
`FunRefCloCompile.instantiate_moduleOf`) are exactly `{diverges}`: no run ends, in values, a
trap or an exception, and an infinite run exists. The proof
(`Silmaril.Proofs.Wasm.Models.FunRefCloDiv`) is FunCloDiv's step-indexed every-run argument with
the heap threaded: the inversion lemmas of the source need a heap typing (type preservation,
`FunRefClo.eval_sound`) to exclude stuck terms, and the safety statement of a diverging term
holds in every store whose cells represent the heap it diverges from. The parts that return
reuse FunRefCloCompile's total-correctness statement, which hands on the cells of the heap they
return in.

**All programs.** `behaviours_compile_all`: for every accepted program and argument, the
behaviours are `{returns [w]}` (`w` the word of the value) or `{diverges}`, as the program
returns or diverges (`conv_or_div`).

**The model embedding and the game institution.** `funRefCloAllModel` has every accepted program
in its domain and observes divergence (`obsAll`); on the terminating programs it observes what
`funRefCloModel` does (`obsAll_eq_obs`). `compileEmbAll P` is an equality embedding into
`core|micro functionalMutGC` (`view_compile_all`), with `compileGameHomAll`, `compileCoHomAll`,
`reduct_compileAll` and `sat_compileAll_iff`.

**Example: Landin's knot.** `exKnot` is
`let r = ref (λy. y) in r := (λy. (!r) y); (!r) x`: the closure in the cell calls itself through
the cell, with no `fix` recursion. It diverges on every argument (`exKnot_diverges`), is outside
`funRefCloModel`'s domain (`exKnot_not_terminates`), and its compiled `main` diverges
(`exKnot_behaviours`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCloDiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Models.FunRefClo (Tm Prog obsWord funRefCloModel)
open Silmaril.Wasm.Models.FunRefCloCompile (storeOf ptOf moduleOf moduleOf_valid ptOf_dom
  behaviours_compile)
open Silmaril.Wasm.Models.FunCompile (callOf readWord valWord valWord_i32)
open Silmaril.Wasm.Models.FunRefCompile (S₁)
open Silmaril.Proofs.Wasm.Models.FunRefCloDiv (conv_or_div not_div_eval)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Behaviours -/

/-- **The behaviours of a diverging program**: `main` on `n` diverges and does nothing else, at
every profile and for every host. -/
theorem behaviours_div (P : Profile) (host : HostSemantics Nat) {p : Prog} (hp : p.Ok)
    {n : BitVec 31} (hd : DivergesOn p n) :
    behaviours P host (storeOf p) 0 [.i32 (n.setWidth 32)] = {.diverges} :=
  Silmaril.Proofs.Wasm.Models.FunRefCloDiv.behaviours_div P host hp.1 hp.2 hd

/-- A program returns on `n` or diverges on `n`. -/
theorem eval_or_div (p : Prog) (n : BitVec 31) : (∃ v, p.Eval n v) ∨ DivergesOn p n :=
  (conv_or_div [] [.int n] p.body).imp (fun ⟨k, v, σ, hv⟩ => ⟨v, k, σ, hv⟩) id

theorem not_div_of_eval {p : Prog} {n : BitVec 31} {v : FunRefClo.Val} (hv : p.Eval n v) :
    ¬ DivergesOn p n :=
  let ⟨_, _, hk⟩ := hv
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
      · rw [FunRefClo.Prog.Eval.unique hv' hv]; rfl
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

theorem obsAll_eval {p : Prog} {n : BitVec 31} {v : FunRefClo.Val} (hv : p.Eval n v) :
    obsAll p n = {.returns [obsWord v]} := by
  ext b
  constructor
  · rintro (⟨v', hv', rfl⟩ | ⟨hd, -⟩)
    · rw [FunRefClo.Prog.Eval.unique hv' hv]; rfl
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

/-- On a terminating program, the observations with divergence are those of `funRefCloModel`. -/
theorem obsAll_eq_obs {p : Prog} (ht : p.Terminates) (n : BitVec 31) :
    obsAll p n = funRefCloModel.obs p n := by
  obtain ⟨v, hv⟩ := ht n
  rw [obsAll_eval hv]
  exact (FunRefClo.Prog.obs_eq hv).symm

/-- A single behaviour, read back. -/
theorem view_of_obs (P : Profile) {p : Prog} {n : BitVec 31} {b : Behaviour Val}
    (hb : (coreModel P Nat S₁).obs (ptOf p) (callOf n) = {b}) :
    (coreModel P Nat S₁).view (some ∘ readWord) (ptOf p) (callOf n) = {readWord b} := by
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
    (coreModel P Nat S₁).view (some ∘ readWord) (ptOf p) (callOf n) = obsAll p n := by
  rcases eval_or_div p n with ⟨v, hv⟩ | hd
  · have hb : (coreModel P Nat S₁).obs (ptOf p) (callOf n) =
        {.returns [.i32 ((obsWord v).setWidth 32)]} :=
      behaviours_compile P FunCompile.noHost hp hv
    have hr : readWord (.returns [.i32 ((obsWord v).setWidth 32)]) = .returns [obsWord v] := by
      simp only [readWord, Behaviour.map_returns, List.map_cons, List.map_nil, valWord_i32]
    rw [view_of_obs P hb, obsAll_eval hv, hr]
  · have hb : (coreModel P Nat S₁).obs (ptOf p) (callOf n) = {.diverges} :=
      behaviours_div P FunCompile.noHost hp hd
    rw [view_of_obs P hb, obsAll_div hd]
    rfl

/-! ## The embedding and the game institution -/

/-- **The compiler as an embedding of models** `funRefCloAllModel → core|micro functionalMutGC`,
of direction `eq`, on every accepted program. -/
def compileEmbAll (P : Profile) : funRefCloAllModel.Emb (coreModel P Nat S₁) where
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
def compileGameHomAll (P : Profile) : funRefCloAllModel.game ⟶ (coreModel P Nat S₁).game :=
  (compileEmbAll P).gameHom (compileTotalAll P)

/-- **The comorphism of game institutions of the compiler**, diverging programs included. -/
def compileCoHomAll (P : Profile) :
    Inst.CoHom funRefCloAllModel.ginst (coreModel P Nat S₁).ginst :=
  (compileEmbAll P).ginstCoHom (compileTotalAll P)

/-- **The reduct of the compiled point's strategy is the program's strategy.** -/
theorem reduct_compileAll (P : Profile) {p : Prog} (hp : funRefCloAllModel.dom p) :
    Game.reduct (compileGameHomAll P) ((coreModel P Nat S₁).strat (ptOf p)) =
      funRefCloAllModel.strat p :=
  (compileEmbAll P).reduct_eq (compileTotalAll P) rfl hp

/-- **Compatible satisfaction** for every `GInst` sentence, on every accepted program. -/
theorem sat_compileAll_iff (P : Profile) {p : Prog} (hp : funRefCloAllModel.dom p)
    (φ : GSen funRefCloAllModel.game.E funRefCloAllModel.game.F) :
    (Game.senMap (compileGameHomAll P) φ).holds ((coreModel P Nat S₁).strat (ptOf p)) ↔
      φ.holds (funRefCloAllModel.strat p) :=
  (compileEmbAll P).sat_translate_iff (compileTotalAll P) rfl hp φ

/-! ## Landin's knot: recursion through the heap -/

/-- The body of the closure stored in the cell: `(!r) y` (`y` is `var 0`, `r` is `var 2`). -/
def knotBody : Tm := .app (.get (.var 2)) (.var 0)

/-- `let r = ref (λy. y) in r := (λy. (!r) y); (!r) x`: the stored closure calls itself
through the cell. -/
def exKnot : Prog :=
  ⟨.let_ (.ref (.fix (.var 0)))
    (.let_ (.set (.var 0) (.fix knotBody)) (.app (.get (.var 1)) (.var 2))), .int⟩

theorem exKnot_ok : exKnot.Ok :=
  ⟨⟨.let_ (.ref (.fix (σ := .int) (.var rfl)))
      (.let_ (.set (.var rfl) (.fix (.app (.get (.var rfl)) (.var rfl))))
        (.app (.get (.var rfl)) (.var rfl))),
    trivial⟩, by unfold Prog.Fits; decide⟩

/-- The environment of the stored closure. -/
def knotEnv (n : BitVec 31) : List FunRefClo.Val := [.loc 0, .int n]

/-- The heap after the knot is tied. -/
def knotHeap (n : BitVec 31) : FunRefClo.Heap := [.clo knotBody (knotEnv n)]

theorem knot_loop (n : BitVec 31) (u : FunRefClo.Val) :
    ∀ k, FunRefClo.eval k (knotHeap n) (u :: .clo knotBody (knotEnv n) :: knotEnv n) knotBody =
      none
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | k + 3 => knot_loop n u (k + 2)

/-- **`exKnot` diverges on every argument.** -/
theorem exKnot_diverges (n : BitVec 31) : DivergesOn exKnot n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | k + 6 => knot_loop n (.int n) (k + 3)

/-- `exKnot` is not in the domain of `funRefCloModel` (terminating programs). -/
theorem exKnot_not_terminates : ¬ exKnot.Terminates := fun h =>
  let ⟨_, hv⟩ := h 0
  not_div_of_eval hv (exKnot_diverges 0)

/-- **The compiled `exKnot` diverges**, at every profile and for every host. -/
theorem exKnot_behaviours (P : Profile) (host : HostSemantics Nat) (n : BitVec 31) :
    behaviours P host (storeOf exKnot) 0 [.i32 (n.setWidth 32)] = {.diverges} :=
  behaviours_div P host exKnot_ok (exKnot_diverges n)

end Silmaril.Wasm.Models.FunRefCloDiv
