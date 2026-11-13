module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiSpec
public import Silmaril.Proofs.Wasm.Component.Reference.ImpGames
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Callouts and resumption under a change of host type

The reference engine runs Core 3.0 code in stores whose host functions are canon host
functions (the `canon lower` trampolines); the game semantics of an instance with imports uses
`Store Nat`, whose host function `k` is import `k`. `Store.mapH g` renames host code along
`g`; with imports, `g` maps each trampoline to the index of its import.

* `hostArity?_mapH`, `topRedex_mapH`, `decompose?_mapH_eq`: a host-call redex of the store is the
  redex of the renamed store, with the host code renamed;
* `config_mapH`, `resumeResult_mapH`: resumption does not depend on host code;
* `SegRun`: a run of a thread made of host-free segments separated by callouts, each resumed
  with a result; `SegRun.path`: on the renamed store such a run is a path of the instance's
  transition system (the game strategy), one import question and answer per callout.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} (g : H → Nat)

/-! ## Redexes -/

theorem hostArity?_mapH (s : Store H) (a : Nat) :
    hostArity? (Store.mapH g s) a = (hostArity? s a).map fun p => (g p.1, p.2) := by
  unfold hostArity?
  rw [Store.mapH_funcs_getElem?]
  cases s.funcs[a]? with
  | none => rfl
  | some fi =>
    simp only [Option.map_some]
    cases hc : fi.code <;> cases hft : fi.type.funcType? <;>
      simp [FuncInst.mapH, hc, hft, FuncCode.mapH]

/-- The renaming of a redex. -/
def mapR : Ctx × Nat × H × List Execution.Core.Val → Ctx × Nat × Nat × List Execution.Core.Val :=
  fun x => (x.1, x.2.1, g x.2.2.1, x.2.2.2)

theorem topRedex_mapH (s : Store H) (vs : List Execution.Core.Val) (rest : List Admin) :
    topRedex (Store.mapH g s) vs rest = (topRedex s vs rest).map (mapR g) := by
  unfold topRedex
  split
  · rw [hostArity?_mapH]
    cases hostArity? s _ with
    | none => rfl
    | some p =>
      show (if p.2 ≤ _ then _ else none) = Option.map _ (if p.2 ≤ _ then _ else none)
      split <;> rfl
  · rfl

theorem decompose?_mapH_eq (s : Store H) (code : List Admin) :
    decompose? (Store.mapH g s) code = (decompose? s code).map (mapR g) := by
  rw [decompose?_eq, decompose?_eq]
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · rfl
  · show decompHead (Store.mapH g s) vs d rest = (decompHead s vs d rest).map (mapR g)
    cases d with
    | label n cont body =>
      simp only [decompHead, decompose?_mapH_eq s body, Option.map_map]
      rfl
    | handler n cs body =>
      simp only [decompHead, decompose?_mapH_eq s body, Option.map_map]
      rfl
    | frame n f body =>
      simp only [decompHead, decompose?_mapH_eq s body, Option.map_map]
      rfl
    | plain i =>
      simp only [decompHead]
      split
      · exact topRedex_mapH g s vs rest
      · rfl
    | ref r => rfl
    | callRefType t => exact topRedex_mapH g s vs rest
    | returnCallRefType t => rfl
    | trap => rfl
termination_by sizeOf code
decreasing_by
  all_goals
    have h := splitVals_snd_sizeOf code
    rw [hsp] at h
    simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec, Admin.handler.sizeOf_spec,
      Admin.frame.sizeOf_spec] at h
    omega

/-! ## Threads -/

theorem config_mapH (s : Store H) (t : Thread) :
    t.config (Store.mapH g s) = Config.mapH g (t.config s) := by
  cases t with
  | pending a args => exact (invoke_mapH g s a args).symm
  | active f code => rfl

theorem decompose?_config_mapH (s : Store H) (t : Thread) :
    decompose? (Store.mapH g s) (t.config (Store.mapH g s)).code =
      (decompose? s (t.config s).code).map (mapR g) := by
  rw [config_mapH, show (Config.mapH g (t.config s)).code = (t.config s).code from rfl]
  exact decompose?_mapH_eq g s _

theorem resumeResult_mapH (s : Store H) (t : Thread) (r : Result) :
    resumeResult (Store.mapH g s) t r = resumeResult s t r := by
  unfold resumeResult
  dsimp only
  rw [decompose?_config_mapH]
  cases decompose? s (t.config s).code with
  | none => rfl
  | some x =>
    simp only [Option.map_some, config_mapH]
    rfl

/-! ## Segmented runs -/

/-- A run of thread `t` from store `s` to `(s', t')`: host-free segments, each but the last
ending at a host callout `h args` that is resumed with the result `r`; the callouts are
recorded with their host code renamed by `g`. -/
inductive SegRun (P : Profile) : Store H → Thread → List (Nat × List Execution.Core.Val × Result) →
    Store H → Thread → Prop
  | done {s s' : Store H} {t t' : Thread} :
      Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (s, t) (s', t') → SegRun P s t [] s' t'
  | call {s s₁ s' : Store H} {t t₁ t' : Thread} {E : Ctx} {a : Nat} {h : H} {args : List Execution.Core.Val}
      {r : Result} {rest : List (Nat × List Execution.Core.Val × Result)} :
      Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (s, t) (s₁, t₁) →
      decompose? s₁ (t₁.config s₁).code = some (E, a, h, args) →
      SegRun P s₁ (resumeResult s₁ t₁ r) rest s' t' →
      SegRun P s t ((g h, args, r) :: rest) s' t'

/-- One callout of a segmented run, on the renamed store. -/
theorem path_callout {P : Profile} {I : Silmaril.Wasm.Game.ScalarInstance} {f : I.F.Op}
    {s₀ s₁ : Store H} {t₀ t₁ : Thread} {E : Ctx} {a : Nat} {h : H}
    {args : List Execution.Core.Val} {q : I.HState}
    (run : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (s₀, t₀) (s₁, t₁))
    (hd : decompose? s₁ (t₁.config s₁).code = some (E, a, h, args)) {x : Round I.E}
    (hx : I.importOp? (g h) args = some x.1) {rest : List (Move I.E I.F)}
    (ih : I.Path P (.running f (Store.mapH g s₁)
      (resumeResult s₁ t₁ (Silmaril.Wasm.Game.Answer.toResult x.2))) rest q) :
    I.Path P (.running f (Store.mapH g s₀) t₀) (.inl (.ask x.1) :: .inl (.ans x.1 x.2) :: rest)
      q := by
  have hco : Silmaril.Wasm.Game.CalloutAt (Store.mapH g s₁) t₁ (g h) args :=
    ⟨E, a, by rw [decompose?_config_mapH, hd]; rfl⟩
  have ih' : I.Path P (.running f (Store.mapH g s₁)
      (resumeResult (Store.mapH g s₁) t₁ (Silmaril.Wasm.Game.Answer.toResult x.2))) rest q := by
    rw [resumeResult_mapH]
    exact ih
  exact .cons (.ucall (reach_mapH g run) hco hx) (.cons (.uret _) ih')

/-- **A segmented run is a path of the instance**: on the renamed store, every callout is the
import question of its renamed host code and arguments, answered by an answer whose result
resumed the thread, and the final result answers the export question. -/
theorem SegRun.path {P : Profile} {I : Silmaril.Wasm.Game.ScalarInstance} {f : I.F.Op}
    {s s' : Store H} {t t' : Thread} {calls : List (Nat × List Execution.Core.Val × Result)}
    (hrun : SegRun g P s t calls s' t') :
    ∀ {cs : List (Round I.E)}, List.Forall₂ (fun (c : Nat × List Execution.Core.Val × Result) x =>
        I.importOp? c.1 c.2.1 = some x.1 ∧ Silmaril.Wasm.Game.Answer.toResult x.2 = c.2.2) calls cs →
      ∀ {r : Result} {w : I.F.Ar f}, Silmaril.Wasm.Game.ResultAt (Store.mapH g s') t' r →
        Silmaril.Wasm.Game.Answer.ofResult? (I.exports.get f.1) r = some w →
        I.Path P (.running f (Store.mapH g s) t) (callMoves cs ++ [.inr (.ans f w)])
          (.idle (Store.mapH g s')) := by
  induction hrun with
  | done run =>
    intro cs hcs r w final hw
    cases hcs
    exact .cons (.oret (reach_mapH g run) final hw) (.nil _)
  | call run hd _ ih =>
    intro cs hcs r w final hw
    cases hcs with
    | cons hx hcs' => exact path_callout g run hd hx.1 (hx.2 ▸ ih hcs' final hw)

end Silmaril.Proofs.Wasm.Component.Reference
