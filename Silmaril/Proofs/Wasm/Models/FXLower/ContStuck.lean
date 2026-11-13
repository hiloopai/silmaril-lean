module

public import Silmaril.Proofs.Wasm.Models.FXLower.SrcInv

/-!
# A continuation reference cannot be branched out of a label (a defect of the FX model)

In `StepFX` the rules that move values (`labelVals`, `brLabelZero`, `brLabelSucc`,
`returnLabel`, `handlerVals`, `frameVals`, …) take Core values `cvals vs` only. A continuation
reference `contRef k` is not a Core value, so no rule moves it. The `suspend` rule leaves
`cvals vs ++ [contRef k, br l]`, which is meant to branch to the handler's label `l` with the
new continuation as its last argument. That branch never happens:

* `contRef_stuck`: code whose first non-value is `contRef j`, not followed by an FX
  instruction, does not step;
* `label_contRef_stuck`: neither does a label around it, which is the configuration `suspend`
  leaves inside the handler's block;
* `suspend_to_label`: the smallest abortive handler, `block` around `resume … (on x 0)` of a
  body that suspends at once, steps to such a label;
* **`suspend_to_label_stuck`**: and then has no behaviours.

So every `(on x l)` handler clause gets stuck at the branch in this model. The lowering of
abortive handlers to `try_table`/`throw` (where the branch does happen) cannot be correct
against `StepFX` as it stands; the model must first treat `contRef` as a value. This is recorded
in docs/projects/spectec/README.md.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The tail does not start with an FX instruction. -/
abbrev NoFXHead (T : List AdminFX) : Prop := ∀ i T', T ≠ .fx i :: T'

theorem noFXHead_prefix {T₁ rest : List AdminFX} (h : NoFXHead (T₁ ++ rest)) : NoFXHead T₁ := by
  intro i T' hT
  exact h i (T' ++ rest) (by rw [hT]; rfl)

/-- The rules on `ref.cont` need an FX instruction next. -/
theorem contRef_rule {vs W : List Val} {k j : Nat} {i : FXInstr} {T : List AdminFX}
    (hT : NoFXHead T) (hx : cvals vs ++ [.contRef k, .fx i] = cvals W ++ .contRef j :: T) :
    False := by
  obtain ⟨-, -, hT'⟩ := cvals_append_cons_inj hx rfl rfl
  exact hT i [] hT'.symm

/-- **A continuation reference not followed by an FX instruction is stuck.** -/
theorem contRef_stuck {x y : ConfigFX H} (h : StepFX P noHost fx x y) :
    ∀ W j T, NoFXHead T → x.code ≠ cvals W ++ .contRef j :: T := by
  induction h with
  | core _ => exact fun W j T _ hx => core_ne_cvals_cons rfl hx
  | seq h _ ih =>
    intro W j T hT hx
    rcases seq_split rfl hx with ⟨V, hV⟩ | ⟨W₂, T₁, rfl, hes, rfl⟩
    · exact no_step_cvals h V hV
    · exact ih W₂ j T₁ (noFXHead_prefix hT) hes
  | contBind | contBindUsed | resume | resumeUsed | resumeThrow =>
    exact fun W j T hT hx => contRef_rule hT hx
  | invoke hc => exact fun W j T _ hx => invoke_ne hc (by simp) hx
  | _ => intro W j T _ hx; fnvX_absurd hx

/-- The body of a label, from an equation of one-instruction codes. -/
theorem label_body {n n' : Nat} {k k' : List InstrFX} {B B' : List AdminFX}
    (h : [AdminFX.label n' k' B'] = [.label n k B]) : B' = B := by
  simp only [List.cons.injEq, AdminFX.label.injEq, and_true] at h
  exact h.2.2

/-- **A label around a stuck continuation reference is stuck.** -/
theorem label_contRef_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
    {k : List InstrFX} {W : List Val} {j : Nat} {T : List AdminFX} (hT : NoFXHead T)
    {y : ConfigFX H} :
    ¬ StepFX P noHost fx ⟨s, K, f, [.label n k (cvals W ++ .contRef j :: T)]⟩ y := by
  intro h
  generalize hx : (⟨s, K, f, [.label n k (cvals W ++ .contRef j :: T)]⟩ : ConfigFX H) = x at h
  have hc : x.code = [.label n k (cvals W ++ .contRef j :: T)] := by rw [← hx]
  cases h with
  | ctxLabel h' => exact contRef_stuck h' W j T hT (label_body hc)
  | seq h' hne => exact no_step_nil h' (seq_single rfl hne hc)
  | labelVals | brLabelZero | brLabelSucc | returnLabel | trapLabel | throwLabel =>
    exact absurd (congrArg fnvX (label_body hc)) (by simp [cthrowing, throwing])
  | _ => fnvX_absurd hc

/-- The smallest abortive handler: `block` around a handler with clause `(on x l)` whose body
suspends at once. -/
def abortSrc (n : Nat) (k : List InstrFX) (hs : List HClause) (vs : List Val) (x : TagIdx) :
    List AdminFX :=
  [.label n k [.handler hs (cvals vs ++ [.fx (.suspend x)])]]

/-- **`suspend` branches to the label with the continuation.** -/
theorem suspend_to_label {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
    {k : List InstrFX} {hs : List HClause} {vs : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFX P noHost fx ⟨s, K, f, abortSrc n k hs vs x⟩
      ⟨s, K ++ [some ⟨Ctx.hole.plug⟩], f,
        [.label n k (cvals vs ++ .contRef K.length :: [.core (.plain (.br l))])]⟩ :=
  StepFX.ctxLabel (StepFX.suspend (E := .hole) ht (by simp [Ctx.Handles]) hc)

/-- **And then it has no behaviours**: the branch with the continuation is stuck. -/
theorem suspend_to_label_stuck (s : Store H) (K : List (Option ContFX)) (f : Frame) (n : Nat)
    (k : List InstrFX) (vs : List Val) (j : Nat) (l : LabelIdx) :
    behavioursFX P noHost fx
      ⟨s, K, f, [.label n k (cvals vs ++ .contRef j :: [.core (.plain (.br l))])]⟩ = ∅ := by
  have hT : NoFXHead [.core (.plain (.br l))] := by simp [NoFXHead]
  have hnr : ∀ r : Result,
      [AdminFX.label n k (cvals vs ++ .contRef j :: [.core (.plain (.br l))])] ≠
        r.toAdmin.map .core := fun r h => by
    have h1 := congrArg (List.all · Silmaril.Proofs.Wasm.Models.FX.isCore) h
    simp [Silmaril.Proofs.Wasm.Models.FX.isCore] at h1
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  rcases hb with ⟨d, r, hrun, hd, -⟩ | ⟨-, hdiv⟩
  · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, -⟩
    · exact hnr r hd
    · exact label_contRef_stuck hT hy
  · obtain ⟨y, hy, -⟩ := hdiv.unfold
    exact label_contRef_stuck hT hy

end Silmaril.Proofs.Wasm.Models.FXLower
