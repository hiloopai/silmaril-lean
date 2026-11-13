module

public import Silmaril.Wasm.Models.FXRenameSim.Thms
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.Determinism.FamDet
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

/-!
# The target of the abortive lowering has one run to the join

The target `abortTgt W x l ks` is `label_|W|{ks} (handler_|W|{catch x l} (W; throw x))`. Without
host calls, every Core step of it, and of the two configurations after it, is the step of
`tgt_runs` (`Silmaril.Wasm.Models.FXAbort`):

* `tgt_step₀`: `throw x` allocates the exception `⟨ta, W⟩` (the tag's arity is `|W|`, so the
  throw takes all of `W`);
* `tgt_step₁`: the handler catches it and branches with its fields `W`;
* `tgt_step₂`: the branch leaves the label with `W` and continues with `ks`;
* **`tgt_behaviours_sub`**: so every behaviour of the target is a behaviour of the join `W; ks`
  at the store `s.addExn ⟨ta, W⟩` (any profile).

Each inversion takes the step apart with silmaril's `hostFree_head_inv` and a case analysis of
the head rules (`Det.Head`); the other rules are excluded by comparing first non-values
(`Det.fnv`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAbortConv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (hostFree_head_inv)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head fnv famOf famOf_of_shape)
open Silmaril.Wasm.Models.FXAbort
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- Equal codes have equal first non-values. -/
theorem fnv_ne {A B : List Admin} (h : A = B) (hne : fnv A ≠ fnv B) : False := hne (congrArg _ h)

/-- Close a head rule whose instruction family or left-hand side does not match. -/
local macro "head_family" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.TableStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.RefStep.shape ‹_›)).2
      (by simp [famOf])
  | exact absurd (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape ‹_›)).2
      (by simp [famOf])
  | (simp only [Admin.IsCallRef] at *; done)))

/-- Compare the first non-values of a body equation `hb` against the body `hB`. -/
local macro "body_absurd" hB:term:max hb:term:max : tactic => `(tactic| (exfalso; first
  | exact fnv_ne (($hB).symm.trans $hb) (by simp [fnv, Admin.val?])
  | exact fnv_ne (($hb).symm.trans $hB) (by simp [fnv, Admin.val?])))

/-- A `return_call_ref` instruction is not the first non-value `e` of `W; e; r`. -/
theorem rcr_ne {W vs : List Val} {e c : Admin} {r rest : List Admin}
    (h : vals W ++ e :: r = vals vs ++ [c] ++ rest) (he : e.val? = none)
    (hne : ¬ e.IsReturnCallRef) (hc : c.IsReturnCallRef) : False := by
  have h' : vals W ++ e :: r = vals vs ++ c :: rest := by simpa using h
  obtain ⟨-, rfl, -⟩ := Silmaril.Wasm.SingleThreaded.Det.vals_append_cons_inj h' he
    (Silmaril.Wasm.SingleThreaded.Det.IsReturnCallRef.val_none hc)
  exact hne hc

/-! ## Step 0: `throw` -/

/-- The head rules of a handler whose body is `W; throw x`: only the context rule. -/
theorem head_handler_throwBody {s : Store H} {f : Frame} {args : List Val} {m : Nat}
    {cs : List Catch} {B : List Admin} {c₀ : Config H} {W : List Val} {x : TagIdx}
    (hB : B = vals W ++ [.plain (.throw x)]) (h : Head P s f args (.handler m cs B) c₀) :
    args = [] ∧ ∃ s' f' B', Step P noHost ⟨s, f, B⟩ ⟨s', f', B'⟩ ∧
      c₀ = ⟨s', f', [.handler m cs B']⟩ := by
  cases h with
  | ctxtHandler h => exact ⟨rfl, _, _, _, h, rfl⟩
  | brHandler hb => body_absurd hB hb
  | returnCallRefHandler hb hc =>
    exact (rcr_ne (hB.symm.trans hb) rfl (by simp [Admin.IsReturnCallRef]) hc).elim
  | returnHandler hb => body_absurd hB hb
  | handlerVals hb => body_absurd hB hb
  | throwRefHandlerEmpty => body_absurd hB rfl
  | throwRefHandlerCatch => body_absurd hB rfl
  | throwRefHandlerCatchRef => body_absurd hB rfl
  | throwRefHandlerCatchAll => body_absurd hB rfl
  | throwRefHandlerCatchAllRef => body_absurd hB rfl
  | throwRefHandlerNext => body_absurd hB rfl
  | trapHandler => body_absurd hB rfl
  | _ => head_family

/-- The head rule of `throw x`. -/
theorem head_throw {s : Store H} {f : Frame} {args : List Val} {x : TagIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.throw x)) c₀) :
    ∃ ta ti ts, s.tag? f x = some (ta, ti) ∧ Expand ti.type (.func ts .nil) ∧
      args.length = ts.length ∧
      c₀ = ⟨s.addExn ⟨ta, args⟩, f, [.ref (.exn s.exns.length), .plain .throwRef]⟩ := by
  cases h with
  | throw ht he hn => exact ⟨_, _, _, ht, he, hn, rfl⟩
  | _ => head_family

/-- A step of a single administrative instruction that is not a value, trap or `throw_ref`. -/
theorem step_single {s : Store H} {f : Frame} {e : Admin} {c' : Config H} (he : e.val? = none)
    (htrap : e ≠ .trap) (hthrow : e ≠ .plain .throwRef) (h : Step P noHost ⟨s, f, [e]⟩ c') :
    ∃ c₀, Head P s f [] e c₀ ∧ c' = c₀ := by
  obtain ⟨vs, args, c₀, hva, hh, rfl⟩ :=
    hostFree_head_inv (W := []) (rest := []) he htrap hthrow h
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hva.symm
  exact ⟨c₀, hh, by simp⟩

/-- **`throw x` takes all of `W`** (the tag's arity is `|W|`). -/
theorem throw_step {s : Store H} {f : Frame} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (he : Expand ti.type (.func ts .nil)) (hn : W.length = ts.length) {c' : Config H}
    (h : Step P noHost ⟨s, f, vals W ++ [.plain (.throw x)]⟩ c') :
    c' = ⟨s.addExn ⟨ta, W⟩, f, throwing s.exns.length⟩ := by
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := hostFree_head_inv (rest := []) rfl (by simp) (by simp) h
  obtain ⟨ta', ti', ts', ht', he', hn', rfl⟩ := head_throw hh
  rw [ht] at ht'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
  have hts : ts' = ts := by
    have h1 := Silmaril.Wasm.SingleThreaded.Det.Expand.det he' he
    cases h1
    rfl
  subst hts
  have hvs : vs = [] := by
    have h1 := congrArg List.length hW
    simp only [List.length_append] at h1
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hvs
  simp only [List.nil_append] at hW
  subst hW
  simp [vals]

/-- **The first step of the target.** -/
theorem tgt_step₀ {s : Store H} {f : Frame} {W : List Val} {x : TagIdx} {ks : List Instr}
    {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) {c' : Config H}
    (h : Step P noHost ⟨s, f, abortTgt W x l ks⟩ c') :
    c' = ⟨s.addExn ⟨ta, W⟩, f,
      [.label W.length ks [.handler W.length [.catch_ x l] (throwing s.exns.length)]]⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := step_single rfl (by simp) (by simp) h
  cases hh with
  | ctxtLabel h₁ =>
    obtain ⟨c₁, hh₁, rfl⟩ := step_single rfl (by simp) (by simp) h₁
    obtain ⟨-, s', f', B', hB', hc⟩ := head_handler_throwBody rfl hh₁
    have h2 := throw_step ht he hn hB'
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj h2
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
    rfl
  | labelVals hb => body_absurd rfl hb
  | brLabelZero hb => body_absurd rfl hb
  | brLabelSucc hb => body_absurd rfl hb
  | returnLabel hb => body_absurd rfl hb
  | returnCallRefLabel hb hc =>
    exact (rcr_ne (W := []) hb rfl (by simp [Admin.IsReturnCallRef]) hc).elim
  | _ => head_family

/-! ## Step 1: the handler catches -/

/-- The head rules of `catch x l` around the exception `a` with tag `x`: the catch. -/
theorem handler_catch_head {s : Store H} {f : Frame} {W : List Val} {x : TagIdx} {ta : Nat}
    {l : LabelIdx} {a n : Nat} {c₀ : Config H} (hx : s.exns[a]? = some ⟨ta, W⟩)
    (htag : f.module.tags[x.toNat]? = some ta)
    (hh : Head P s f [] (.handler n [.catch_ x l] (throwing a)) c₀) :
    c₀ = ⟨s, f, vals W ++ [.plain (.br l)]⟩ := by
  cases hh with
  | ctxtHandler h₂ => exact (Silmaril.Wasm.SingleThreaded.Det.not_step_throwing h₂).elim
  | throwRefHandlerCatch he' _ =>
    have hW : _ = (⟨ta, W⟩ : ExnInst) := Option.some.inj (he'.symm.trans hx)
    rw [hW]
  | throwRefHandlerNext hm => exact (hm ⟨_, _, hx, htag, rfl⟩).elim
  | brHandler hb => body_absurd rfl hb
  | returnCallRefHandler hb hc =>
    exact (rcr_ne (W := [.ref (.exn a)]) hb rfl (by simp [Admin.IsReturnCallRef]) hc).elim
  | returnHandler hb => body_absurd rfl hb
  | handlerVals hb => body_absurd rfl hb
  | _ => head_family

/-- **The second step of the target.** -/
theorem tgt_step₁ {s : Store H} {f : Frame} {W : List Val} {x : TagIdx} {ks : List Instr}
    {ta : Nat} {l : LabelIdx} {a : Nat} (hx : s.exns[a]? = some ⟨ta, W⟩)
    (htag : f.module.tags[x.toNat]? = some ta) {c' : Config H}
    (h : Step P noHost
      ⟨s, f, [.label W.length ks [.handler W.length [.catch_ x l] (throwing a)]]⟩ c') :
    c' = ⟨s, f, [.label W.length ks (vals W ++ [.plain (.br l)])]⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := step_single rfl (by simp) (by simp) h
  cases hh with
  | ctxtLabel h₁ =>
    obtain ⟨c₁, hh₁, rfl⟩ := step_single rfl (by simp) (by simp) h₁
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (handler_catch_head hx htag hh₁)
    rfl
  | labelVals hb => body_absurd rfl hb
  | brLabelZero hb => body_absurd rfl hb
  | brLabelSucc hb => body_absurd rfl hb
  | returnLabel hb => body_absurd rfl hb
  | returnCallRefLabel hb hc =>
    exact (rcr_ne (W := []) hb rfl (by simp [Admin.IsReturnCallRef]) hc).elim
  | _ => head_family

/-! ## Step 2: the branch leaves the label -/

/-- The arguments of `br` at label depth 0 in `W; br l`. -/
theorem brZero_args {W vs' vs : List Val} {l l' : LabelIdx} {rest : List Admin}
    (hb : vals W ++ [Admin.plain (.br l)] = vals vs' ++ vals vs ++ [.plain (.br l')] ++ rest)
    (hn : vs.length = W.length) : vs = W := by
  have h' : vals [] ++ (vals W ++ Admin.plain (.br l) :: []) =
      vals vs' ++ (vals vs ++ Admin.plain (.br l') :: rest) := by
    simpa using hb
  obtain ⟨hV, -, -⟩ := Silmaril.Wasm.SingleThreaded.Det.vals_append_vals_cons_inj h' rfl rfl
  exact (List.append_inj' hV hn.symm).2.symm

/-- The label of `br` in `W; br l`. -/
theorem br_label {W vs : List Val} {l l' : LabelIdx} {rest : List Admin}
    (hb : vals W ++ [Admin.plain (.br l)] = vals vs ++ [.plain (.br l')] ++ rest) : l' = l := by
  have h' : vals W ++ Admin.plain (.br l) :: [] = vals vs ++ Admin.plain (.br l') :: rest := by
    simpa using hb
  obtain ⟨-, he, -⟩ := Silmaril.Wasm.SingleThreaded.Det.vals_append_cons_inj h' rfl rfl
  simp only [Admin.plain.injEq, Instr.br.injEq] at he
  exact he.symm

/-- `W; br l` does not step. -/
theorem br_body_stuck {s s' : Store H} {f f' : Frame} {W : List Val} {l : LabelIdx}
    {B' : List Admin} (h : Step P noHost ⟨s, f, vals W ++ [.plain (.br l)]⟩ ⟨s', f', B'⟩) :
    False :=
  Silmaril.Wasm.SingleThreaded.Det.not_step_blocked h (W := W) (rest := [])
    (by simp [fnv, Admin.val?]) (.inl ⟨l, rfl⟩)

/-- **The third step of the target.** -/
theorem tgt_step₂ {s : Store H} {f : Frame} {W : List Val} {ks : List Instr} {l : LabelIdx}
    (hl : l.toNat = 0) {c' : Config H}
    (h : Step P noHost ⟨s, f, [.label W.length ks (vals W ++ [.plain (.br l)])]⟩ c') :
    c' = ⟨s, f, abortJoin W ks⟩ := by
  obtain ⟨c₀, hh, rfl⟩ := step_single rfl (by simp) (by simp) h
  generalize hB : vals W ++ [Admin.plain (.br l)] = B at hh
  cases hh with
  | ctxtLabel h₁ => exact (br_body_stuck (hB ▸ h₁)).elim
  | brLabelZero hb _ hn' => rw [brZero_args (hB.trans hb) hn']; rfl
  | brLabelSucc hb hl' => exact absurd (br_label (hB.trans hb) ▸ hl') (by omega)
  | labelVals hb => body_absurd hB.symm hb
  | returnLabel hb => body_absurd hB.symm hb
  | returnCallRefLabel hb hc =>
    exact (rcr_ne (hB.trans hb) rfl (by simp [Admin.IsReturnCallRef]) hc).elim
  | throwRefLabel => body_absurd hB.symm rfl
  | trapLabel => body_absurd hB.symm rfl
  | _ => head_family

/-! ## Behaviours -/

/-- Behaviours of a Core configuration from those of its successors. -/
theorem behavioursOf_sub_of_succ {host : HostSemantics H} {c : Config H}
    {B : Set (Behaviour Val)} (hnr : ∀ r : Result, c.code ≠ r.toAdmin)
    (h : ∀ c', Step P host c c' → behavioursOf P host c' ⊆ B) : behavioursOf P host c ⊆ B := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, hrest⟩
    · exact absurd hd (hnr r)
    · exact h y hy (Or.inl ⟨d, r, hrest, hd, rfl⟩)
  · obtain ⟨y, hy, htr⟩ := Silmaril.InfiniteTrace.unfold hdiv
    exact h y hy (Or.inr ⟨rfl, htr⟩)

/-- A single label is not a result. -/
theorem label_not_result {n : Nat} {k : List Instr} {B : List Admin} (r : Result) :
    [Admin.label n k B] ≠ r.toAdmin := by
  cases r with
  | values vs =>
    intro h
    have h1 := congrArg fnv h
    simp [fnv, Admin.val?, Result.toAdmin] at h1
  | throw a => simp [Result.toAdmin]
  | trap => simp [Result.toAdmin]

/-- **Every behaviour of the target is a behaviour of the join at `s.addExn ⟨ta, W⟩`.** -/
theorem tgt_behaviours_sub {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ ⊆
      behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ := by
  have hx : (s.addExn ⟨ta, W⟩).exns[s.exns.length]? = some ⟨ta, W⟩ := by
    simp [Store.addExn]
  refine behavioursOf_sub_of_succ label_not_result fun c₁ h₁ => ?_
  rw [tgt_step₀ ht he hn h₁]
  refine behavioursOf_sub_of_succ label_not_result fun c₂ h₂ => ?_
  rw [tgt_step₁ hx (Silmaril.Proofs.Wasm.Models.FXAbort.tag?_module ht) h₂]
  refine behavioursOf_sub_of_succ label_not_result fun c₃ h₃ => ?_
  rw [tgt_step₂ hl h₃]

end Silmaril.Proofs.Wasm.Models.FXAbortConv
