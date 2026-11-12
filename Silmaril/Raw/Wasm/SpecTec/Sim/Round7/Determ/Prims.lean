module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Prims
public import Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.Thms

/-!
# Round 7, determination: round 6's primitives preserve `ExpFree` (unrefined)

`builtinsEF_BI`: at an export-blind host, `Round4Int.BI P hn host` answers an `ExpFree` value at
`ExpFree` arguments.

The primitives are defined by large `match`es on the name and the argument shapes, whose
splitters are too expensive to build (`split` times out). So the proof unfolds each `match` into
its decision tree (`dite` on the name, sparse case analyses on the arguments) and walks the tree
with congruence lemmas for `OKV`, "every answer passes `efB`": `ok_dite`, `ok_cast`, `ok_bind`,
and the tactic `ok_sc`, which splits a sparse case analysis on its variable and reduces the
branch taken. The leaves are the value encoders, whose images pass `efB` by unfolding. Kept
unrefined: the trees are walked by a tactic loop.
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

/-! ## Walking a decision tree -/

/-- **Every answer of `o` passes `efB`.** A structure, so that `intro` does not unfold it. -/
structure OKV (o : Option Value) : Prop where
  ok : ∀ v, o = some v → efB v = true

theorem ok_none : OKV none := ⟨fun _ h => by cases h⟩

theorem ok_some {v : Value} (h : efB v = true) : OKV (some v) :=
  ⟨fun w hw => by cases hw; exact h⟩

theorem ok_pure {v : Value} (h : efB v = true) : OKV (pure v) := ok_some h

theorem ok_dite {c : Prop} {inst : Decidable c} {t : c → Option Value} {e : ¬c → Option Value}
    (ht : ∀ h, OKV (t h)) (he : ∀ h, OKV (e h)) : OKV (dite c t e) := by
  cases inst with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

theorem ok_ite {c : Prop} {inst : Decidable c} {t e : Option Value} (ht : OKV t) (he : OKV e) :
    OKV (ite c t e) := by
  cases inst with
  | isTrue _ => exact ht
  | isFalse _ => exact he

theorem ok_cast {α : Sort _} {a b : α} {m : Option Value} (h : b = a) (hm : OKV m) :
    OKV (Eq.ndrec_symm (motive := fun _ => Option Value) m h) := by cases h; exact hm

theorem ok_bind {α : Type} {o : Option α} {f : α → Option Value} (hf : ∀ a, OKV (f a)) :
    OKV (o.bind f) := by
  refine ⟨fun v hv => ?_⟩
  cases o with
  | none => cases hv
  | some a => exact (hf a).ok v hv

theorem ok_map {α : Type} {o : Option α} {f : α → Value} (hf : ∀ a, efB (f a) = true) :
    OKV (o.map f) := by
  refine ⟨fun v hv => ?_⟩
  cases o with
  | none => cases hv
  | some a => cases hv; exact hf a

theorem ok_orElse {a b : Option Value} (ha : OKV a) (hb : OKV b) : OKV (a <|> b) := by
  refine ⟨fun v hv => ?_⟩
  cases a with
  | none => exact hb.ok v hv
  | some w => exact ha.ok v hv

theorem ok_optCasesOn {α : Type} {o : Option α} {n : Option Value} {f : α → Option Value}
    (hn : OKV n) (hf : ∀ a, OKV (f a)) : OKV (Option.casesOn (motive := fun _ => Option Value) o n f) := by
  cases o with
  | none => exact hn
  | some a => exact hf a

theorem ok_pure_list_map {α : Type} {l : List α} {f : α → Value} (hf : ∀ a, efB (f a) = true) :
    OKV (pure (Value.list (l.map f))) :=
  ok_pure (by simp only [efB_list, efBs_map, List.all_eq_true]; exact fun a _ => hf a)

theorem ok_some_list_map {α : Type} {l : List α} {f : α → Value} (hf : ∀ a, efB (f a) = true) :
    OKV (some (Value.list (l.map f))) := ok_pure_list_map hf

theorem ok_pure_opt_map {α : Type} {o : Option α} {f : α → Value} (hf : ∀ a, efB (f a) = true) :
    OKV (pure (Value.opt (o.map f))) :=
  ok_pure (by cases o with | none => rfl | some a => exact hf a)

open Lean Meta Elab Tactic in
/-- Reduce the head of the argument of `OKV`: unfold its head constant once, then
beta/iota-reduce. -/
elab "ok_red" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let e := ty.appArg!
  let some e₁ ← unfoldDefinition? e | throwError "ok_red: cannot unfold"
  let e₂ ← whnfCore e₁
  replaceMainGoal [← (← getMainGoal).change (mkApp ty.appFn! e₂)]

open Lean Meta Elab Tactic in
/-- Split a sparse case analysis (`_sparseCasesOn_k t f g`) on its variable `t`, and reduce the
branch taken. -/
elab "ok_sc" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let e := ty.appArg!
  let fn := e.getAppFn
  let some n := fn.constName? | throwError "ok_sc: not a constant"
  unless (n.toString.splitOn "_sparseCasesOn").length > 1 do
    throwError "ok_sc: not a sparse case analysis"
  let some major := e.getAppArgs.find? (·.isFVar) | throwError "ok_sc: no variable"
  let m ← Term.exprToSyntax major
  evalTactic (← `(tactic| (cases $m:term <;> ok_red)))

/-- Walk a decision tree of `dite`, casts and sparse case analyses, closing the leaves with
`leaf`. -/
syntax "ok_tree " tacticSeq : tactic
macro_rules
  | `(tactic| ok_tree $leaf) => `(tactic| repeat' (first
      | exact ok_none
      | (apply ok_dite <;> intro _)
      | (refine ok_cast (by assumption) ?_)
      | ok_sc
      | ($leaf)))

/-- Close a leaf of a numeric primitive. -/
syntax "ok_leaf" : tactic
macro_rules
  | `(tactic| ok_leaf) => `(tactic| first
      | (apply ok_pure_list_map; intro _; first | exact efB_floatV _ _ | exact efB_numV _ | rfl)
      | (apply ok_pure_opt_map; intro _; first | exact efB_numV _ | rfl)
      | (apply ok_some_list_map; intro _; first | exact efB_floatV _ _ | exact efB_numV _ | rfl)
      | (apply ok_pure; first | exact efB_numV _ | rfl)
      | (apply ok_some; first | exact efB_numV _ | rfl)
      | (apply ok_bind <;> intro _)
      | (apply ok_map <;> intro _ <;> rfl)
      | (apply ok_ite))

/-! ## The float primitives -/

theorem ok_floatCall' (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKV (Floats.floatCall' P x ws) := by
  unfold Floats.floatCall'
  delta Floats.floatCall'.match_1
  ok_tree ok_leaf

/-! ## The integer and bitwise primitives -/

theorem ok_unBits (N : Nat) (f : BitVec N → BitVec N) (a : Value) :
    OKV (Silmaril.SpecTec.Equiv.ExecBuiltins.unBits N f a) := by
  unfold Silmaril.SpecTec.Equiv.ExecBuiltins.unBits
  split
  · exact ok_some rfl
  · exact ok_none

theorem ok_binBits (N : Nat) (f : BitVec N → BitVec N → BitVec N) (a b : Value) :
    OKV (Silmaril.SpecTec.Equiv.ExecBuiltins.binBits N f a b) := by
  unfold Silmaril.SpecTec.Equiv.ExecBuiltins.binBits
  split
  · exact ok_some rfl
  · exact ok_none

theorem ok_shiftBits (N : Nat) (f : BitVec N → Nat → BitVec N) (a b : Value) :
    OKV (IntNumeric.shiftBits N f a b) := by
  unfold IntNumeric.shiftBits
  split
  · exact ok_some rfl
  · exact ok_none

theorem ok_remBits (N : Nat) (s a b : Value) : OKV (IntNumeric.remBits N s a b) := by
  unfold IntNumeric.remBits
  split
  · exact ok_some (by simp only [efB_opt_map]; cases Silmaril.Wasm.Numerics.irem_ _ _ _ _ <;> rfl)
  · exact ok_none

theorem ok_ternBits (N : Nat) (f : BitVec N → BitVec N → BitVec N → BitVec N) (a b c : Value) :
    OKV (FwdSimdAgg.ternBits N f a b c) := by
  unfold FwdSimdAgg.ternBits
  split
  · exact ok_some rfl
  · exact ok_none

/-- Close a leaf of an integer or bitwise primitive. -/
syntax "ok_bits" : tactic
macro_rules
  | `(tactic| ok_bits) => `(tactic| first
      | exact ok_unBits _ _ _
      | exact ok_binBits _ _ _ _
      | exact ok_shiftBits _ _ _ _
      | exact ok_remBits _ _ _ _
      | exact ok_ternBits _ _ _ _ _
      | exact ok_some rfl
      | (apply ok_optCasesOn <;> intros)
      | (split <;> intros))

theorem ok_intCall (x : IL.Id) (ws : List ArgV) : OKV (IntNumeric.intCall x ws) := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_1
  ok_tree ok_bits

theorem ok_vvCall (x : IL.Id) (ws : List ArgV) : OKV (FwdSimdAgg.vvCall x ws) := by
  unfold FwdSimdAgg.vvCall
  delta FwdSimdAgg.vvCall.match_1
  ok_tree ok_bits

/-! ## Encoders of lists -/

theorem efB_leBytesV (k n : Nat) : efB (.list (FwdMem.leBytesV k n)) = true := by
  simp only [FwdMem.leBytesV, FwdMem.bytesV, efB_list, efBs_map, List.all_eq_true]
  exact fun _ _ => rfl

theorem efB_list_map {α : Type} (l : List α) {f : α → Value} (hf : ∀ a, efB (f a) = true) :
    efB (.list (l.map f)) = true := by
  simp only [efB_list, efBs_map, List.all_eq_true]
  exact fun a _ => hf a

theorem efB_vecsOf (R : Silmaril.Wasm.Numerics.V128 → Prop) :
    efB (.list (Round5.Simd.vecsOf R)) = true := by
  unfold Round5.Simd.vecsOf
  exact efB_list_map _ fun _ => rfl

theorem efB_lanesV (sh : Silmaril.Wasm.Shape) (a : Silmaril.Wasm.Numerics.V128) :
    efB (.list (Round5.Simd.lanesV sh a)) = true := by
  simp only [Round5.Simd.lanesV, efB_list, efBs_map, List.all_eq_true]
  intro x _
  unfold Round5.Simd.laneV
  split
  · rfl
  · exact efB_floatV _ _
  · exact efB_floatV _ _

theorem efB_vecV1 (a : Silmaril.Wasm.Numerics.V128) : efB (.list [Vec.vecV a]) = true := rfl

theorem efB_vecV (a : Silmaril.Wasm.Numerics.V128) : efB (Vec.vecV a) = true := rfl

theorem efB_i32NV (a : BitVec 32) : efB (Vec.i32NV a) = true := rfl

/-! ## The vector primitives -/

theorem ok_someVec (R : Silmaril.Wasm.Numerics.V128 → Prop) : OKV (Round5.Simd.someVec R) := by
  unfold Round5.Simd.someVec
  exact ok_dite (fun _ => ok_some rfl) (fun _ => ok_none)

/-- Close a leaf of a vector primitive. -/
syntax "ok_vec" : tactic
macro_rules
  | `(tactic| ok_vec) => `(tactic| first
      | exact ok_someVec _
      | (apply ok_orElse)
      | (apply ok_map; intro _; first | rfl | exact efB_vecsOf _)
      | (apply ok_bind <;> intro _)
      | (apply ok_ite)
      | exact ok_some rfl)

section
attribute [local irreducible] Round5.Simd.vecsOf Round5.Simd.decodeArgs

theorem ok_vecOpCall (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKV (Round5.Simd.vecOpCall P x ws) := by
  unfold Round5.Simd.vecOpCall
  delta Round5.Simd.vecOpCall.match_1
  repeat' (first
      | exact ok_none
      | (apply ok_dite <;> intro _)
      | (refine ok_cast (by assumption) ?_))
  all_goals beta_reduce
  · exact ok_orElse (ok_map fun _ => efB_vecV1 _) (ok_map fun _ => efB_vecsOf _)
  · exact ok_orElse (ok_map fun _ => efB_vecV1 _) (ok_map fun _ => efB_vecsOf _)
  · exact ok_orElse (ok_map fun _ => efB_vecV1 _) (ok_map fun _ => efB_vecsOf _)
  · exact ok_orElse (ok_map fun _ => efB_vecV _) (ok_map fun _ => efB_vecV _)
  · exact ok_map fun _ => efB_vecV _
  · exact ok_map fun _ => efB_i32NV _
  · exact ok_map fun _ => efB_vecV _
  · exact ok_bind fun _ => ok_ite (ok_some (efB_vecV _)) ok_none
  · exact ok_bind fun _ => ok_someVec _
  · exact ok_bind fun _ => ok_someVec _
  · exact ok_bind fun _ => ok_someVec _
  · exact ok_bind fun _ => ok_someVec _
  · exact ok_bind fun _ => ok_someVec _
end

theorem ok_lanesCall (sv v : Value) : OKV (Round5.Simd.lanesCall sv v) := by
  unfold Round5.Simd.lanesCall
  exact ok_dite (fun _ => ok_some (efB_lanesV _ _)) (fun _ => ok_none)

theorem ok_invLanesCall (sv lv : Value) : OKV (Round5.Simd.invLanesCall sv lv) := by
  unfold Round5.Simd.invLanesCall
  exact ok_dite (fun _ => ok_some rfl) (fun _ => ok_none)

/-! ## The memory, type and instance primitives -/

theorem ok_nbytesCall (nt c : Value) : OKV (FwdMem.nbytesCall nt c) := by
  unfold FwdMem.nbytesCall
  exact ok_bind fun _ => ok_bind fun _ => ok_pure (efB_leBytesV _ _)

theorem ok_ibytesCall (N c : Value) : OKV (FwdMem.ibytesCall N c) := by
  unfold FwdMem.ibytesCall
  delta FwdMem.ibytesCall.match_1
  ok_tree (exact ok_some (efB_leBytesV _ _))

theorem ok_zbytesCall (zt c : Value) : OKV (ZBytes.zbytesCall zt c) := by
  unfold ZBytes.zbytesCall
  delta ZBytes.zbytesCall.match_1
  ok_tree (first | exact ok_ibytesCall _ _ | exact ok_nbytesCall _ _)

theorem ok_unrolldtCall (v : Value) : OKV (Prims.unrolldtCall v) := by
  unfold Prims.unrolldtCall
  exact ok_bind fun _ => ok_bind fun _ => ok_some (efB_tyV _)

theorem ok_blocktypeCall (z xv : Value) : OKV (Prims.blocktypeCall z xv) := by
  unfold Prims.blocktypeCall
  refine ok_bind fun _ => ok_bind fun _ => ok_bind fun _ => ok_bind fun _ => ok_bind fun _ =>
    ok_some ?_
  simp [Exn.instrTypeV]

theorem ok_growtableCall (tv nv rv : Value) : OKV (Prims.growtableCall tv nv rv) := by
  unfold Prims.growtableCall
  refine ok_dite (fun _ => ok_map fun _ => ?_) (fun _ => ok_none)
  simp [tableInstToValue, CT]

theorem ok_growmemCall (mv nv : Value) : OKV (Prims.growmemCall mv nv) := by
  unfold Prims.growmemCall
  refine ok_dite (fun _ => ok_map fun _ => ?_) (fun _ => ok_none)
  simp [memInstToValue, efB_bytesToValue]

theorem ok_floatCall (P : Silmaril.Wasm.Numerics.Profile) (x : IL.Id) (ws : List ArgV) :
    OKV (Floats.floatCall P x ws) := by
  unfold Floats.floatCall
  exact ok_ite (ok_floatCall' P x ws) ok_none

theorem ok_hostcallCall {H : Type} (hn : H → String)
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} (hb : Round7.HostExportBlind host)
    {ws : List ArgV} (hw : ∀ w, ArgV.val w ∈ ws → efB w = true) :
    OKV (Prims.hostcallCall hn host ws) :=
  ⟨fun _ h => efB_hostcallCall hn hb hw h⟩

/-! ## All of round 6's primitives -/

section
attribute [local irreducible] Prims.hostcallCall Prims.unrolldtCall Prims.blocktypeCall
  Prims.growtableCall Prims.growmemCall FwdMem.nbytesCall FwdMem.ibytesCall ZBytes.zbytesCall
  FwdSimdAgg.vvCall Round5.Simd.lanesCall Round5.Simd.invLanesCall Round5.Simd.vecOpCall

theorem ok_call {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} (hb : Round7.HostExportBlind host)
    (x : IL.Id) {ws : List ArgV} (hw : ∀ w, ArgV.val w ∈ ws → efB w = true) :
    OKV (Prims.call P hn host x ws) := by
  unfold Prims.call
  split
  · rename_i v hv
    exact ok_some ((ok_floatCall P x ws).ok v hv)
  · split
    · rename_i v hv
      exact ok_some ((ok_intCall x ws).ok v hv)
    · delta Prims.call.match_1
      ok_tree (first
        | exact ok_hostcallCall hn hb hw
        | exact ok_unrolldtCall _
        | exact ok_blocktypeCall _ _
        | exact ok_growtableCall _ _ _
        | exact ok_growmemCall _ _
        | exact ok_nbytesCall _ _
        | exact ok_ibytesCall _ _
        | exact ok_zbytesCall _ _
        | exact ok_vvCall _ _
        | exact ok_lanesCall _ _
        | exact ok_invLanesCall _ _
        | exact ok_vecOpCall _ _ _)
end

/-- **Round 6's primitives preserve `ExpFree`** at an export-blind host. -/
theorem builtinsEF_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} (hb : Round7.HostExportBlind host) :
    BuiltinsEF (Round4Int.BI P hn host) := by
  intro x ws v hw h
  have hw' : ∀ w, ArgV.val w ∈ ws → efB w = true := fun w hmem => efB_of_expFree (hw w hmem)
  exact expFree_of_efB _ ((ok_call P hn hb x hw').ok v h)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
