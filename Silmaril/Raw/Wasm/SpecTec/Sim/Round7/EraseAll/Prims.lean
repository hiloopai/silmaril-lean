module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# Round 7, the whole-evaluator erasure: `BIErase` for round 6's primitives (unrefined)

`biErase_BI`: at every `gd` that names neither `$hostcall` nor `$blocktype_`, the builtins of
`utf8Env (Round4Int.BI P hn host)` commute with erasure and keep the swap set. In particular
`Hyps (QC c) grE gdE (utf8Env (BI P hn host))` holds under `StripInj c` (`hyps_BI`).

The argument is **strictness**. Every primitive other than `$hostcall`, `$blocktype_` and `$sx`
answers only at arguments without `EXPORTS` records, and answers a value without one
(`OKS ws o`). A value with an `EXPORTS` record still has one after `eraseV` (`nxB_eraseV`), so at
such arguments both sides fail; at the others `eraseA` is the identity. `$sx` ignores its argument
(`[.val _] => ε`), so it is compared directly (`call_sx_erase`); `$utf8` is strict too.

The primitives are large `match`es; as in `Round7.Determ.ok_call`, each is unfolded into its
decision tree (`dite` on the name, sparse case analyses on the arguments) and walked by a tactic
loop (`xs_tree`). Here the predicate also speaks about the arguments, which the case analyses
substitute along the way, so a leaf is `OKS [explicit argument list] (leaf)`. Kept unrefined: the
trees are walked by a tactic loop.
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.ExecBuiltins (asBits? unBits binBits)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

/-! ## Erasure keeps an `EXPORTS` record -/

mutual
theorem nxB_eraseV : ∀ v : Value, nxB (eraseV v) = nxB v
  | .bool _ => rfl
  | .num _ => rfl
  | .text _ => rfl
  | .tuple vs => by rw [eraseV_tuple, nxB_tuple, nxB_tuple, nxBs_eraseVs vs]
  | .case _ w => by rw [eraseV_case, nxB_case, nxB_case, nxB_eraseV w]
  | .struct gs => by rw [eraseV_struct, nxB_struct, nxB_struct, nxBf_eraseVf gs]
  | .list vs => by rw [eraseV_list, nxB_list, nxB_list, nxBs_eraseVs vs]
  | .opt none => rfl
  | .opt (some w) => by rw [eraseV_opt_some, nxB_opt_some, nxB_opt_some, nxB_eraseV w]

theorem nxBs_eraseVs : ∀ vs : List Value, nxBs (eraseVs vs) = nxBs vs
  | [] => rfl
  | v :: vs => by simp only [eraseVs, nxBs, nxB_eraseV v, nxBs_eraseVs vs]

theorem nxBf_eraseVf : ∀ gs : List (IL.AtomS × Value), nxBf (eraseVf gs) = nxBf gs
  | [] => rfl
  | (a, v) :: gs => by
    rw [eraseVf_cons]
    simp only [nxBf, nxBf_eraseVf gs]
    by_cases ha : a = "EXPORTS"
    · subst ha; simp
    · rw [ite_eq_right ha, nxB_eraseV v]
end

/-! ## Strictness -/

/-- Every value argument of `ws` has no `EXPORTS` record. -/
def ValsNx (ws : List ArgV) : Prop := ∀ w, ArgV.val w ∈ ws → nxB w = true

@[simp] theorem valsNx_nil : ValsNx [] := fun _ h => by cases h

@[simp] theorem valsNx_cons_val (w : Value) (ws : List ArgV) :
    ValsNx (.val w :: ws) ↔ nxB w = true ∧ ValsNx ws := by
  constructor
  · intro h
    exact ⟨h w (List.mem_cons_self ..), fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
  · rintro ⟨h₁, h₂⟩ u hu
    rcases List.mem_cons.1 hu with hu | hu
    · cases hu; exact h₁
    · exact h₂ u hu

theorem valsNx_map_eraseA (ws : List ArgV) : ValsNx (ws.map eraseA) ↔ ValsNx ws := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
    cases a with
    | val w => simp only [List.map_cons, eraseA, valsNx_cons_val, nxB_eraseV, ih]
    | _ =>
      simp only [List.map_cons, eraseA]
      constructor
      · intro h u hu
        rcases List.mem_cons.1 hu with hu | hu
        · cases hu
        · exact ih.1 (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) u hu
      · intro h u hu
        rcases List.mem_cons.1 hu with hu | hu
        · cases hu
        · exact ih.2 (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) u hu

theorem map_eraseA_of_valsNx : ∀ ws : List ArgV, ValsNx ws → ws.map eraseA = ws
  | [], _ => rfl
  | a :: ws, h => by
    have h' : ValsNx ws := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rw [List.map_cons, map_eraseA_of_valsNx ws h']
    cases a with
    | val w => rw [eraseA, eraseV_of_nxB w (h w (List.mem_cons_self ..))]
    | _ => rfl

/-- **Strict with an export-free answer**: `o` answers only if every value argument of `ws` is
export-free, and then with an export-free value. A structure, so that `intro` does not unfold it. -/
structure OKS (ws : List ArgV) (o : Option Value) : Prop where
  ok : ∀ v, o = some v → nxB v = true ∧ ValsNx ws

/-- **A strict primitive commutes with erasure.** -/
theorem erase_of_oks {Q : Value → Prop} {f : List ArgV → Option Value} {ws : List ArgV}
    (h : ∀ ws, OKS ws (f ws)) :
    f (ws.map eraseA) = (f ws).map eraseV ∧ ∀ u, f ws = some u → AllIn Q u := by
  refine ⟨?_, fun u hu => allIn_of_nxB Q u ((h ws).ok u hu).1⟩
  by_cases hw : ValsNx ws
  · rw [map_eraseA_of_valsNx ws hw]
    cases hf : f ws with
    | none => rfl
    | some u => simp [eraseV_of_nxB u ((h ws).ok u hf).1]
  · have h₁ : f ws = none := by
      cases hf : f ws with
      | none => rfl
      | some u => exact absurd ((h ws).ok u hf).2 hw
    have h₂ : f (ws.map eraseA) = none := by
      cases hf : f (ws.map eraseA) with
      | none => rfl
      | some u => exact absurd ((valsNx_map_eraseA ws).1 ((h _).ok u hf).2) hw
    rw [h₁, h₂]
    rfl

/-! ## Walking a decision tree -/

theorem oks_none {ws : List ArgV} : OKS ws none := ⟨fun _ h => by cases h⟩

theorem oks_dite {ws : List ArgV} {c : Prop} {inst : Decidable c} {t : c → Option Value}
    {e : ¬c → Option Value} (ht : ∀ h, OKS ws (t h)) (he : ∀ h, OKS ws (e h)) :
    OKS ws (dite c t e) := by
  cases inst with
  | isTrue hc => exact ht hc
  | isFalse hc => exact he hc

theorem oks_cast {ws : List ArgV} {α : Sort _} {a b : α} {m : Option Value} (h : b = a)
    (hm : OKS ws m) : OKS ws (Eq.ndrec_symm (motive := fun _ => Option Value) m h) := by
  cases h; exact hm

open Lean Meta Elab Tactic in
/-- Reduce the head of the second argument of `OKS`: unfold its head constant once, then
beta/iota-reduce. -/
elab "xs_red" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let e := ty.appArg!
  let some e₁ ← unfoldDefinition? e | throwError "xs_red: cannot unfold"
  let e₂ ← whnfCore e₁
  replaceMainGoal [← (← getMainGoal).change (mkApp ty.appFn! e₂)]

open Lean Meta Elab Tactic in
/-- Split a sparse case analysis (`_sparseCasesOn_k t f g`) in the second argument of `OKS` on
its variable `t`, and reduce the branch taken. -/
elab "xs_sc" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let e := ty.appArg!
  let fn := e.getAppFn
  let some n := fn.constName? | throwError "xs_sc: not a constant"
  unless (n.toString.splitOn "_sparseCasesOn").length > 1 do
    throwError "xs_sc: not a sparse case analysis"
  let some major := e.getAppArgs.find? (·.isFVar) | throwError "xs_sc: no variable"
  let m ← Term.exprToSyntax major
  evalTactic (← `(tactic| (cases $m:term <;> xs_red)))

/-- Walk a decision tree of `dite`, casts and sparse case analyses, closing the leaves with
`leaf`. -/
syntax "xs_tree " tacticSeq : tactic
macro_rules
  | `(tactic| xs_tree $leaf) => `(tactic| repeat' (first
      | exact oks_none
      | contradiction
      | (apply oks_dite <;> intro _)
      | (refine oks_cast (by assumption) ?_)
      | xs_sc
      | ($leaf)))

/-! ## The decoders are strict -/

theorem asBits?_nx {N : Nat} {a : Value} {x : BitVec N} (h : asBits? N a = some x) :
    nxB a = true := by
  unfold asBits? at h
  split at h
  · rfl
  · cases h

theorem asSx?_nx {a : Value} {x : Silmaril.Wasm.Signedness} (h : IntNumeric.asSx? a = some x) :
    nxB a = true := by
  unfold IntNumeric.asSx? at h
  split at h <;> first | rfl | cases h

theorem asPctNat?_nx {a : Value} {x : Nat} (h : IntNumeric.asPctNat? a = some x) :
    nxB a = true := by
  unfold IntNumeric.asPctNat? at h
  split at h
  · rfl
  · cases h

theorem decNum_nx {t : Silmaril.Wasm.NumType} {a : Value} {x : BitVec t.width}
    (h : Floats.decNum t a = some x) : nxB a = true := by
  unfold Floats.decNum at h
  split at h
  · rename_i hx
    obtain ⟨b, hb⟩ := hx
    rw [← hb]
    exact nxB_numV _
  · cases h

theorem decNumType_nx {a : Value} {x : Silmaril.Wasm.NumType} (h : Floats.decNumType a = some x) :
    nxB a = true := by
  unfold Floats.decNumType at h
  split at h
  · rename_i hx
    obtain ⟨b, hb⟩ := hx
    rw [← hb]
    exact nxB_numTypeV _
  · cases h

theorem tyInv_nx {k : Silmaril.Wasm.Validation.TKind} {a : Value} {x : Silmaril.Wasm.Validation.Ty k}
    (h : Prims.tyInv k a = some x) : nxB a = true := by
  unfold Prims.tyInv at h
  split at h
  · rename_i hx
    obtain ⟨b, hb⟩ := hx
    rw [← hb]
    exact nxB_tyV _
  · cases h

theorem charCode?_nx {a : Value} {x : Nat} (h : Round6.MemSimd.charCode? a = some x) :
    nxB a = true := by
  unfold Round6.MemSimd.charCode? at h
  split at h
  · rfl
  · cases h


/-! ## The float primitives -/

/-- Unfold the `do` blocks of a hypothesis `o = some v`. -/
macro "xs_bind" h:ident : tactic => `(tactic|
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Option.map_eq_some_iff] at $h:ident)

section
variable (P : Silmaril.Wasm.Numerics.Profile)
open Silmaril.Wasm

theorem oks_fUn (op : FloatUnOp) (N : Nat) (a : Value) :
    OKS [.val (.num (.natN N)), .val a] (Floats.fUn P op N a) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Floats.fUn] at hv
  xs_bind hv
  obtain ⟨t, -, x, hx, rfl⟩ := hv
  simp [decNum_nx hx]

theorem oks_fBin (op : FloatBinOp) (N : Nat) (a b : Value) :
    OKS [.val (.num (.natN N)), .val a, .val b] (Floats.fBin P op N a b) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Floats.fBin] at hv
  xs_bind hv
  obtain ⟨t, -, x, hx, y, hy, rfl⟩ := hv
  simp [decNum_nx hx, decNum_nx hy]

theorem oks_fRel (op : FloatRelOp) (N : Nat) (a b : Value) :
    OKS [.val (.num (.natN N)), .val a, .val b] (Floats.fRel op N a b) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Floats.fRel] at hv
  xs_bind hv
  obtain ⟨t, -, x, hx, y, hy, rfl⟩ := hv
  exact ⟨rfl, by simp [decNum_nx hx, decNum_nx hy]⟩

theorem oks_wrapBits (N N' : Nat) (a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val a] (Floats.wrapBits N N' a) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Floats.wrapBits] at hv
  xs_bind hv
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨rfl, by simp [asBits?_nx hx]⟩

theorem oks_extendBits (N N' : Nat) (s a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a]
      (Floats.extendBits N N' s a) := by
  refine ⟨fun v hv => ?_⟩
  simp only [Floats.extendBits] at hv
  xs_bind hv
  obtain ⟨sx, hs, x, hx, rfl⟩ := hv
  exact ⟨rfl, by simp [asBits?_nx hx, asSx?_nx hs]⟩

theorem convOpt_nx {op : ConvertOp} {a v : Value} (h : Floats.convOpt P op a = some v) :
    nxB v = true ∧ nxB a = true := by
  simp only [Floats.convOpt] at h
  xs_bind h
  obtain ⟨x, hx, rfl⟩ := h
  refine ⟨?_, decNum_nx hx⟩
  simp only [nxB_opt_map, nxB_numV]
  cases Floats.convRes P op x <;> rfl

theorem convOne_nx {op : ConvertOp} {a v : Value} (h : Floats.convOne P op a = some v) :
    nxB v = true ∧ nxB a = true := by
  simp only [Floats.convOne] at h
  xs_bind h
  obtain ⟨x, hx, z, -, rfl⟩ := h
  exact ⟨nxB_numV _, decNum_nx hx⟩

theorem convList_nx {op : ConvertOp} {a v : Value} (h : Floats.convList P op a = some v) :
    nxB v = true ∧ nxB a = true := by
  simp only [Floats.convList] at h
  xs_bind h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨by simp, decNum_nx hx⟩

theorem oks_convList (op : ConvertOp) (N N' : Nat) (a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val a] (Floats.convList P op a) := by
  refine ⟨fun v hv => ?_⟩
  obtain ⟨h₁, h₂⟩ := convList_nx P hv
  exact ⟨h₁, by simp [h₂]⟩

theorem oks_trunc (N N' : Nat) (s a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] (do
      let t ← Floats.floatOfWidth N
      let i ← Floats.intOfWidth N'
      let sx ← IntNumeric.asSx? s
      Floats.convOpt P (.trunc t i sx) a) := by
  refine ⟨fun v hv => ?_⟩
  xs_bind hv
  obtain ⟨t, -, i, -, sx, hs, hc⟩ := hv
  obtain ⟨h₁, h₂⟩ := convOpt_nx P hc
  exact ⟨h₁, by simp [h₂, asSx?_nx hs]⟩

theorem oks_truncSat (N N' : Nat) (s a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] (do
      let t ← Floats.floatOfWidth N
      let i ← Floats.intOfWidth N'
      let sx ← IntNumeric.asSx? s
      Floats.convOpt P (.truncSat t i sx) a) := by
  refine ⟨fun v hv => ?_⟩
  xs_bind hv
  obtain ⟨t, -, i, -, sx, hs, hc⟩ := hv
  obtain ⟨h₁, h₂⟩ := convOpt_nx P hc
  exact ⟨h₁, by simp [h₂, asSx?_nx hs]⟩

theorem oks_convert (N N' : Nat) (s a : Value) :
    OKS [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] (do
      let i ← Floats.intOfWidth N
      let t ← Floats.floatOfWidth N'
      let sx ← IntNumeric.asSx? s
      Floats.convOne P (.convert i t sx) a) := by
  refine ⟨fun v hv => ?_⟩
  xs_bind hv
  obtain ⟨i, -, t, -, sx, hs, hc⟩ := hv
  obtain ⟨h₁, h₂⟩ := convOne_nx P hc
  exact ⟨h₁, by simp [h₂, asSx?_nx hs]⟩

theorem oks_reinterpret (n₁ n₂ a : Value) :
    OKS [.val n₁, .val n₂, .val a] (do
      let t₁ ← Floats.decNumType n₁
      let t₂ ← Floats.decNumType n₂
      let op ← Floats.reinterpOp? t₁ t₂
      Floats.convOne P op a) := by
  refine ⟨fun v hv => ?_⟩
  xs_bind hv
  obtain ⟨t₁, h₁, t₂, h₂, op, -, hc⟩ := hv
  obtain ⟨h₃, h₄⟩ := convOne_nx P hc
  exact ⟨h₃, by simp [h₄, decNumType_nx h₁, decNumType_nx h₂]⟩


theorem oks_floatCall' (x : IL.Id) (ws : List ArgV) : OKS ws (Floats.floatCall' P x ws) := by
  unfold Floats.floatCall'
  delta Floats.floatCall'.match_1
  xs_tree (first
    | exact oks_fUn P _ _ _
    | exact oks_fBin P _ _ _ _
    | exact oks_fRel _ _ _ _
    | exact oks_wrapBits _ _ _
    | exact oks_extendBits _ _ _ _
    | exact oks_convList P _ _ _ _
    | exact oks_trunc P _ _ _ _
    | exact oks_truncSat P _ _ _ _
    | exact oks_convert P _ _ _ _
    | exact oks_reinterpret P _ _ _)

theorem oks_floatCall (x : IL.Id) (ws : List ArgV) : OKS ws (Floats.floatCall P x ws) := by
  unfold Floats.floatCall
  split
  · exact oks_floatCall' P x ws
  · exact oks_none

end

/-! ## The integer and bitwise primitives -/

theorem oks_unBits (N : Nat) (f : BitVec N → BitVec N) (n : IL.Num) (a : Value) :
    OKS [.val (.num n), .val a] (unBits N f a) := by
  refine ⟨fun v hv => ?_⟩
  unfold unBits at hv
  split at hv
  · rename_i x hx
    cases hv
    exact ⟨rfl, by simp [asBits?_nx hx]⟩
  · cases hv

theorem oks_binBits (N : Nat) (f : BitVec N → BitVec N → BitVec N) (n : IL.Num) (a b : Value) :
    OKS [.val (.num n), .val a, .val b] (binBits N f a b) := by
  refine ⟨fun v hv => ?_⟩
  unfold binBits at hv
  split at hv
  · rename_i x y hx hy
    cases hv
    exact ⟨rfl, by simp [asBits?_nx hx, asBits?_nx hy]⟩
  · cases hv

theorem oks_ternBits (N : Nat) (f : BitVec N → BitVec N → BitVec N → BitVec N) (n : IL.Num)
    (a b c : Value) : OKS [.val (.num n), .val a, .val b, .val c] (FwdSimdAgg.ternBits N f a b c) := by
  refine ⟨fun v hv => ?_⟩
  unfold FwdSimdAgg.ternBits at hv
  split at hv
  · rename_i x y z hx hy hz
    cases hv
    exact ⟨rfl, by simp [asBits?_nx hx, asBits?_nx hy, asBits?_nx hz]⟩
  · cases hv

theorem oks_shiftBits (N : Nat) (f : BitVec N → Nat → BitVec N) (n : IL.Num) (a b : Value) :
    OKS [.val (.num n), .val a, .val b] (IntNumeric.shiftBits N f a b) := by
  refine ⟨fun v hv => ?_⟩
  unfold IntNumeric.shiftBits at hv
  split at hv
  · rename_i x y hx hy
    cases hv
    exact ⟨rfl, by simp [asBits?_nx hx, asPctNat?_nx hy]⟩
  · cases hv

theorem oks_remBits (N : Nat) (n : IL.Num) (s a b : Value) :
    OKS [.val (.num n), .val s, .val a, .val b] (IntNumeric.remBits N s a b) := by
  refine ⟨fun v hv => ?_⟩
  unfold IntNumeric.remBits at hv
  split at hv
  · rename_i sx x y hs hx hy
    cases hv
    refine ⟨?_, by simp [asSx?_nx hs, asBits?_nx hx, asBits?_nx hy]⟩
    simp only [nxB_opt_map]
    cases Silmaril.Wasm.Numerics.irem_ _ _ _ _ <;> rfl
  · cases hv

theorem oks_truncz (q : ℚ) :
    OKS [.val (.num (.ratN q))] (some (.num (.intN (IntNumeric.truncQ q)))) :=
  ⟨fun v hv => by cases hv; exact ⟨rfl, by simp⟩⟩

theorem oks_intCall (x : IL.Id) (ws : List ArgV) : OKS ws (IntNumeric.intCall x ws) := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_3
  xs_tree (first
    | exact oks_unBits _ _ _ _
    | exact oks_binBits _ _ _ _ _
    | exact oks_shiftBits _ _ _ _ _
    | (refine ⟨fun v hv => ?_⟩
       split at hv
       · rename_i hs
         obtain ⟨h₁, h₂⟩ := (oks_shiftBits _ _ (.natN 0) _ _).ok v hv
         simp only [valsNx_cons_val] at h₂
         exact ⟨h₁, by simp [h₂, asSx?_nx hs]⟩
       · cases hv)
    | exact oks_remBits _ _ _ _ _
    | exact oks_truncz _)

theorem oks_vvCall {x : IL.Id} (hx : x ≠ "sx") (ws : List ArgV) :
    OKS ws (FwdSimdAgg.vvCall x ws) := by
  unfold FwdSimdAgg.vvCall
  delta FwdSimdAgg.vvCall.match_1
  xs_tree (first
    | exact oks_unBits _ _ _ _
    | exact oks_binBits _ _ _ _ _
    | exact oks_ternBits _ _ _ _ _ _)


end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
