module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Shape

/-!
# Simulation: instructions that stay in the top frame

A kernel step of `push`, `prim`, `drop` or `contNew` is matched by one or two `StepFX'` steps in
the top frame of the encoded stack (`sim_same`), and the relation `Rel` is restored with the
top frame's operands and code updated.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- A kernel step is matched: a positive `StepFX'` run to a related configuration. -/
def SimGoal (S : Setup H) (W : Prog (Ins Val)) (c₀ : ConfigFX H) (x' : SCfg Val) : Prop :=
  ∃ c', Relation.TransGen (SX S) c₀ c' ∧ Rel S W x' c'

/-- **A step inside the top frame.** -/
theorem sim_same {KK' : List (Option (List (SFrame Val)))} {K K' : List (Option ContFX)}
    {p p' : SFrame Val × Ann} {rs : List (SFrame Val × Ann)} (hmain : MainOk S W (p :: rs))
    (hp' : FrOk S W p') (hk : p'.2.kind = p.2.kind) (hK' : List.Forall₂ (KRel S W) KK' K')
    (hrun : Relation.TransGen (FS S ((outer S rs p.2.kind).frameAt S.f0))
      (K, fvals (opsF p.1.ops) ++ adm p.2.code) (K', fvals (opsF p'.1.ops) ++ adm p'.2.code)) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S (p :: rs)).plug []⟩ ⟨KK', p'.1 :: rs.map Prod.fst⟩ := by
  refine ⟨⟨S.s, K', S.f0, (stkCtx S (p' :: rs)).plug []⟩, ?_, ?_⟩
  · rw [code_top, code_top, hk]
    exact fplus_plus (fplus_lift _ hrun)
  · exact ⟨rfl, rfl, hK', p' :: rs, rfl, mainOk_top S hmain hp' hk, rfl⟩

/-- The frame at the top of a well-formed main stack belongs to `M`. -/
theorem top_module (hok : Ok S W) {p : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (hmain : MainOk S W (p :: rs)) : ((outer S rs p.2.kind).frameAt S.f0).module = S.M :=
  outer_module S hok p rs hmain.1

/-- `push v`. -/
theorem sim_push {K : List (Option ContFX)} {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {v : Val} {i : Instr}
    {c : List (Ins Val)} {Y : List InstrFX} (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K)
    (hY : a.code = .core i :: .core .nop :: Y) (hv : Admin.plain i = v.toAdmin)
    (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, { fr with code := c, ops := .val v :: fr.ops } :: rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine sim_same S (p' := ({ fr with code := c, ops := .val v :: fr.ops }, { a with code := Y }))
    hmain ⟨henc, hfr.2⟩ rfl hK (.single ?_)
  have h := step_nop S (K := K) (F := (outer S rs a.kind).frameAt S.f0) (opsF fr.ops ++ [.val v])
    (adm Y)
  simpa only [hY, adm, List.map_cons, InstrFX.toAdmin, fvals_append, fvals_val1, hv, opsF_cons,
    toF, List.append_assoc, List.cons_append, List.nil_append] using h

/-- `drop`. -/
theorem sim_drop {K : List (Option ContFX)} {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {x : SV Val} {o : List (SV Val)}
    {c : List (Ins Val)} {Y : List InstrFX} (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) (hops : fr.ops = x :: o)
    (hY : a.code = .core .drop :: Y) (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, { fr with code := c, ops := o } :: rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine sim_same S (p' := ({ fr with code := c, ops := o }, { a with code := Y }))
    hmain ⟨henc, hfr.2⟩ rfl hK (.single ?_)
  have hcode : fvals (opsF fr.ops) ++ adm a.code =
      fvals (opsF o ++ [toF x]) ++ .core (.plain .drop) :: adm Y := by
    rw [hops, hY, opsF_cons]
    rfl
  rw [hcode]
  match x with
  | .val v => exact step_dropVal S (opsF o) (adm Y) v
  | .cont k => exact step_dropCont S (opsF o) (adm Y) k

/-- The operands of a `prim` are `i32`s. -/
theorem i32s_of_all {a : List (SV Val)} (h : a.all isI32 = true) :
    ∃ bs : List (BitVec 32), a = (bs.map Val.i32).map .val := by
  induction a with
  | nil => exact ⟨[], rfl⟩
  | cons x a ih =>
    have hx : isI32 x = true ∧ a.all isI32 = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using h
    obtain ⟨bs, rfl⟩ := ih hx.2
    match x, hx.1 with
    | .val (.num ⟨.int .i32, b⟩), _ => exact ⟨b :: bs, rfl⟩

theorem allVals_map (vs : List Val) : allVals (vs.map SV.val) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, allVals, ih, Option.map_some]

theorem opsF_vals (vs : List Val) : opsF (vs.map SV.val) = vs.reverse.map .val :=
  opsF_of_allVals (allVals_map vs)

/-- `prim n op` on `i32` operands. -/
theorem sim_prim (hok : Ok S W) {K : List (Option ContFX)} {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {n : Nat}
    {op : List Val → List Val} {i : Instr} {c : List (Ins Val)} {Y : List InstrFX}
    {bs : List (BitVec 32)} {o : List (SV Val)} (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) (hops : fr.ops = (bs.map Val.i32).map .val ++ o)
    (hn : bs.length = n) (hY : a.code = .core i :: Y) (hi : PrimOk S n op i)
    (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, { fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o } ::
        rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine sim_same S (p' := ({ fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o },
    { a with code := Y })) hmain ⟨henc, hfr.2⟩ rfl hK (.single ?_)
  have h := step_prim S (K := K) hi (top_module S hok hmain) bs hn (opsF o) (adm Y)
  simpa only [hops, hY, opsF_append, opsF_vals, fvals_append, adm, List.map_cons,
    InstrFX.toAdmin, List.append_assoc, List.cons_append, List.nil_append] using h

/-- `contNew f`. -/
theorem sim_contNew (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {f : Nat} {bf : List (Ins Val)} {c : List (Ins Val)}
    {Y : List InstrFX} (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hY : a.code = .core (.refFunc (S.xf f)) :: .fx (.contNew S.ct) :: Y)
    (hf : W f = some (0, bf)) (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK ++ [some [⟨bf, [], none⟩]],
        { fr with code := c, ops := .cont KK.length :: fr.ops } :: rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨-, fi, h, Yb, hx, hfi, -, -, -⟩ := hok.funcs f 0 bf hf
  have hlen : KK.length = K.length := hK.length_eq
  have hK' : List.Forall₂ (KRel S W) (KK ++ [some [⟨bf, [], none⟩]])
      (K ++ [some (freshK (S.fa f) fi)]) :=
    List.rel_append hK (.cons (Or.inl ⟨f, bf, fi, hf, hfi, rfl, rfl⟩) .nil)
  refine sim_same S (p' := ({ fr with code := c, ops := .cont KK.length :: fr.ops },
    { a with code := Y })) hmain ⟨henc, hfr.2⟩ rfl hK' ?_
  have h := run_contNew S (K := K) hx hfi (top_module S hok hmain) (opsF fr.ops) (adm Y)
  simpa only [hY, hlen, adm, List.map_cons, InstrFX.toAdmin, opsF_cons, toF] using h

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
