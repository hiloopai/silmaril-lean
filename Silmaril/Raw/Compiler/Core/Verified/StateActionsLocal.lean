module

public import Silmaril.Compiler.Core.Verified.StateReturnLocal.Defs
public import Silmaril.Compiler.Core.Verified.CallArena.Defs

/-! # Local steps for the memory and sequencing operations of State callees -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateActionsLocal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open ConvInt (IsInt isConvLoadedInt)
open IntExpr (spec)
open StateMem (Local Inv Defined defsOf ptr update)
open LoadTask (plain_effectExpr plain_pureExpr plain_value plain_apply Touched)

variable {file : Program} {labels : Labels}

theorem wseq (ann : List Annot) (pat : Pattern Sym) (a b : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.wseq pat a b)) env, k, m⟩
      ⟨.effectExpr a env, .effectBind pat b env :: k, m⟩ :=
  .single (.next (LoadTask.requestAux_wseq m ann pat a b env k false) (plain_effectExpr _ _))

theorem annotations_bind (xs : List Access) (ann : List Annot) (ty : BaseType) (v : Val) (b : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.value v, .annotations xs :: .strongBind (.mk ann (.base (none, ty))) b env :: k, m⟩
      ⟨.effectExpr b env, .annotations xs :: k, m⟩ := by
  exact .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, extendEnv]) (plain_effectExpr _ _))

theorem pure_unit (ann pann : List Annot) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.pure (.mk pann () (.val .unit)))) env, k, m⟩
      ⟨.value .unit, k, focusMemory ann m⟩ :=
  CallLocal.pure ann (fun _ => .val) k m

theorem store (ann a1 a2 a3 a4 a5 c1 c3 : List Annot) (l : Loc) (u : Unit) (x s t : Sym)
    (hs : isConvLoadedInt file s = true) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (ht : env.lookup t = some (spec n)) (hn : IsInt n) (live : Mem.Concrete.LiveInt m id addr) :
    ∃ xs, LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false (Locals.intVal a1 c1)
        (.mk a2 () (.sym x)) (.mk a3 () (.call (.sym s)
          [Locals.intVal a4 c3, .mk a5 () (.sym t)])) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations xs :: k, Locals.stored (focusMemory ann m) id addr n⟩ := by
  refine ⟨[StoreTask.writeAccess k addr], StoreTask.store_local ann l u _ _ _ env k m c1 live hn ?_⟩
  exact .cons .val (.cons (.sym hx) (.cons
    (ConvInt.convLoadedInt_eval (ann := c3) hs hn (.cons .val (.cons (.sym ht) .nil))) .nil))

theorem uninitialized (ann a1 c1 a2 a3 c3 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : Mem.Concrete.LiveInt m id addr) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.store false (Locals.intVal a1 c1) (.mk a2 () (.sym x))
          (.mk a3 () (.val (.loaded (.unspecified (Mem.Concrete.intType c3))))) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [StoreTask.writeAccess k addr] :: k,
        Uninitialized.stored (focusMemory ann m) id addr⟩ := by
  refine (CallLocal.focus (c' := .pureExpr (Locals.intVal a1 c1) env)
    (k' := .arguments (.memory .store) [] [.mk a2 () (.sym x),
      .mk a3 () (.val (.loaded (.unspecified (Mem.Concrete.intType c3))))] env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp only [requestAux, awaitsScheduling, arguments]; rfl
  · have ev : Eval file (tagsOf file (focusMemory ann m)) env
        (.inr [Locals.intVal a1 c1, .mk a2 () (.sym x),
          .mk a3 () (.val (.loaded (.unspecified (Mem.Concrete.intType c3))))])
        (.inr [.ctype (Mem.Concrete.intType c1), .object (.pointer (.allocated id addr)),
          .loaded (.unspecified (Mem.Concrete.intType c3))]) :=
      .cons .val (.cons (.sym hx) (.cons .val .nil))
    refine (PureLocal.args_local file _ ev (.memory .store) [] k
      (focusMemory ann m) rfl).tail ?_
    exact .memory (name := "Store") (by
      simp [requestAux, awaitsScheduling, memoryRequest, toMemory,
        Uninitialized.store_int _ c1 c3 (Locals.liveInt_focus ann live),
        Mem.Concrete.access_int _ c1 (Locals.liveInt_focus ann live),
        StoreTask.writeAccess, bind, Except.bind, pure, Except.pure]
      rfl)

theorem create (ann a1 a2 a3 c1 c2 : List Annot) (l : Loc) (u : Unit) (pref : Prefix)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < Mem.Concrete.nextIntAddress m) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.create (.mk a1 () (.ctor .ivAlignof [Locals.intVal a2 c1])) (Locals.intVal a3 c2) pref))))) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated (focusMemory ann m).nextId
        (Mem.Concrete.nextIntAddress m)))), k, Actions.created pref c2 (focusMemory ann m)⟩ := by
  have ev : Eval file (tagsOf file (focusMemory ann m)) env
      (.inr [.mk a1 () (.ctor .ivAlignof [Locals.intVal a2 c1]), Locals.intVal a3 c2])
      (.inr [.object (.integer 4), .ctype (Mem.Concrete.intType c2)]) :=
    .cons (.ctor (.cons .val .nil) (Locals.alignof_int _ c1)) (.cons .val .nil)
  refine (CallLocal.focus (c' := .pureExpr (.mk a1 () (.ctor .ivAlignof [Locals.intVal a2 c1])) env)
    (k' := .arguments (.memory (.create pref)) [] [Locals.intVal a3 c2] env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp only [requestAux, awaitsScheduling, arguments]; rfl
  · refine (PureLocal.args_local file _ ev (.memory (.create pref)) [] k (focusMemory ann m) rfl).tail ?_
    rw [← Locals.nextIntAddress_focus ann m]
    exact .memory (name := "Create") (by
      simp [requestAux, awaitsScheduling, memoryRequest,
        Mem.Concrete.allocate_int _ c2 (focusMemory ann m)
          (by rw [Locals.nextIntAddress_focus]; exact hpos), Actions.created])

theorem effect_case (ann : List Annot) {p : PE} {body : EE} {bs : List (Pattern Sym × EE)}
    {env : Env} {v : Val} {xs : Bindings}
    (hp : ∀ tags, Eval file tags env (.inl p) (.inl v))
    (hm : selectCase v bs = some (xs, body)) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.effectExpr (.mk ann (.case_ p bs)) env, k, m⟩
      ⟨.effectExpr body (extendEnv xs env), k, focusMemory ann m⟩ := by
  refine (CallLocal.focus (c' := .pureExpr p env) (k' := .effectCase bs env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp [requestAux, awaitsScheduling, focusMemory]; rfl
  · exact (PureLocal.eval_local file _ (hp _) _ _ rfl).tail
      (.next (by simp [requestAux, awaitsScheduling, hm]) (plain_effectExpr _ _))

theorem boolSource_touched {c : Sym} {e : Eff} (h : StmtIf.boolSource c e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (v : Int)
    (hc : env.lookup c = some (spec v)) :
    ∃ m', Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
      ⟨.value (boolean (decide (v ≠ 1))), k, m'⟩ := by
  unfold StmtIf.boolSource at h
  split at h
  · rename_i ann pa c' sa spa z ty ea pif pn pe pz z' pv pt pf ua up un
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc', hz'⟩ := h
    let env' := extendEnv [(z, (.object (.integer v) : Val))] env
    have hsym : env.lookup c' = some (spec v) := by
      rw [ReturnLit.lookup_key hc']; exact hc
    let P : PE := .mk pif () (.if_ (.mk pn () (.not (.mk pe () (.op .eq
      (.mk pz () (.sym z')) (.mk pv () (.val (.object (.integer 1))))))))
      (.mk pt () (.val .true)) (.mk pf () (.val .false)))
    have pre := effect_case (file := file) (labels := labels) (p := .mk pa () (.sym c')) ann
      (fun _ => Eval.sym hsym)
      (SeqReach.select_specified sa ua (.mk spa (.base (some z, ty))) up
        (.mk ea (.pure P)) un (.integer v) (show matchPattern
          (.mk spa (.base (some z, ty))) (.object (.integer v)) =
          some [(z, .object (.integer v))] from rfl)) k m
    have ev (tags : Mem.Concrete.Tags) : Eval file tags env' (.inl P)
        (.inl (boolean (decide (v ≠ 1)))) := by
      have eq : Eval file tags env'
          (.inl (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))
          (.inl (boolean (v == 1))) :=
        .op (.cons (.sym (ConvInt.lookup_one hz')) (.cons .val .nil))
          (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
      have ne : Eval file tags env'
          (.inl (.mk pn () (.not (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))))
          (.inl (boolean (decide (v ≠ 1)))) := by
        apply Eval.not (.cons eq .nil)
        by_cases hv : v = 1 <;> simp [primitive, hv, boolean] <;> rfl
      by_cases hv : v = 1
      · exact .ifFalse (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pf) (v := .false)))
      · exact .ifTrue (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pt) (v := .true)))
    refine ⟨SeqReach.focusMemory ea (SeqReach.focusMemory ann m),
      (StateStmt.seqFocus_touched ann m).trans (StateStmt.seqFocus_touched ea _), pre.trans ?_⟩
    exact CallLocal.pure ea ev k _
  · cases h

end Silmaril.Compile.Core.Verified.StateActionsLocal
