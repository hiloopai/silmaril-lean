module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Ctx

/-!
# `StepFX'` steps of the encoded instructions, at one frame

Each lemma runs the WasmFX code of one kernel instruction under a value prefix `O` and a code
suffix `R`, at a frame `F` of the module `M`:

* `step_core`, `step_nop`, `step_prim`, `step_dropVal`, `step_dropCont`: one Core step;
* `run_call`: `call x` reaches the FX function's frame with its parameters pushed (`call`,
  the FX `invoke` rule, then one `local.get` per parameter, `run_localGets`);
* `run_contNew`: `ref.func x; cont.new` stores a fresh continuation;
* `step_block`, `step_if`, `step_resume`: block entry, `if`, and `resume`.

Also the bookkeeping of operand stacks (`opsF`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type}

/-- The step relation of a setting. -/
abbrev SX (S : Setup H) := StepFX' S.P S.host S.fx

/-! ## Operand stacks -/

@[simp] theorem opsF_nil : opsF ([] : List (SV Val)) = [] := rfl

theorem opsF_cons (x : SV Val) (o : List (SV Val)) : opsF (x :: o) = opsF o ++ [toF x] := by
  simp only [opsF, List.map_cons, List.reverse_cons]

theorem opsF_append (a o : List (SV Val)) : opsF (a ++ o) = opsF o ++ opsF a := by
  simp only [opsF, List.map_append, List.reverse_append]

theorem opsF_length (o : List (SV Val)) : (opsF o).length = o.length := by
  simp only [opsF, List.length_reverse, List.length_map]

theorem opsF_of_allVals {a : List (SV Val)} {ws : List Val} (h : allVals a = some ws) :
    opsF a = ws.reverse.map .val := by
  induction a generalizing ws with
  | nil =>
    have hws : ws = [] := by simpa only [allVals, Option.some.injEq, eq_comm] using h
    simp only [hws, opsF_nil, List.reverse_nil, List.map_nil]
  | cons x a ih =>
    match x, h with
    | .val v, h =>
      obtain ⟨ws', hws', rfl⟩ : ∃ ws', allVals a = some ws' ∧ v :: ws' = ws := by
        simpa only [allVals, Option.map_eq_some_iff] using h
      simp only [opsF_cons, ih hws', toF, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]

theorem allVals_length {a : List (SV Val)} {ws : List Val} (h : allVals a = some ws) :
    ws.length = a.length := by
  induction a generalizing ws with
  | nil => simp only [allVals, Option.some.injEq] at h; subst h; rfl
  | cons x a ih =>
    match x, h with
    | .val v, h =>
      obtain ⟨ws', hws', rfl⟩ : ∃ ws', allVals a = some ws' ∧ v :: ws' = ws := by
        simpa only [allVals, Option.map_eq_some_iff] using h
      simp only [List.length_cons, ih hws']

@[simp] theorem fvals_val1 (v : Val) : fvals [FVal.val v] = [AdminFX.core v.toAdmin] := rfl

@[simp] theorem fvals_cont1 (k : Nat) : fvals [FVal.cont k] = [AdminFX.contRef k] := rfl

theorem fvals_vals_map (ws : List Val) : fvals (ws.map .val) = (vals ws).map .core :=
  fvals_val ws

theorem popN_eq {α : Type} {n : Nat} {ops a o : List α} (h : popN n ops = some (a, o)) :
    ops = a ++ o ∧ a.length = n := by
  unfold popN at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop n ops).symm, List.length_take_of_le hle⟩
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-! ## One Core step -/

/-- The steps of a setting at frame `F`. -/
abbrev FS (S : Setup H) (F : Frame) := FStep S.P S.host S.fx S.s F

variable (S : Setup H) {K : List (Option ContFX)} {F : Frame}

theorem step_core {cs cs' : List Admin} (O : List FVal) (R : List AdminFX)
    (h : Step S.P (blockFX S.host S.fx) ⟨S.s, F, cs⟩ ⟨S.s, F, cs'⟩) :
    FS S F (K, fvals O ++ cs.map .core ++ R) (K, fvals O ++ cs'.map .core ++ R) :=
  step_seq O R (.core h)

theorem step_nop (O : List FVal) (R : List AdminFX) :
    FS S F (K, fvals O ++ .core (.plain .nop) :: R) (K, fvals O ++ R) := by
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_assoc, List.append_nil] using
    step_core S (K := K) (F := F) (cs := [.plain .nop]) (cs' := []) O R (.parametric .nop)

theorem step_dropVal (O : List FVal) (R : List AdminFX) (v : Val) :
    FS S F (K, fvals (O ++ [.val v]) ++ .core (.plain .drop) :: R) (K, fvals O ++ R) := by
  have h := step_core S (K := K) (F := F) (cs := [v.toAdmin, .plain .drop]) (cs' := []) O R
    (.parametric (.drop v))
  simpa only [fvals_append, fvals_val1, List.append_assoc, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append] using h

theorem step_dropCont (O : List FVal) (R : List AdminFX) (k : Nat) :
    FS S F (K, fvals (O ++ [.cont k]) ++ .core (.plain .drop) :: R) (K, fvals O ++ R) := by
  have h : FS S F (K, fvals O ++ [.contRef k, .core (.plain .drop)] ++ R) (K, fvals O ++ [] ++ R) :=
    step_seq O R (StepFX'.dropCont (s := S.s) (K := K) (f := F) (k := k))
  simpa only [List.append_nil, fvals_append, fvals_cont1, List.append_assoc, List.cons_append,
    List.nil_append] using h

theorem step_prim {n : Nat} {op : List Val → List Val} {i : Instr} (hi : PrimOk S n op i)
    (hF : F.module = S.M) (bs : List (BitVec 32)) (hbs : bs.length = n) (O : List FVal)
    (R : List AdminFX) :
    FS S F (K, fvals O ++ fvals ((bs.map Val.i32).reverse.map .val) ++ .core (.plain i) :: R)
      (K, fvals O ++ fvals ((op (bs.map Val.i32)).reverse.map .val) ++ R) := by
  have h := step_core S (K := K) O R (hi bs F hbs hF)
  simpa only [fvals_vals_map, List.map_append, List.append_assoc, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append] using h

/-! ## Calls -/

/-- One `local.get` of the prologue. -/
theorem step_localGet {ws : List Val} {j : Nat} (hj : j < ws.length) (hlt : j < 2 ^ 32)
    (R : List AdminFX) :
    FS S (Frame.forCall S.M ws [])
      (K, fvals ((ws.take j).map .val) ++ .core (.plain (.localGet (ix j))) :: R)
      (K, fvals ((ws.take (j + 1)).map .val) ++ R) := by
  have hloc : (Frame.forCall S.M ws []).local? (ix j) = some (some ws[j]) := by
    simp only [Frame.local?, Frame.forCall, ix, Idx.toNat, Nat.mod_eq_of_lt hlt,
      List.map_nil, List.append_nil, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some]
  have h := step_core S (K := K) (F := Frame.forCall S.M ws [])
    (cs := [.plain (.localGet (ix j))]) (cs' := [ws[j].toAdmin]) ((ws.take j).map .val) R
    (.variable (.localGet hloc))
  simpa only [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.map_append, fvals_append, fvals_val1, List.append_assoc, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append] using h

/-- The rest of the prologue from parameter `j` on. -/
theorem run_localGets_from {ws : List Val} (hlt : ws.length < 2 ^ 32) (R : List AdminFX) :
    ∀ d j, j + d = ws.length →
      Relation.ReflTransGen (FS S (Frame.forCall S.M ws []))
        (K, fvals ((ws.take j).map .val) ++
          adm ((List.range' j d).map fun i => .core (.localGet (ix i))) ++ R)
        (K, fvals (ws.map .val) ++ R) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hj' : j = ws.length := by omega
    rw [hj']
    simp only [List.take_length, List.range'_zero, List.map_nil, adm, List.append_nil]
    exact .refl
  | succ d ih =>
    intro j hj
    have hstep := step_localGet S (K := K) (j := j) (ws := ws) (by omega) (by omega)
      (adm ((List.range' (j + 1) d).map fun i => .core (.localGet (ix i))) ++ R)
    have hrest := ih (j + 1) (by omega)
    refine Relation.ReflTransGen.head ?_ hrest
    simpa only [List.range'_succ, List.map_cons, adm, InstrFX.toAdmin, List.cons_append,
      List.append_assoc] using hstep

/-- **The prologue** pushes the parameters. -/
theorem run_localGets {ws : List Val} (hlt : ws.length < 2 ^ 32) (R : List AdminFX) :
    Relation.ReflTransGen (FS S (Frame.forCall S.M ws []))
      (K, adm (localGets ws.length) ++ R) (K, fvals (ws.map .val) ++ R) := by
  have h := run_localGets_from S (K := K) hlt R ws.length 0 (Nat.zero_add _)
  simpa only [List.take_zero, List.map_nil, fvals_nil, List.nil_append, localGets,
    List.range_eq_range'] using h

/-- **A call** of an FX function of the setting reaches its body with the parameters pushed. -/
theorem run_call {f a np : Nat} {fi : FuncInst H} {h : H} {Y : List InstrFX} {ws : List Val}
    (hx : S.M.funcs[(S.xf f).toNat]? = some a) (hfi : S.s.funcs[a]? = some fi)
    (hcode : fi.code = .host h) (hfx : S.fx h = some ⟨S.M, np, 1, [], localGets np ++ Y⟩)
    (hnp : np < 2 ^ 32) (hws : ws.length = np) (hF : F.module = S.M) (O : List FVal)
    (R : List AdminFX) :
    Relation.TransGen (FS S F)
      (K, fvals O ++ fvals (ws.map .val) ++ .core (.plain (.call (S.xf f))) :: R)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (fvals (ws.map .val) ++ adm Y)] :: R) := by
  have h₁ : FS S F (K, fvals (O ++ ws.map .val) ++ [.plain (.call (S.xf f))].map .core ++ R)
      (K, fvals (O ++ ws.map .val) ++ [Admin.ref (.func a), .callRefType fi.type].map .core ++ R) :=
    step_core S _ R (.call (by rw [hF]; exact hx) hfi)
  have h₂ : FS S F (K, fvals O ++ (cvals ws ++ [.core (.ref (.func a)),
        .core (.callRefType fi.type)]) ++ R)
      (K, fvals O ++ [.frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] ((localGets np ++ Y).map InstrFX.toAdmin)]] ++ R) :=
    step_seq O R (StepFX'.invoke (c := .callRefType fi.type)
      (show Admin.IsCallRef (.callRefType fi.type) from trivial) hfi hcode hfx hws)
  have h₃ := frun_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F)
    (.seq O (.frame 1 (Frame.forCall S.M ws []) (.label 1 [] .hole)) R)
    (run_localGets S (K := K) (ws := ws) (by omega) (adm Y))
  have hgets : localGets np = localGets ws.length := by rw [hws]
  have e₁ : FS S F (K, fvals O ++ fvals (ws.map .val) ++ .core (.plain (.call (S.xf f))) :: R)
      (K, fvals O ++ fvals (ws.map .val) ++ .core (.ref (.func a)) ::
        .core (.callRefType fi.type) :: R) := by
    simpa only [fvals_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] using h₁
  have e₂ : FS S F (K, fvals O ++ fvals (ws.map .val) ++ .core (.ref (.func a)) ::
        .core (.callRefType fi.type) :: R)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (adm (localGets ws.length) ++ adm Y)] :: R) := by
    simpa only [fvals_vals_map, cvals, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, hgets, adm, List.map_append] using h₂
  have e₃ : Relation.ReflTransGen (FS S F)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (adm (localGets ws.length) ++ adm Y)] :: R)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (fvals (ws.map .val) ++ adm Y)] :: R) := by
    simpa only [CtxV.plug, List.singleton_append, List.append_assoc] using h₃
  exact .head' e₁ (.head e₂ e₃)

/-! ## Continuations, blocks and `if` -/

/-- The fresh continuation of the function at address `a`. -/
def freshK (a : Nat) (fi : FuncInst H) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩

/-- **`ref.func x; cont.new`** stores a fresh continuation. -/
theorem run_contNew {f a : Nat} {fi : FuncInst H} (hx : S.M.funcs[(S.xf f).toNat]? = some a)
    (hfi : S.s.funcs[a]? = some fi) (hF : F.module = S.M) (O : List FVal) (R : List AdminFX) :
    Relation.TransGen (FS S F)
      (K, fvals O ++ .core (.plain (.refFunc (S.xf f))) :: .fx (.contNew S.ct) :: R)
      (K ++ [some (freshK a fi)], fvals (O ++ [.cont K.length]) ++ R) := by
  have h₁ : FS S F (K, fvals O ++ [.plain (.refFunc (S.xf f))].map .core ++ (.fx (.contNew S.ct) :: R))
      (K, fvals O ++ [Admin.ref (.func a)].map .core ++ (.fx (.contNew S.ct) :: R)) :=
    step_core S O _ (.reference (.refFunc (by rw [hF]; exact hx)))
  have h₂ : FS S F (K, fvals O ++ [.core (.ref (.func a)), .fx (.contNew S.ct)] ++ R)
      (K ++ [some (freshK a fi)], fvals O ++ [.contRef K.length] ++ R) :=
    step_seq O R (StepFX'.contNew hfi)
  have e₁ : FS S F (K, fvals O ++ .core (.plain (.refFunc (S.xf f))) :: .fx (.contNew S.ct) :: R)
      (K, fvals O ++ .core (.ref (.func a)) :: .fx (.contNew S.ct) :: R) := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.append_assoc] using h₁
  have e₂ : FS S F (K, fvals O ++ .core (.ref (.func a)) :: .fx (.contNew S.ct) :: R)
      (K ++ [some (freshK a fi)], fvals (O ++ [.cont K.length]) ++ R) := by
    simpa only [fvals_append, fvals_cont1, List.cons_append, List.nil_append,
      List.append_assoc] using h₂
  exact .tail (.single e₁) e₂

/-- Block entry. -/
theorem step_block {bt : BlockType} {body : List InstrFX} {vs : List FVal}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hbt : F.module.blockType? bt = some (t₁, t₂))
    (hvs : vs.length = t₁.length) (O : List FVal) (R : List AdminFX) :
    FS S F (K, fvals O ++ fvals vs ++ .block bt body :: R)
      (K, fvals O ++ .label t₂.length [] (fvals vs ++ adm body) :: R) := by
  have h : FS S F (K, fvals O ++ (fvals vs ++ [.block bt body]) ++ R)
      (K, fvals O ++ [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)] ++ R) :=
    step_seq O R (StepFX'.block hbt hvs)
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, adm]
    using h

/-- `if` on a non-zero `i32`. -/
theorem step_ifTrue {c : BitVec 32} (hc : c ≠ 0) {bt : BlockType} {b₁ b₂ : List InstrFX}
    (O : List FVal) (R : List AdminFX) :
    FS S F (K, fvals (O ++ [.val (Val.i32 c)]) ++ .if_ bt b₁ b₂ :: R)
      (K, fvals O ++ .block bt b₁ :: R) := by
  have h : FS S F (K, fvals O ++ [.core (constI32 c), .if_ bt b₁ b₂] ++ R)
      (K, fvals O ++ [.block bt b₁] ++ R) := step_seq O R (StepFX'.ifTrue hc)
  simpa only [fvals_append, fvals_val1, constI32, List.append_assoc, List.cons_append,
    List.nil_append] using h

/-- `if` on `i32 0`. -/
theorem step_ifFalse {bt : BlockType} {b₁ b₂ : List InstrFX} (O : List FVal) (R : List AdminFX) :
    FS S F (K, fvals (O ++ [.val (Val.i32 0)]) ++ .if_ bt b₁ b₂ :: R)
      (K, fvals O ++ .block bt b₂ :: R) := by
  have h : FS S F (K, fvals O ++ [.core (constI32 0), .if_ bt b₁ b₂] ++ R)
      (K, fvals O ++ [.block bt b₂] ++ R) := step_seq O R StepFX'.ifFalse
  simpa only [fvals_append, fvals_val1, constI32, List.append_assoc, List.cons_append,
    List.nil_append] using h

/-- `resume` without arguments. -/
theorem step_resume {k : Nat} {C : ContFX} {hs : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve S.s F) = some hs') (O : List FVal)
    (R : List AdminFX) :
    FS S F (K, fvals (O ++ [.cont k]) ++ .fx (.resume S.ct hs) :: R)
      (K.set k none, fvals O ++ .handler hs' (C.plug []) :: R) := by
  have h : FS S F (K, fvals O ++ (fvals [] ++ [.contRef k, .fx (.resume S.ct hs)]) ++ R)
      (K.set k none, fvals O ++ [.handler hs' (C.plug (fvals []))] ++ R) :=
    step_seq O R (StepFX'.resume hk hr)
  simpa only [fvals_append, fvals_cont1, fvals_nil, List.append_assoc, List.cons_append,
    List.nil_append, List.singleton_append] using h

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
