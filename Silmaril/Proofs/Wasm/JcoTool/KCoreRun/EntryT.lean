module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry
public import Silmaril.Wasm.JcoTool.KTee.Defs

/-!
# The lift of the generated tee on Core 3.0

`entryT_run`: the Core invocation of the tee's lift (`KTee.entryT`, `[async-lift]name` on the
input's readable end `r`) runs to `YIELD` (`1`): two `stream.new` calls give the outputs `(r₀, w₀)`
and `(r₁, w₁)`, `waitable-set.new` the set `ws`, **one `task.return` of the two values `r₀`, `r₁`**
(`KCoreRun.lans` records any number of `i32`s), the input and both writable ends join `ws`, and
the instance's globals become `liftGT g r w₀ w₁ ws` (`KTee.initMST`'s handles). The instance's
`task.return` must take two values (`RetAt hb cs mi 2`).

The calls with other destination locals than `KCore.entry`'s (`new_runD`, `wsnew_runD`) generalise
`Entry.new_run` and `Entry.wsnew_run`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun.EntryT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile convertP)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Proofs.Wasm.JcoTool.KCoreRun (noHost ix_toNat w_toNat stmt_run args_run inst_of_rel rel_of_inst)
open Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd locals Prog INSR OUTSW WS L64 seqs yield_)
open Silmaril.Wasm.JcoTool.KDrop (DSt)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode callCode biFn)
open Silmaril.Wasm.Component.Streams.Drop (DStore dstep)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)
open Silmaril.Wasm.JcoTool.KTee (entryT W1g)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

/-- The globals after the tee's lift: input `r`, writable ends `w₀`, `w₁`, set `ws`. -/
def liftGT (g : Nat → Nat) (r w₀ w₁ ws : Nat) : Nat → Nat :=
  upd (upd (upd (upd g INSR r) OUTSW w₀) W1g w₁) WS ws

/-- The packed ends of `stream.new`, unpacked into locals `d₁` and `d₂`. -/
theorem unpack_runD {x : HL} {cs : Store H} {F : Frame} (h7 : 7 < F.locals.length) {d₁ d₂ : Nat}
    (h1 : d₁ < 7) (h2 : d₂ < 7) (V : BitVec 64) (rest : List Admin) :
    LSteps Pf hb ma (x, ⟨cs, F, vals [Val.i64 V] ++ (((callCode .streamNew [] [d₁, d₂]).drop 1).map Admin.plain ++ rest)⟩)
      (x, ⟨cs, ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix d₁) (Val.i32 (V.setWidth 32))).setLocal (ix d₂)
        (Val.i32 ((V >>> 32).setWidth 32)), rest⟩) := by
  have h7' : (ix (k := .local) L64).toNat < F.locals.length := by rw [ix_toNat (by decide)]; exact h7
  have hg : ∀ F' : Frame, F'.locals.length = F.locals.length →
      (F'.setLocal (ix L64) (Val.i64 V)).local? (ix L64) = some (some (Val.i64 V)) := fun F' hl => by
    show (F'.locals.set _ _)[_]? = _
    rw [List.getElem?_set_self (by rw [hl]; exact h7')]
  have hl₁ : (F.setLocal (ix L64) (Val.i64 V)).locals.length = F.locals.length := List.length_set ..
  have h1' : (ix (k := .local) d₁).toNat < (F.setLocal (ix L64) (Val.i64 V)).locals.length := by
    rw [hl₁, ix_toNat (by unfold M32; omega)]; omega
  have hg₂ : ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix d₁) (Val.i32 (V.setWidth 32))).local? (ix L64) =
      some (some (Val.i64 V)) := by
    show ((F.locals.set _ _).set _ _)[_]? = _
    rw [List.getElem?_set_ne (by rw [ix_toNat (by unfold M32; omega), ix_toNat (by decide)]; unfold L64; omega),
      List.getElem?_set_self h7']
  have h2' : (ix (k := .local) d₂).toNat <
      ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix d₁) (Val.i32 (V.setWidth 32))).locals.length := by
    show _ < ((F.locals.set _ _).set _ _).length
    rw [List.length_set, List.length_set, ix_toNat (by unfold M32; omega)]; omega
  exact (l_lset h7' _).trans ((l_lget (hg F rfl) _).trans ((l_wrap V _).trans ((l_lset h1' _).trans
    ((l_lget hg₂ _).trans ((l_shr V _).trans ((l_wrap _ _).trans (l_lset h2' _)))))))

/-- **`stream.new`** into the locals `d₁`, `d₂`. -/
theorem new_runD {cs : Store H} {F : Frame} {s : DSt} (t : List Nat) (hR : Rel hb CBL ma cs F s)
    (h7 : 7 < F.locals.length) {d₁ d₂ : Nat} (h1 : d₁ < 7) (h2 : d₂ < 7) {st' : DStore} {r w' : Nat}
    (hnew : dstep s.st .streamNew = some (st', .ends r w')) (hr : r < M32) (hw : w' < M32)
    (rest : List Admin) :
    ∃ F', Rel hb CBL ma cs F' { s with st := st', l := upd (upd s.l d₁ r) d₂ w' } ∧ F'.module = F.module ∧
      F'.locals.length = F.locals.length ∧
      LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, (callCode .streamNew [] [d₁, d₂]).map Admin.plain ++ rest⟩)
        (((st', s.rp), t), ⟨cs, F', rest⟩) := by
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, har⟩ := imp_arity hR .streamNew (by decide)
  have hans : lansAll ma .streamNew ((s.st, s.rp), t) cs [] =
      some (((st', s.rp), t), cs, [Val.i64 (BitVec.ofNat 64 (r + w' * M32))]) := by
    simp only [lansAll, isLift, ↓reduceIte, lans, hnew, hr, hw, and_self, Option.map_some]
  have hcall := lcall (Pf := Pf) hfa hfi hcode hexp (by rw [har]; rfl) hans
    (((callCode .streamNew [] [d₁, d₂]).drop 1).map Admin.plain ++ rest)
  have hun := unpack_runD (Pf := Pf) (hb := hb) (ma := ma) (x := ((st', s.rp), t)) (cs := cs) h7 h1 h2
    (BitVec.ofNat 64 (r + w' * M32)) rest
  rw [(lo_hi hr hw).1, (lo_hi hr hw).2] at hun
  have hR' := rel_set (rel_set (rel_set7 hR (Val.i64 (BitVec.ofNat 64 (r + w' * M32))))
    (i := d₁) (by unfold CBL; omega) hr) (i := d₂) (by unfold CBL; omega) hw
  refine ⟨((F.setLocal (ix L64) (Val.i64 (BitVec.ofNat 64 (r + w' * M32)))).setLocal (ix d₁)
    (Val.i32 (w r))).setLocal (ix d₂) (Val.i32 (w w')), rel_conv hR' rfl rfl rfl, rfl, ?_, hcall.trans hun⟩
  show (((F.locals.set _ _).set _ _).set _ _).length = F.locals.length
  simp only [List.length_set]

/-- **`waitable-set.new`** into the local `d`. -/
theorem wsnew_runD {cs : Store H} {F : Frame} {s : DSt} (t : List Nat) (hR : Rel hb CBL ma cs F s)
    {d : Nat} (hd : d < CBL) {st' : DStore} {n : Nat} (hws : dstep s.st .wsNew = some (st', .nat n))
    (hn : n < M32) (rest : List Admin) :
    ∃ F', Rel hb CBL ma cs F' { s with st := st', l := upd s.l d n } ∧ F'.module = F.module ∧
      LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, (callCode .wsNew [] [d]).map Admin.plain ++ rest⟩)
        (((st', s.rp), t), ⟨cs, F', rest⟩) := by
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, har⟩ := imp_arity hR .wsNew (by decide)
  have hans : lansAll ma .wsNew ((s.st, s.rp), t) cs [] = some (((st', s.rp), t), cs, [Val.i32 (w n)]) := by
    simp only [lansAll, isLift, ↓reduceIte, lans, hws, hn, Option.map_some]
  have hcall := lcall (Pf := Pf) hfa hfi hcode hexp (by rw [har]; rfl) hans
    ([Admin.plain (.localSet (ix d))] ++ rest)
  have h3 : (ix (k := .local) d).toNat < F.locals.length := by
    rw [ix_toNat (by unfold CBL at hd; unfold M32; omega)]
    exact (List.getElem?_eq_some_iff.mp (hR.loc d hd).1).1
  exact ⟨F.setLocal (ix d) (Val.i32 (w n)), rel_conv (rel_set hR (i := d) hd hn) rfl rfl rfl, rfl,
    hcall.trans (l_lset h3 rest)⟩

/-- The code of `KTee.entryT`, statement by statement. -/
def piecesT : List (List Instr) :=
  [callCode .streamNew [] [1, 2], callCode .streamNew [] [3, 4], sCode (.gset INSR (.l 0)),
    sCode (.gset OUTSW (.l 2)), sCode (.gset W1g (.l 4)), callCode .wsNew [] [5], sCode (.gset WS (.l 5)),
    ([E.l 1, E.l 3].map eCode).flatten ++ [Instr.call (ix (biFn .taskReturn))],
    ([E.g INSR, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))],
    ([E.g OUTSW, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))],
    ([E.g W1g, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))], sCode yield_]

/-- The code from piece `k` on, then `U`. -/
def sfx (k : Nat) (U : List Admin) : List Admin :=
  ((piecesT.drop k).map fun p => p.map Admin.plain).foldr (· ++ ·) U

theorem sfx_succ (k : Nat) (U : List Admin) (hk : k < piecesT.length) :
    sfx k U = (piecesT[k]'hk).map Admin.plain ++ sfx (k + 1) U := by
  unfold sfx
  rw [List.drop_eq_getElem_cons hk]
  rfl

theorem entryT_code (U : List Admin) : (sCode entryT).map Admin.plain ++ U = sfx 0 U := by
  simp only [sfx, piecesT, entryT, seqs, sCode, callCode, List.map_append, List.append_assoc, List.drop_zero,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]

theorem retAt_conv {cs cs' : Store H} {mi : ModuleInst} {n : Nat} (h : RetAt hb cs mi n)
    (hf : cs'.funcs = cs.funcs) : RetAt hb cs' mi n := by
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := h
  exact ⟨a, fi, ps, rs, h1, by rw [hf]; exact h2, h3, h4, h5⟩

/-- **The body of the tee's lift**, in its frame. -/
theorem bodyT_run {cs : Store H} {F : Frame} {g m : Nat → Nat}
    {st st₁ st₂ st₃ st₄ st₅ st₆ : DStore} {rp : Option (Nat × Nat)} {t : List Nat}
    {r r₀ w₀ r₁ w₁ ws : Nat} {u₁ u₂ u₃ : Silmaril.Wasm.Component.Async.Res}
    (hR : Rel hb CBL ma cs F ⟨g, m, locals [r], st, rp⟩) (hret : RetAt hb cs F.module 2)
    (h7 : 7 < F.locals.length) (hr : r < M32)
    (hn₀ : dstep st .streamNew = some (st₁, .ends r₀ w₀)) (hr₀ : r₀ < M32) (hw₀ : w₀ < M32)
    (hn₁ : dstep st₁ .streamNew = some (st₂, .ends r₁ w₁)) (hr₁ : r₁ < M32) (hw₁ : w₁ < M32)
    (hws : dstep st₂ .wsNew = some (st₃, .nat ws)) (hws' : ws < M32)
    (hj₁ : dstep st₃ (.join r ws) = some (st₄, u₁)) (hj₂ : dstep st₄ (.join w₀ ws) = some (st₅, u₂))
    (hj₃ : dstep st₅ (.join w₁ ws) = some (st₆, u₃)) (U : List Admin) :
    ∃ cs' F', InstR hb ma cs' F'.module (liftGT g r w₀ w₁ ws) m ∧ F'.module = F.module ∧
      cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), ⟨cs, F, (sCode entryT).map Admin.plain ++ U⟩)
        (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', F', vals [Val.i32 (w 1)] ++ .plain .return_ :: U⟩) := by
  rw [entryT_code]
  -- the two streams
  obtain ⟨F₁, hR₁, hF₁, hL₁, r₁'⟩ := new_runD (Pf := Pf) t hR h7 (d₁ := 1) (d₂ := 2) (by decide) (by decide)
    hn₀ hr₀ hw₀ (sfx 1 U)
  obtain ⟨F₂, hR₂, hF₂, -, r₂'⟩ := new_runD (Pf := Pf) t hR₁ (by rw [hL₁]; exact h7) (d₁ := 3) (d₂ := 4)
    (by decide) (by decide) hn₁ hr₁ hw₁ (sfx 2 U)
  -- the handles into their globals
  obtain ⟨cs₃, F₃, hR₃, hF₃, hf₃, r₃'⟩ := gset_run (Pf := Pf) t hR₂ (i := INSR) (j := 0) (by decide) (by decide)
    (sfx 3 U)
  obtain ⟨cs₄, F₄, hR₄, hF₄, hf₄, r₄'⟩ := gset_run (Pf := Pf) t hR₃ (i := OUTSW) (j := 2) (by decide) (by decide)
    (sfx 4 U)
  obtain ⟨cs₅, F₅, hR₅, hF₅, hf₅, r₅'⟩ := gset_run (Pf := Pf) t hR₄ (i := W1g) (j := 4) (by decide) (by decide)
    (sfx 5 U)
  -- the set
  obtain ⟨F₆, hR₆, hF₆, r₆'⟩ := wsnew_runD (Pf := Pf) t hR₅ (d := 5) (by decide) hws hws' (sfx 6 U)
  obtain ⟨cs₇, F₇, hR₇, hF₇, hf₇, r₇'⟩ := gset_run (Pf := Pf) t hR₆ (i := WS) (j := 5) (by decide) (by decide)
    (sfx 7 U)
  -- `task.return` of both readable ends
  have hret₇ : RetAt hb cs₇ F₇.module 2 := by
    rw [hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁]
    exact retAt_conv hret (by rw [hf₇, hf₅, hf₄, hf₃])
  have hret₇' : ∃ a fi ps rs, F₇.module.funcs[biFn .taskReturn]? = some a ∧ cs₇.funcs[a]? = some fi ∧
      fi.code = .host (hb .taskReturn) ∧ Expand fi.type (.func ps rs) ∧ ps.length = [r₀, r₁].length := hret₇
  have r₈' := lcall_stmt (Pf := Pf) (t := t) (b := .taskReturn) (args := [.l 1, .l 3]) (as := [r₀, r₁]) hR₇
    (by simp only [List.mapM_cons, List.mapM_nil, cev, CBL]; rfl) hret₇'
    (x' := ((st₃, rp), t ++ [r₀, r₁])) (lans_retN _ _ (by simp [hr₀, hr₁])) (sfx 8 U)
  -- the joins
  have hRg : Rel hb CBL ma cs₇ F₇ ⟨liftGT g r w₀ w₁ ws, m,
      upd (upd (upd (upd (upd (locals [r]) 1 r₀) 2 w₀) 3 r₁) 4 w₁) 5 ws, st₃, rp⟩ :=
    rel_conv hR₇ rfl rfl rfl
  have r₉' := lcall_stmt (Pf := Pf) (t := t ++ [r₀, r₁]) (b := .join) (args := [.g INSR, .g WS])
    (as := [r, ws]) hRg (by simp only [List.mapM_cons, List.mapM_nil, cev, NG, INSR, WS]; rfl)
    (imp_arity hRg .join (by decide)) (x' := ((st₄, rp), t ++ [r₀, r₁])) (lans_join hr hws' hj₁) (sfx 9 U)
  have hRg₂ : Rel hb CBL ma cs₇ F₇ ⟨liftGT g r w₀ w₁ ws, m,
      upd (upd (upd (upd (upd (locals [r]) 1 r₀) 2 w₀) 3 r₁) 4 w₁) 5 ws, st₄, rp⟩ :=
    rel_conv hR₇ rfl rfl rfl
  have r₁₀' := lcall_stmt (Pf := Pf) (t := t ++ [r₀, r₁]) (b := .join) (args := [.g OUTSW, .g WS])
    (as := [w₀, ws]) hRg₂ (by simp only [List.mapM_cons, List.mapM_nil, cev, NG, OUTSW, WS]; rfl)
    (imp_arity hRg₂ .join (by decide)) (x' := ((st₅, rp), t ++ [r₀, r₁])) (lans_join hw₀ hws' hj₂) (sfx 10 U)
  have hRg₃ : Rel hb CBL ma cs₇ F₇ ⟨liftGT g r w₀ w₁ ws, m,
      upd (upd (upd (upd (upd (locals [r]) 1 r₀) 2 w₀) 3 r₁) 4 w₁) 5 ws, st₅, rp⟩ :=
    rel_conv hR₇ rfl rfl rfl
  have r₁₁' := lcall_stmt (Pf := Pf) (t := t ++ [r₀, r₁]) (b := .join) (args := [.g W1g, .g WS])
    (as := [w₁, ws]) hRg₃ (by simp only [List.mapM_cons, List.mapM_nil, cev, NG, W1g, WS]; rfl)
    (imp_arity hRg₃ .join (by decide)) (x' := ((st₆, rp), t ++ [r₀, r₁])) (lans_join hw₁ hws' hj₃) (sfx 11 U)
  refine ⟨cs₇, F₇, inst_of_rel hRg, by rw [hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁], by rw [hf₇, hf₅, hf₄, hf₃], ?_⟩
  have hy : sfx 11 U = vals [Val.i32 (w 1)] ++ .plain .return_ :: U := rfl
  rw [sfx_succ 0 U (by decide), sfx_succ 1 U (by decide), sfx_succ 2 U (by decide), sfx_succ 3 U (by decide),
    sfx_succ 4 U (by decide), sfx_succ 5 U (by decide), sfx_succ 6 U (by decide), sfx_succ 7 U (by decide),
    sfx_succ 8 U (by decide), sfx_succ 9 U (by decide), sfx_succ 10 U (by decide)]
  rw [hy] at r₁₁'
  exact r₁'.trans (r₂'.trans (r₃'.trans (r₄'.trans (r₅'.trans (r₆'.trans (r₇'.trans (r₈'.trans
    (r₉'.trans (r₁₀'.trans r₁₁')))))))))

/-- **The Core invocation of the tee's lift** on the input's readable end `r` runs to `YIELD`:
two output streams, the set, `task.return` of both readable ends, three joins; the globals become
`liftGT g r w₀ w₁ ws`. -/
theorem entryT_run (Pf : Profile) {cs : Store H} {mi : ModuleInst} {P : Prog} {a : Nat}
    {g m : Nat → Nat} {st st₁ st₂ st₃ st₄ st₅ st₆ : DStore} {rp : Option (Nat × Nat)} {t : List Nat}
    {r r₀ w₀ r₁ w₁ ws : Nat} {u₁ u₂ u₃ : Silmaril.Wasm.Component.Async.Res} (hP : P.entry = entryT)
    (hI : InstR hb ma cs mi g m) (hret : RetAt hb cs mi 2) (hen : EntryAt cs mi P a) (hr : r < M32)
    (hn₀ : dstep st .streamNew = some (st₁, .ends r₀ w₀)) (hr₀ : r₀ < M32) (hw₀ : w₀ < M32)
    (hn₁ : dstep st₁ .streamNew = some (st₂, .ends r₁ w₁)) (hr₁ : r₁ < M32) (hw₁ : w₁ < M32)
    (hws : dstep st₂ .wsNew = some (st₃, .nat ws)) (hws' : ws < M32)
    (hj₁ : dstep st₃ (.join r ws) = some (st₄, u₁)) (hj₂ : dstep st₄ (.join w₀ ws) = some (st₅, u₂))
    (hj₃ : dstep st₅ (.join w₁ ws) = some (st₆, u₃)) :
    ∃ cs', InstR hb ma cs' mi (liftGT g r w₀ w₁ ws) m ∧ cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
        (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) := by
  obtain ⟨fi, ty, ps, rs, hf, hfm, hcode, hexp, hps, hrs⟩ := hen
  let F₀ : Frame := Frame.forCall fi.module [Val.i32 (w r)] entryLocals
  have hI₀ : InstR hb ma cs F₀.module g m := by rw [show F₀.module = mi from hfm]; exact hI
  have hR₀ : Rel hb CBL ma cs F₀ ⟨g, m, locals [r], st, rp⟩ := rel_of_inst hI₀ (entry_locals _ hr)
  have h7 : 7 < F₀.locals.length := by simp [F₀, Frame.forCall, entryLocals]
  have hret₀ : RetAt hb cs F₀.module 2 := by rw [show F₀.module = mi from hfm]; exact hret
  obtain ⟨cs', F', hI', hF', hfs, rb⟩ := bodyT_run (Pf := Pf) (t := t) hR₀ hret₀ h7 hr hn₀ hr₀ hw₀ hn₁ hr₁ hw₁
    hws hws' hj₁ hj₂ hj₃ [.plain .unreachable]
  refine ⟨cs', by rw [hF', show F₀.module = mi from hfm] at hI'; exact hI', hfs, ?_⟩
  have hinv : invoke cs a [Val.i32 (w r)] =
      ⟨cs, {}, vals [Val.i32 (w r)] ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hf]
  have q₀ : LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
      (((st, rp), t), ⟨cs, {}, [.frame 1 F₀ [.label 1 [] ((sCode entryT).map Admin.plain ++
        [.plain .unreachable])]]⟩) := by
    rw [hinv]
    have hstep := Step.callRefFunc (P := Pf) (host := noHost) (s := cs) (f := {}) (c := .callRefType fi.type)
      (vs := [Val.i32 (w r)]) trivial hf hexp (by simp [hps]) hcode
    rw [hrs, hP] at hstep
    simpa [expression, F₀] using (Relation.ReflTransGen.single (LStep.core (hb := hb) (ma := ma)
      (x := ((st, rp), t)) hstep))
  have q₁ := lsteps_frame {} 1 (lsteps_label 1 [] rb)
  have q₂ : LSteps Pf hb ma (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, [.frame 1 F' [.label 1 []
        (vals [Val.i32 (w 1)] ++ .plain .return_ :: [.plain .unreachable])]]⟩)
      (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, [.frame 1 F' (vals [Val.i32 (w 1)] ++ [.plain .return_])]⟩) := by
    have hstep := Step.returnLabel (P := Pf) (host := noHost) (s := cs') (f := F') (n := 1) (cont := [])
      (vs := [Val.i32 (w 1)]) (rest := [.plain .unreachable])
    exact lsteps_frame {} 1 (.single (.core (by simpa [vals] using hstep)))
  have q₃ : LSteps Pf hb ma (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, [.frame 1 F' (vals [Val.i32 (w 1)] ++
        [.plain .return_])]⟩) (((st₆, rp), t ++ [r₀, r₁]), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) := by
    have hstep := Step.returnFrame (P := Pf) (host := noHost) (s := cs') (f := {}) (fi := F') (n := 1)
      (vs' := []) (vs := [Val.i32 (w 1)]) (rest := []) rfl
    exact .single (.core (by simpa [vals] using hstep))
  exact q₀.trans (q₁.trans (q₂.trans q₃))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun.EntryT
