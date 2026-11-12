module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Invoke

/-!
# The lift on Core 3.0, with the `Async` built-ins as host functions

`LStep` (`KCoreRun.Defs`) is `HStep` with every built-in a host function: the runtime's
(`stream.read`, `stream.write`, the drops: `bans`) and the lift's (`stream.new`,
`waitable-set.new`, `waitable.join`, `task.return`: `lans`). Here:

* `hstep_l`, `hsteps_l`: every `HStep` run is an `LStep` run (the task's results unchanged), so
  every result about `HStep` (`stmt_run`, `invoke_run`, `rstep_core`) holds for `LStep`;
  `lstep_core`: each `LStep` is a Core 3.0 `Step` against the stateless host of its transition.
* `lcall`: the Core `call` of an imported built-in, then its host answer.
* `new_run`, `wsnew_run`, `lcall_stmt`: the three shapes of the lift's calls, keeping `Rel`.
* `entry_run`: **the Core invocation of the lift of `KCore.entry`** (`[async-lift]name` on the
  input's readable end `r`) runs to `YIELD` (`1`): `stream.new` gives the output stream `(r', w')`,
  `waitable-set.new` the set `ws`, `task.return` returns `r'`, both ends join `ws`, and the
  instance's globals become `liftG g r w' ws` (`KDrop.initMSD`'s handles).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile convertP)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Proofs.Wasm.JcoTool.KCoreRun (noHost ix_toNat w_toNat stmt_run args_run inst_of_rel rel_of_inst)
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd locals Prog INSR OUTSW WS L64 entry seqs yield_)
open Silmaril.Wasm.JcoTool.KDrop (DSt)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode callCode biFn)
open Silmaril.Wasm.Component.Streams.Drop (DStore dstep)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

/-! ## `HStep` runs are `LStep` runs; `LStep` is Core's `Step` -/

theorem i32s_map : ∀ args : List W, i32s? (args.map Val.i32) = some args
  | [] => rfl
  | a :: as => by simp only [List.map_cons, Val.i32, i32s?, i32s_map as, Option.map_some]

theorem bans_notLift {b : BI} {q : HQ} {s : Store H} {args : List W} {r : HQ × Store H × List W}
    (h : bans ma b q s args = some r) : isLift b = false := by
  cases b <;> first | rfl | (exfalso; simp [bans, bi] at h)

theorem lansAll_bans {b : BI} {q q' : HQ} {s s' : Store H} {args res : List W}
    (h : bans ma b q s args = some (q', s', res)) (t : List Nat) :
    lansAll ma b (q, t) s (args.map Val.i32) = some ((q', t), s', res.map Val.i32) := by
  simp only [lansAll, bans_notLift h, Bool.false_eq_true, ↓reduceIte, i32s_map, h,
    Option.bind_eq_bind, Option.bind_some]
  rfl

theorem hstep_l {x y : HQ × Config H} (h : HStep Pf hb ma x y) (t : List Nat) :
    LStep Pf hb ma ((x.1, t), x.2) ((y.1, t), y.2) := by
  induction h with
  | core h => exact .core h
  | host hc hf he hn hcode hans =>
    exact .host hc hf he (by rw [List.length_map]; exact hn) hcode (lansAll_bans hans t)
  | instrs _ hne ih => exact .instrs ih hne
  | label _ ih => exact .label ih
  | frame _ ih => exact .frame ih

/-- **Every `HStep` run is an `LStep` run.** -/
theorem hsteps_l {x y : HQ × Config H} (h : HSteps Pf hb ma x y) (t : List Nat) :
    LSteps Pf hb ma ((x.1, t), x.2) ((y.1, t), y.2) :=
  Relation.ReflTransGen.lift (fun z : HQ × Config H => ((z.1, t), z.2)) (fun _ _ h => hstep_l h t) _ _ h

/-- **An `LStep` is a Core 3.0 `Step`** against the stateless host of its transition. -/
theorem lstep_core {x y : HL × Config H} (h : LStep Pf hb ma x y) :
    Step Pf (hostAtL hb ma x.1 y.1) x.2 y.2 := by
  induction h with
  | core h => exact Step.of_noHost _ h
  | @host x x' s s' f c vs res a fi ps rs b hc hf he hn hcode hans =>
    exact .callRefHost (r := .values res) hc hf he hn hcode ⟨b, s', res, rfl, hans, rfl⟩
  | instrs _ hne ih => exact .ctxtInstrs ih hne
  | label _ ih => exact .ctxtLabel ih
  | frame _ ih => exact .ctxtFrame ih

/-! ## Contexts -/

theorem lstep_ctx {x x' : HL} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (vs : List Val)
    (rest : List Admin) (h : LStep Pf hb ma (x, ⟨s, f, X⟩) (x', ⟨s', f', Y⟩)) :
    LStep Pf hb ma (x, ⟨s, f, vals vs ++ X ++ rest⟩) (x', ⟨s', f', vals vs ++ Y ++ rest⟩) := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv
    simpa only [vals, List.map_nil, List.nil_append, List.append_nil] using h
  · have hne : vs ≠ [] ∨ rest ≠ [] := by
      by_cases h1 : vs = []
      · exact .inr fun h2 => hv ⟨h1, h2⟩
      · exact .inl h1
    exact .instrs h hne

theorem lsteps_app {x x' : HL} {s s' : Store H} {f f' : Frame} {X Y : List Admin}
    (rest : List Admin) (h : LSteps Pf hb ma (x, ⟨s, f, X⟩) (x', ⟨s', f', Y⟩)) :
    LSteps Pf hb ma (x, ⟨s, f, X ++ rest⟩) (x', ⟨s', f', Y ++ rest⟩) := by
  refine Relation.ReflTransGen.lift (p := LStep Pf hb ma)
    (fun z : HL × Config H => ((z.1, ⟨z.2.store, z.2.frame, z.2.code ++ rest⟩) : HL × Config H))
    (fun a b hab => ?_) _ _ h
  rcases a with ⟨xa, sa, fa, ia⟩
  rcases b with ⟨xb, sb, fb, ib⟩
  simpa only [vals, List.map_nil, List.nil_append] using lstep_ctx [] rest hab

theorem lsteps_label {x x' : HL} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (n : Nat)
    (cont : List Instr) (h : LSteps Pf hb ma (x, ⟨s, f, X⟩) (x', ⟨s', f', Y⟩)) :
    LSteps Pf hb ma (x, ⟨s, f, [.label n cont X]⟩) (x', ⟨s', f', [.label n cont Y]⟩) := by
  refine Relation.ReflTransGen.lift (p := LStep Pf hb ma)
    (fun z : HL × Config H => ((z.1, ⟨z.2.store, z.2.frame, [.label n cont z.2.code]⟩) : HL × Config H))
    (fun a b hab => ?_) _ _ h
  rcases a with ⟨xa, sa, fa, ia⟩
  rcases b with ⟨xb, sb, fb, ib⟩
  exact .label hab

theorem lsteps_frame {x x' : HL} {s s' : Store H} {fi fi' : Frame} {X Y : List Admin} (f : Frame)
    (n : Nat) (h : LSteps Pf hb ma (x, ⟨s, fi, X⟩) (x', ⟨s', fi', Y⟩)) :
    LSteps Pf hb ma (x, ⟨s, f, [.frame n fi X]⟩) (x', ⟨s', f, [.frame n fi' Y]⟩) := by
  refine Relation.ReflTransGen.lift (p := LStep Pf hb ma)
    (fun z : HL × Config H => ((z.1, ⟨z.2.store, f, [.frame n z.2.frame z.2.code]⟩) : HL × Config H))
    (fun a b hab => ?_) _ _ h
  rcases a with ⟨xa, sa, fa, ia⟩
  rcases b with ⟨xb, sb, fb, ib⟩
  exact .frame hab

/-- A host-free Core step at the front of the code. -/
theorem lfront {x : HL} {s s' : Store H} {f f' : Frame} {X Y : List Admin} (rest : List Admin)
    (h : Step Pf noHost ⟨s, f, X⟩ ⟨s', f', Y⟩) :
    LSteps Pf hb ma (x, ⟨s, f, X ++ rest⟩) (x, ⟨s', f', Y ++ rest⟩) :=
  lsteps_app rest (.single (.core h))

/-! ## Single instructions -/

theorem l_lset {x : HL} {s : Store H} {f : Frame} {i : LocalIdx} {v : Val} (hi : i.toNat < f.locals.length)
    (R : List Admin) :
    LSteps Pf hb ma (x, ⟨s, f, v.toAdmin :: .plain (.localSet i) :: R⟩) (x, ⟨s, f.setLocal i v, R⟩) :=
  lfront (X := [v.toAdmin, .plain (.localSet i)]) (Y := []) R (.variable (.localSet hi))

theorem l_lget {x : HL} {s : Store H} {f : Frame} {i : LocalIdx} {v : Val}
    (hi : f.local? i = some (some v)) (R : List Admin) :
    LSteps Pf hb ma (x, ⟨s, f, .plain (.localGet i) :: R⟩) (x, ⟨s, f, v.toAdmin :: R⟩) :=
  lfront (X := [.plain (.localGet i)]) (Y := [v.toAdmin]) R (.variable (.localGet hi))

theorem convert_wrap (Pf : Profile) (v : BitVec 64) : convertP Pf .wrap v (.ok (v.setWidth 32)) := by
  unfold convertP
  split <;> rfl

theorem l_wrap {x : HL} {s : Store H} {f : Frame} (v : BitVec 64) (R : List Admin) :
    LSteps Pf hb ma (x, ⟨s, f, (Val.i64 v).toAdmin :: .plain (.convert .wrap) :: R⟩)
      (x, ⟨s, f, (Val.i32 (v.setWidth 32)).toAdmin :: R⟩) :=
  lfront (X := [(Val.i64 v).toAdmin, .plain (.convert .wrap)]) (Y := [(Val.i32 (v.setWidth 32)).toAdmin]) R
    (.numeric (.convert (op := .wrap) (convert_wrap Pf v)))

theorem l_shr {x : HL} {s : Store H} {f : Frame} (v : BitVec 64) (R : List Admin) :
    LSteps Pf hb ma (x, ⟨s, f, (Val.i64 v).toAdmin :: .plain (.intConst .i64 (BitVec.ofNat 64 32)) ::
        .plain (.intBinOp .i64 (.shr .unsigned)) :: R⟩)
      (x, ⟨s, f, (Val.i64 (v >>> 32)).toAdmin :: R⟩) :=
  lfront (X := [(Val.i64 v).toAdmin, .plain (.intConst .i64 (BitVec.ofNat 64 32)),
      .plain (.intBinOp .i64 (.shr .unsigned))]) (Y := [(Val.i64 (v >>> 32)).toAdmin]) R
    (.numeric (.intBinOp rfl))

/-- **The call of an imported built-in**: Core's `call`, then the host's answer `lansAll`. -/
theorem lcall {x x' : HL} {cs cs' : Store H} {F : Frame} {b : BI} {vs res : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} (hfa : F.module.funcs[biFn b]? = some a)
    (hfi : cs.funcs[a]? = some fi) (hcode : fi.code = .host (hb b)) (hexp : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hans : lansAll ma b x cs vs = some (x', cs', res)) (rest : List Admin) :
    LSteps Pf hb ma (x, ⟨cs, F, vals vs ++ Admin.plain (Instr.call (ix (biFn b))) :: rest⟩)
      (x', ⟨cs', F, vals res ++ rest⟩) := by
  have hx : F.module.funcs[(ix (biFn b) : FuncIdx).toNat]? = some a := by
    have hb32 : biFn b < M32 := by cases b <;> decide
    rw [ix_toNat hb32]; exact hfa
  have r₁ : LSteps Pf hb ma (x, ⟨cs, F, vals vs ++ [Admin.plain (Instr.call (ix (biFn b)))] ++ rest⟩)
      (x, ⟨cs, F, vals vs ++ [.ref (.func a), .callRefType fi.type] ++ rest⟩) :=
    .single (lstep_ctx vs rest (.core (.call hx hfi)))
  have r₂ : LStep Pf hb ma (x, ⟨cs, F, vals [] ++ (vals vs ++ [.ref (.func a), .callRefType fi.type]) ++ rest⟩)
      (x', ⟨cs', F, vals [] ++ vals res ++ rest⟩) :=
    lstep_ctx [] rest (.host trivial hfi hexp hn hcode hans)
  have e₁ : vals vs ++ Admin.plain (Instr.call (ix (biFn b))) :: rest = vals vs ++ [Admin.plain (Instr.call (ix (biFn b)))] ++ rest := by
    simp only [List.append_assoc, List.singleton_append]
  have e₂ : vals [] ++ (vals vs ++ [.ref (.func a), .callRefType fi.type]) ++ rest =
      vals vs ++ [.ref (.func a), .callRefType fi.type] ++ rest := by
    simp only [vals, List.map_nil, List.nil_append]
  have e₃ : vals [] ++ vals res ++ rest = vals res ++ rest := by simp only [vals, List.map_nil, List.nil_append]
  rw [e₁]
  rw [e₂, e₃] at r₂
  exact r₁.trans (.single r₂)

/-! ## The locals of the lift -/

theorem upd_self {f : Nat → Nat} {k v : Nat} : upd f k v k = v := ite_eq_left rfl
theorem upd_other {f : Nat → Nat} {k v j : Nat} (h : j ≠ k) : upd f k v j = f j := ite_eq_right h

theorem rel_set {cs : Store H} {F : Frame} {s : DSt} (hR : Rel hb CBL ma cs F s) {i v : Nat}
    (hi : i < CBL) (hv : v < M32) :
    Rel hb CBL ma cs (F.setLocal (ix i) (Val.i32 (w v))) { s with l := upd s.l i v } := by
  have hlen : i < F.locals.length := by
    have h := (hR.loc i hi).1
    exact (List.getElem?_eq_some_iff.mp h).1
  have hix : (ix (k := .local) i).toNat = i := ix_toNat (by unfold CBL at hi; unfold M32; omega)
  have hI : InstR hb ma cs F.module s.g s.m := inst_of_rel hR
  refine rel_of_inst hI fun j hj => ?_
  show (F.locals.set (ix (k := .local) i).toNat (some (Val.i32 (w v))))[j]? =
      some (some (Val.i32 (w (upd s.l i v j)))) ∧ upd s.l i v j < M32
  rw [hix]
  by_cases hji : j = i
  · rw [hji, List.getElem?_set_self hlen, upd_self]
    exact ⟨rfl, hv⟩
  · rw [List.getElem?_set_ne (Ne.symm hji), upd_other hji]
    exact hR.loc j hj

theorem rel_set7 {cs : Store H} {F : Frame} {s : DSt} (hR : Rel hb CBL ma cs F s) (v : Val) :
    Rel hb CBL ma cs (F.setLocal (ix L64) v) s := by
  have hI : InstR hb ma cs F.module s.g s.m := inst_of_rel hR
  refine rel_of_inst hI fun j hj => ?_
  show (F.locals.set (ix (k := .local) L64).toNat (some v))[j]? = some (some (Val.i32 (w (s.l j)))) ∧
    s.l j < M32
  rw [ix_toNat (by decide), List.getElem?_set_ne (by unfold L64; unfold CBL at hj; omega)]
  exact hR.loc j hj

theorem rel_conv {nl : Nat} {cs : Store H} {F : Frame} {s s' : DSt} (h : Rel hb nl ma cs F s)
    (hg : s'.g = s.g) (hm : s'.m = s.m) (hl : s'.l = s.l) : Rel hb nl ma cs F s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [← hg] at h3 h4
  rw [← hm] at h5
  rw [← hl] at h2
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem lo_hi {r w' : Nat} (hr : r < M32) (hw : w' < M32) :
    (BitVec.ofNat 64 (r + w' * M32)).setWidth 32 = w r ∧
      ((BitVec.ofNat 64 (r + w' * M32)) >>> 32).setWidth 32 = w w' := by
  have hr' : r < 4294967296 := hr
  have hw' : w' < 4294967296 := hw
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [w, M32, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow] <;> omega

/-! ## The lift's calls -/

/-- The packed ends of `stream.new`, unpacked into locals `1` and `2` through the `i64` local. -/
theorem unpack_run {x : HL} {cs : Store H} {F : Frame} (h7 : 7 < F.locals.length) (V : BitVec 64)
    (rest : List Admin) :
    LSteps Pf hb ma (x, ⟨cs, F, vals [Val.i64 V] ++ (((callCode .streamNew [] [1, 2]).drop 1).map Admin.plain ++ rest)⟩)
      (x, ⟨cs, ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix 1) (Val.i32 (V.setWidth 32))).setLocal (ix 2)
        (Val.i32 ((V >>> 32).setWidth 32)), rest⟩) := by
  have h7' : (ix (k := .local) L64).toNat < F.locals.length := by rw [ix_toNat (by decide)]; exact h7
  have hg : ∀ F' : Frame, F'.locals.length = F.locals.length →
      (F'.setLocal (ix L64) (Val.i64 V)).local? (ix L64) = some (some (Val.i64 V)) := fun F' hl => by
    show (F'.locals.set _ _)[_]? = _
    rw [List.getElem?_set_self (by rw [hl]; exact h7')]
  have hl₁ : (F.setLocal (ix L64) (Val.i64 V)).locals.length = F.locals.length := List.length_set ..
  have h1 : (ix (k := .local) 1).toNat < (F.setLocal (ix L64) (Val.i64 V)).locals.length := by
    rw [hl₁, ix_toNat (by decide)]; omega
  have hg₂ : ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix 1) (Val.i32 (V.setWidth 32))).local? (ix L64) =
      some (some (Val.i64 V)) := by
    show ((F.locals.set _ _).set _ _)[_]? = _
    rw [List.getElem?_set_ne (by rw [ix_toNat (by decide), ix_toNat (by decide)]; decide),
      List.getElem?_set_self h7']
  have h2 : (ix (k := .local) 2).toNat <
      ((F.setLocal (ix L64) (Val.i64 V)).setLocal (ix 1) (Val.i32 (V.setWidth 32))).locals.length := by
    show _ < ((F.locals.set _ _).set _ _).length
    rw [List.length_set, List.length_set, ix_toNat (by decide)]; omega
  exact (l_lset h7' _).trans ((l_lget (hg F rfl) _).trans ((l_wrap V _).trans ((l_lset h1 _).trans
    ((l_lget hg₂ _).trans ((l_shr V _).trans ((l_wrap _ _).trans (l_lset h2 _)))))))

/-- **`stream.new`**: the call, then the unpacking of the two ends into locals `1` and `2`. -/
theorem new_run {cs : Store H} {F : Frame} {s : DSt} (t : List Nat) (hR : Rel hb CBL ma cs F s)
    (h7 : 7 < F.locals.length) {st' : DStore} {r w' : Nat}
    (hnew : dstep s.st .streamNew = some (st', .ends r w')) (hr : r < M32) (hw : w' < M32)
    (rest : List Admin) :
    ∃ F', Rel hb CBL ma cs F' { s with st := st', l := upd (upd s.l 1 r) 2 w' } ∧ F'.module = F.module ∧
      LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, (callCode .streamNew [] [1, 2]).map Admin.plain ++ rest⟩)
        (((st', s.rp), t), ⟨cs, F', rest⟩) := by
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, har⟩ := hR.imp .streamNew
  have hans : lansAll ma .streamNew ((s.st, s.rp), t) cs [] =
      some (((st', s.rp), t), cs, [Val.i64 (BitVec.ofNat 64 (r + w' * M32))]) := by
    simp only [lansAll, isLift, ↓reduceIte, lans, hnew, hr, hw, and_self, Option.map_some]
  have hcall := lcall (Pf := Pf) hfa hfi hcode hexp (by rw [har (by decide)]; rfl) hans
    (((callCode .streamNew [] [1, 2]).drop 1).map Admin.plain ++ rest)
  have hun := unpack_run (Pf := Pf) (hb := hb) (ma := ma) (x := ((st', s.rp), t)) (cs := cs) h7
    (BitVec.ofNat 64 (r + w' * M32)) rest
  rw [(lo_hi hr hw).1, (lo_hi hr hw).2] at hun
  have hR' := rel_set (rel_set (rel_set7 hR (Val.i64 (BitVec.ofNat 64 (r + w' * M32))))
    (i := 1) (by decide) hr) (i := 2) (by decide) hw
  exact ⟨((F.setLocal (ix L64) (Val.i64 (BitVec.ofNat 64 (r + w' * M32)))).setLocal (ix 1)
    (Val.i32 (w r))).setLocal (ix 2) (Val.i32 (w w')), rel_conv hR' rfl rfl rfl, rfl, hcall.trans hun⟩

/-- **`waitable-set.new`**: the call, the set into local `3`. -/
theorem wsnew_run {cs : Store H} {F : Frame} {s : DSt} (t : List Nat) (hR : Rel hb CBL ma cs F s)
    {st' : DStore} {n : Nat} (hws : dstep s.st .wsNew = some (st', .nat n)) (hn : n < M32)
    (rest : List Admin) :
    ∃ F', Rel hb CBL ma cs F' { s with st := st', l := upd s.l 3 n } ∧ F'.module = F.module ∧
      LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, (callCode .wsNew [] [3]).map Admin.plain ++ rest⟩)
        (((st', s.rp), t), ⟨cs, F', rest⟩) := by
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, har⟩ := hR.imp .wsNew
  have hans : lansAll ma .wsNew ((s.st, s.rp), t) cs [] = some (((st', s.rp), t), cs, [Val.i32 (w n)]) := by
    simp only [lansAll, isLift, ↓reduceIte, lans, hws, hn, Option.map_some]
  have hcall := lcall (Pf := Pf) hfa hfi hcode hexp (by rw [har (by decide)]; rfl) hans
    ([Admin.plain (.localSet (ix 3))] ++ rest)
  have h3 : (ix (k := .local) 3).toNat < F.locals.length := by
    rw [ix_toNat (by decide)]
    exact (List.getElem?_eq_some_iff.mp (hR.loc 3 (by decide)).1).1
  exact ⟨F.setLocal (ix 3) (Val.i32 (w n)), rel_conv (rel_set hR (i := 3) (by decide) hn) rfl rfl rfl, rfl,
    hcall.trans (l_lset h3 rest)⟩

/-- The import of a built-in other than `task.return`, with its arity. -/
theorem imp_arity {cs : Store H} {F : Frame} {s : DSt} {nl : Nat} (hR : Rel hb nl ma cs F s) (b : BI)
    (hb' : b ≠ .taskReturn) :
    ∃ a fi ps rs, F.module.funcs[biFn b]? = some a ∧ cs.funcs[a]? = some fi ∧
      fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ ps.length = arity b := by
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hR.imp b
  exact ⟨a, fi, ps, rs, h1, h2, h3, h4, h5 hb'⟩

/-- **A call of a lift built-in with no results** (`task.return`, `waitable.join`): its arguments,
then the call. -/
theorem lcall_stmt {cs : Store H} {F : Frame} {s : DSt} {t : List Nat} {x' : HL} {b : BI} {args : List E}
    {as : List Nat} (hR : Rel hb CBL ma cs F s) (hm : args.mapM (cev CBL s) = some as)
    (himp : ∃ a fi ps rs, F.module.funcs[biFn b]? = some a ∧ cs.funcs[a]? = some fi ∧
      fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ ps.length = as.length)
    (hans : lansAll ma b ((s.st, s.rp), t) cs ((as.map w).map Val.i32) = some (x', cs, []))
    (rest : List Admin) :
    LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, ((args.map eCode).flatten ++ [Instr.call (ix (biFn b))]).map
        Admin.plain ++ rest⟩) (x', ⟨cs, F, rest⟩) := by
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, hps⟩ := himp
  obtain ⟨-, hrun⟩ := args_run (Pf := Pf) (q := (s.st, s.rp)) hR args hm
  have r₁ := hsteps_l (hrun [] (Admin.plain (Instr.call (ix (biFn b))) :: rest)) t
  have e₁ : stackA ([] : List W) ++ ((args.map eCode).flatten.map Admin.plain ++
      Admin.plain (Instr.call (ix (biFn b))) :: rest) =
      ((args.map eCode).flatten ++ [Instr.call (ix (biFn b))]).map Admin.plain ++ rest := by
    simp [stackA, vals]
  have e₂ : stackA ((as.map w).reverse ++ []) ++ Admin.plain (Instr.call (ix (biFn b))) :: rest =
      vals ((as.map w).map Val.i32) ++ Admin.plain (Instr.call (ix (biFn b))) :: rest := by
    simp [stackA]
  have hn : ((as.map w).map Val.i32).length = ps.length := by simp [hps]
  rw [e₁, e₂] at r₁
  simpa only [vals, List.map_nil, List.nil_append] using r₁.trans (lcall hfa hfi hcode hexp hn hans rest)

/-- **`global.set i (local.get j)`** (`stmt_run`). -/
theorem gset_run {cs : Store H} {F : Frame} {s : DSt} (t : List Nat) (hR : Rel hb CBL ma cs F s)
    {i j : Nat} (hi : i < NG) (hj : j < CBL) (rest : List Admin) :
    ∃ cs' F', Rel hb CBL ma cs' F' { s with g := upd s.g i (s.l j) } ∧ F'.module = F.module ∧
      cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((s.st, s.rp), t), ⟨cs, F, (sCode (.gset i (.l j))).map Admin.plain ++ rest⟩)
        (((s.st, s.rp), t), ⟨cs', F', rest⟩) := by
  have hx : bexec CBL (.gset i (.l j)) 0 s = some (.norm, { s with g := upd s.g i (s.l j) }) := by
    simp only [bexec, hi, ↓reduceIte, cev, hj, Option.map_some]
  obtain ⟨-, -, hres⟩ := stmt_run (Pf := Pf) (.gset i (.l j)) 0 hx hR
  obtain ⟨cs', F', junk, hR', hF, hfs, hj', r⟩ := hres rest
  rw [hj' rfl] at r
  exact ⟨cs', F', hR', hF, hfs, by simpa [outCode] using hsteps_l r t⟩

/-! ## The lift -/

/-- The code of `KCore.entry`, call by call. -/
theorem entry_code : sCode entry =
    callCode .streamNew [] [1, 2] ++ sCode (.gset INSR (.l 0)) ++ sCode (.gset OUTSW (.l 2)) ++
      callCode .wsNew [] [3] ++ sCode (.gset WS (.l 3)) ++
      ((([E.l 1].map eCode).flatten ++ [Instr.call (ix (biFn .taskReturn))]) ++
      ((([E.g INSR, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]) ++
      ((([E.g OUTSW, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]) ++ sCode yield_))) := by
  simp only [entry, seqs, sCode, callCode, List.append_assoc]

/-- The lift's first part: `stream.new`, then the input and output handles into their globals. -/
theorem lift_a {cs : Store H} {F : Frame} {g m : Nat → Nat} {st st₁ : DStore} {rp : Option (Nat × Nat)}
    {t : List Nat} {r r' w' : Nat} (hR : Rel hb CBL ma cs F ⟨g, m, locals [r], st, rp⟩)
    (h7 : 7 < F.locals.length) (hnew : dstep st .streamNew = some (st₁, .ends r' w')) (hr' : r' < M32)
    (hw' : w' < M32) (rest : List Admin) :
    ∃ cs' F', Rel hb CBL ma cs' F' ⟨upd (upd g INSR r) OUTSW w', m, upd (upd (locals [r]) 1 r') 2 w', st₁, rp⟩ ∧
      F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), ⟨cs, F, (callCode .streamNew [] [1, 2] ++ sCode (.gset INSR (.l 0)) ++
          sCode (.gset OUTSW (.l 2))).map Admin.plain ++ rest⟩) (((st₁, rp), t), ⟨cs', F', rest⟩) := by
  obtain ⟨F₁, hR₁, hF₁, r₁⟩ := new_run (Pf := Pf) t hR h7 hnew hr' hw'
    ((sCode (.gset INSR (.l 0)) ++ sCode (.gset OUTSW (.l 2))).map Admin.plain ++ rest)
  obtain ⟨cs₂, F₂, hR₂, hF₂, hf₂, r₂⟩ := gset_run (Pf := Pf) t hR₁ (i := INSR) (j := 0) (by decide) (by decide)
    ((sCode (.gset OUTSW (.l 2))).map Admin.plain ++ rest)
  obtain ⟨cs₃, F₃, hR₃, hF₃, hf₃, r₃⟩ := gset_run (Pf := Pf) t hR₂ (i := OUTSW) (j := 2) (by decide)
    (by decide) rest
  have hl0 : upd (upd (locals [r]) 1 r') 2 w' 0 = r := rfl
  have hl2 : upd (upd (locals [r]) 1 r') 2 w' 2 = w' := upd_self
  refine ⟨cs₃, F₃, ?_, hF₃.trans (hF₂.trans hF₁), hf₃.trans hf₂, ?_⟩
  · exact rel_conv hR₃ (by simp only [hl0, hl2]) rfl rfl
  · simp only [List.map_append, List.append_assoc] at r₁ ⊢
    exact r₁.trans (r₂.trans r₃)

/-- The lift's second part: `waitable-set.new`, then the set into its global. -/
theorem lift_b {cs : Store H} {F : Frame} {g m l : Nat → Nat} {st₁ st₂ : DStore} {rp : Option (Nat × Nat)}
    {t : List Nat} {ws : Nat} (hR : Rel hb CBL ma cs F ⟨g, m, l, st₁, rp⟩)
    (hws : dstep st₁ .wsNew = some (st₂, .nat ws)) (hws' : ws < M32) (rest : List Admin) :
    ∃ cs' F', Rel hb CBL ma cs' F' ⟨upd g WS ws, m, upd l 3 ws, st₂, rp⟩ ∧ F'.module = F.module ∧
      cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st₁, rp), t), ⟨cs, F, (callCode .wsNew [] [3] ++ sCode (.gset WS (.l 3))).map
          Admin.plain ++ rest⟩) (((st₂, rp), t), ⟨cs', F', rest⟩) := by
  obtain ⟨F₁, hR₁, hF₁, r₁⟩ := wsnew_run (Pf := Pf) t hR hws hws' ((sCode (.gset WS (.l 3))).map Admin.plain ++ rest)
  obtain ⟨cs₂, F₂, hR₂, hF₂, hf₂, r₂⟩ := gset_run (Pf := Pf) t hR₁ (i := WS) (j := 3) (by decide) (by decide) rest
  refine ⟨cs₂, F₂, rel_conv hR₂ (by simp only [upd_self]) rfl rfl, hF₂.trans hF₁, hf₂, ?_⟩
  simp only [List.map_append, List.append_assoc] at r₁ ⊢
  exact r₁.trans r₂

/-- `task.return` of any number of `i32`s records them as the task's results. -/
theorem lans_retN {cs : Store H} (q : HQ) (t : List Nat) {vs : List Nat} (hv : ∀ v ∈ vs, v < M32) :
    lansAll ma .taskReturn (q, t) cs ((vs.map w).map Val.i32) = some ((q, t ++ vs), cs, []) := by
  have e : (vs.map w).map BitVec.toNat = vs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id vs]
    exact List.map_congr_left fun v hv' => w_toNat (hv v hv')
  simp only [lansAll, isLift, ↓reduceIte, lans, i32s_map, Option.map_some, e]

theorem lans_ret {cs : Store H} (q : HQ) (t : List Nat) {v : Nat} (hv : v < M32) :
    lansAll ma .taskReturn (q, t) cs ([v].map w |>.map Val.i32) = some ((q, t ++ [v]), cs, []) :=
  lans_retN q t (by simpa using hv)

theorem lans_join {cs : Store H} {st st' : DStore} {rp : Option (Nat × Nat)} {t : List Nat} {h x : Nat}
    {u : Silmaril.Wasm.Component.Async.Res} (hh : h < M32) (hx : x < M32)
    (hj : dstep st (.join h x) = some (st', u)) :
    lansAll ma .join ((st, rp), t) cs ([h, x].map w |>.map Val.i32) = some (((st', rp), t), cs, []) := by
  have e₁ : (w h).toNat = h := w_toNat hh
  have e₂ : (w x).toNat = x := w_toNat hx
  have hj' : dstep st (.join (w h).toNat (w x).toNat) = some (st', u) := by rw [e₁, e₂]; exact hj
  simp only [lansAll, isLift, lans, List.map_cons, List.map_nil, Val.i32, ↓reduceIte]
  erw [hj']
  rfl

/-- The lift's last part: `task.return` of the output's readable end, the joins of both ends. -/
theorem lift_c {cs : Store H} {F : Frame} {g m l : Nat → Nat} {st₂ st₃ st₄ : DStore} {rp : Option (Nat × Nat)}
    {t : List Nat} {u₁ u₂ : Silmaril.Wasm.Component.Async.Res}
    (hR : Rel hb CBL ma cs F ⟨g, m, l, st₂, rp⟩) (hret : RetAt hb cs F.module 1)
    (hj₁ : dstep st₂ (.join (g INSR) (g WS)) = some (st₃, u₁))
    (hj₂ : dstep st₃ (.join (g OUTSW) (g WS)) = some (st₄, u₂)) (rest : List Admin) :
    LSteps Pf hb ma (((st₂, rp), t), ⟨cs, F, ((([E.l 1].map eCode).flatten ++
        [Instr.call (ix (biFn .taskReturn))]) ++ ((([E.g INSR, E.g WS].map eCode).flatten ++
        [Instr.call (ix (biFn .join))]) ++ (([E.g OUTSW, E.g WS].map eCode).flatten ++
        [Instr.call (ix (biFn .join))]))).map Admin.plain ++ rest⟩)
      (((st₄, rp), t ++ [l 1]), ⟨cs, F, rest⟩) := by
  have hl1 : l 1 < M32 := (hR.loc 1 (by decide)).2
  have hI : g INSR < M32 := hR.glt INSR (by decide)
  have hW : g WS < M32 := hR.glt WS (by decide)
  have hO : g OUTSW < M32 := hR.glt OUTSW (by decide)
  have r₁ := lcall_stmt (Pf := Pf) (t := t) (b := .taskReturn) (args := [.l 1]) (as := [l 1]) hR
    (by simp [cev, CBL]) hret (x' := ((st₂, rp), t ++ [l 1])) (lans_ret _ _ hl1)
    ((((([E.g INSR, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]) ++
      (([E.g OUTSW, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]))).map Admin.plain ++ rest)
  have hR' : Rel hb CBL ma cs F ⟨g, m, l, st₃, rp⟩ := rel_conv hR rfl rfl rfl
  have r₂ := lcall_stmt (Pf := Pf) (t := t ++ [l 1]) (b := .join) (args := [.g INSR, .g WS])
    (as := [g INSR, g WS]) hR (by simp [cev, NG, INSR, WS]) (imp_arity hR .join (by decide)) (x' := ((st₃, rp), t ++ [l 1]))
    (lans_join hI hW hj₁)
    ((([E.g OUTSW, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]).map Admin.plain ++ rest)
  have r₃ := lcall_stmt (Pf := Pf) (t := t ++ [l 1]) (b := .join) (args := [.g OUTSW, .g WS])
    (as := [g OUTSW, g WS]) hR' (by simp [cev, NG, OUTSW, WS]) (imp_arity hR' .join (by decide)) (x' := ((st₄, rp), t ++ [l 1]))
    (lans_join hO hW hj₂) rest
  simp only [List.map_append, List.append_assoc] at r₁ r₂ r₃ ⊢
  exact r₁.trans (r₂.trans r₃)

/-- The lift's frame: its parameter `r`, six `i32` zeros, an `i64` zero. -/
theorem entry_locals (mi : ModuleInst) {r : Nat} (hr : r < M32) :
    ∀ i, i < CBL → (Frame.forCall mi [Val.i32 (w r)] entryLocals).locals[i]? =
      some (some (Val.i32 (w (locals [r] i)))) ∧ locals [r] i < M32 := by
  have h0 : (0 : Nat) < M32 := by decide
  intro i hi
  match i, hi with
  | 0, _ => exact ⟨rfl, hr⟩
  | 1, _ => exact ⟨rfl, h0⟩
  | 2, _ => exact ⟨rfl, h0⟩
  | 3, _ => exact ⟨rfl, h0⟩
  | 4, _ => exact ⟨rfl, h0⟩
  | 5, _ => exact ⟨rfl, h0⟩
  | 6, _ => exact ⟨rfl, h0⟩
  | n + 7, h => exact absurd h (by unfold CBL; omega)

/-- The globals after the three handle stores. -/
theorem liftG_at (g : Nat → Nat) (r w' ws : Nat) :
    liftG g r w' ws INSR = r ∧ liftG g r w' ws OUTSW = w' ∧ liftG g r w' ws WS = ws :=
  ⟨rfl, rfl, rfl⟩

/-- **The body of the lift**, in its frame: from `Rel` at the frame of the call to `YIELD`. -/
theorem body_run {cs : Store H} {F : Frame} {g m : Nat → Nat} {st st₁ st₂ st₃ st₄ : DStore}
    {rp : Option (Nat × Nat)} {t : List Nat} {r r' w' ws : Nat} {u₁ u₂ : Silmaril.Wasm.Component.Async.Res}
    (hR : Rel hb CBL ma cs F ⟨g, m, locals [r], st, rp⟩) (hret : RetAt hb cs F.module 1)
    (h7 : 7 < F.locals.length)
    (hnew : dstep st .streamNew = some (st₁, .ends r' w')) (hr' : r' < M32) (hw' : w' < M32)
    (hws : dstep st₁ .wsNew = some (st₂, .nat ws)) (hws' : ws < M32)
    (hj₁ : dstep st₂ (.join r ws) = some (st₃, u₁)) (hj₂ : dstep st₃ (.join w' ws) = some (st₄, u₂))
    (U : List Admin) :
    ∃ cs' F', InstR hb ma cs' F'.module (liftG g r w' ws) m ∧ F'.module = F.module ∧ cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), ⟨cs, F, (sCode entry).map Admin.plain ++ U⟩)
        (((st₄, rp), t ++ [r']), ⟨cs', F', vals [Val.i32 (w 1)] ++ .plain .return_ :: U⟩) := by
  obtain ⟨cs₁, F₁, hR₁, hF₁, hf₁, r₁⟩ := lift_a (Pf := Pf) (t := t) hR h7 hnew hr' hw' _
  obtain ⟨cs₂, F₂, hR₂, hF₂, hf₂, r₂⟩ := lift_b (Pf := Pf) (t := t) hR₁ hws hws' _
  have hj₁' : dstep st₂ (.join (liftG g r w' ws INSR) (liftG g r w' ws WS)) = some (st₃, u₁) := hj₁
  have hj₂' : dstep st₃ (.join (liftG g r w' ws OUTSW) (liftG g r w' ws WS)) = some (st₄, u₂) := hj₂
  have hret₂ : RetAt hb cs₂ F₂.module 1 := by
    rw [hF₂, hF₁]
    obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := hret
    exact ⟨a, fi, ps, rs, h1, by rw [hf₂, hf₁]; exact h2, h3, h4, h5⟩
  have r₃ := lift_c (Pf := Pf) (t := t) (rest := vals [Val.i32 (w 1)] ++ .plain .return_ :: U) hR₂ hret₂ hj₁' hj₂'
  have hl1 : upd (upd (upd (locals [r]) 1 r') 2 w') 3 ws 1 = r' := rfl
  rw [hl1] at r₃
  have ecode : (sCode entry).map Admin.plain ++ U =
      (callCode .streamNew [] [1, 2] ++ sCode (.gset INSR (.l 0)) ++ sCode (.gset OUTSW (.l 2))).map
        Admin.plain ++ ((callCode .wsNew [] [3] ++ sCode (.gset WS (.l 3))).map Admin.plain ++
        (((([E.l 1].map eCode).flatten ++ [Instr.call (ix (biFn .taskReturn))]) ++
        ((([E.g INSR, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]) ++
        (([E.g OUTSW, E.g WS].map eCode).flatten ++ [Instr.call (ix (biFn .join))]))).map Admin.plain ++
        (vals [Val.i32 (w 1)] ++ .plain .return_ :: U))) := by
    rw [entry_code]
    simp only [List.map_append, List.append_assoc]
    rfl
  have hI₂ : InstR hb ma cs₂ F₂.module (liftG g r w' ws) m := inst_of_rel hR₂
  refine ⟨cs₂, F₂, hI₂, hF₂.trans hF₁, hf₂.trans hf₁, ?_⟩
  rw [ecode]
  exact r₁.trans (r₂.trans r₃)

/-- **The Core invocation of the lift of `KCore.entry`** on the input's readable end `r` runs to
`YIELD`: the output stream `(r', w')` and the waitable set `ws` are created, `r'` is returned
(`task.return`), both ends join `ws`, the globals become `liftG g r w' ws`. -/
theorem entry_run (Pf : Profile) {cs : Store H} {mi : ModuleInst} {P : Prog} {a : Nat}
    {g m : Nat → Nat} {st st₁ st₂ st₃ st₄ : DStore} {rp : Option (Nat × Nat)} {t : List Nat}
    {r r' w' ws : Nat} {u₁ u₂ : Silmaril.Wasm.Component.Async.Res} (hP : P.entry = entry)
    (hI : InstR hb ma cs mi g m) (hret : RetAt hb cs mi 1) (hen : EntryAt cs mi P a) (hr : r < M32)
    (hnew : dstep st .streamNew = some (st₁, .ends r' w')) (hr' : r' < M32) (hw' : w' < M32)
    (hws : dstep st₁ .wsNew = some (st₂, .nat ws)) (hws' : ws < M32)
    (hj₁ : dstep st₂ (.join r ws) = some (st₃, u₁)) (hj₂ : dstep st₃ (.join w' ws) = some (st₄, u₂)) :
    ∃ cs', InstR hb ma cs' mi (liftG g r w' ws) m ∧ cs'.funcs = cs.funcs ∧
      LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
        (((st₄, rp), t ++ [r']), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) := by
  obtain ⟨fi, ty, ps, rs, hf, hfm, hcode, hexp, hps, hrs⟩ := hen
  let F₀ : Frame := Frame.forCall fi.module [Val.i32 (w r)] entryLocals
  have hI₀ : InstR hb ma cs F₀.module g m := by rw [show F₀.module = mi from hfm]; exact hI
  have hR₀ : Rel hb CBL ma cs F₀ ⟨g, m, locals [r], st, rp⟩ := rel_of_inst hI₀ (entry_locals _ hr)
  have h7 : 7 < F₀.locals.length := by simp [F₀, Frame.forCall, entryLocals]
  have hret₀ : RetAt hb cs F₀.module 1 := by rw [show F₀.module = mi from hfm]; exact hret
  obtain ⟨cs', F', hI', hF', hfs, rb⟩ := body_run (Pf := Pf) (t := t) hR₀ hret₀ h7 hnew hr' hw' hws hws' hj₁ hj₂
    [.plain .unreachable]
  refine ⟨cs', by rw [hF', show F₀.module = mi from hfm] at hI'; exact hI', hfs, ?_⟩
  have hinv : invoke cs a [Val.i32 (w r)] =
      ⟨cs, {}, vals [Val.i32 (w r)] ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hf]
  have r₀ : LSteps Pf hb ma (((st, rp), t), invoke cs a [Val.i32 (w r)])
      (((st, rp), t), ⟨cs, {}, [.frame 1 F₀ [.label 1 [] ((sCode entry).map Admin.plain ++
        [.plain .unreachable])]]⟩) := by
    rw [hinv]
    have hstep := Step.callRefFunc (P := Pf) (host := noHost) (s := cs) (f := {}) (c := .callRefType fi.type)
      (vs := [Val.i32 (w r)]) trivial hf hexp (by simp [hps]) hcode
    rw [hrs, hP] at hstep
    simpa [expression, F₀] using (Relation.ReflTransGen.single (LStep.core (hb := hb) (ma := ma)
      (x := ((st, rp), t)) hstep))
  have r₁ := lsteps_frame {} 1 (lsteps_label 1 [] rb)
  have r₂ : LSteps Pf hb ma (((st₄, rp), t ++ [r']), ⟨cs', {}, [.frame 1 F' [.label 1 []
        (vals [Val.i32 (w 1)] ++ .plain .return_ :: [.plain .unreachable])]]⟩)
      (((st₄, rp), t ++ [r']), ⟨cs', {}, [.frame 1 F' (vals [Val.i32 (w 1)] ++ [.plain .return_])]⟩) := by
    have hstep := Step.returnLabel (P := Pf) (host := noHost) (s := cs') (f := F') (n := 1) (cont := [])
      (vs := [Val.i32 (w 1)]) (rest := [.plain .unreachable])
    exact lsteps_frame {} 1 (.single (.core (by simpa [vals] using hstep)))
  have r₃ : LSteps Pf hb ma (((st₄, rp), t ++ [r']), ⟨cs', {}, [.frame 1 F' (vals [Val.i32 (w 1)] ++
        [.plain .return_])]⟩) (((st₄, rp), t ++ [r']), ⟨cs', {}, vals [Val.i32 (w 1)]⟩) := by
    have hstep := Step.returnFrame (P := Pf) (host := noHost) (s := cs') (f := {}) (fi := F') (n := 1)
      (vs' := []) (vs := [Val.i32 (w 1)]) (rest := []) rfl
    exact .single (.core (by simpa [vals] using hstep))
  exact r₀.trans (r₁.trans (r₂.trans r₃))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Entry
