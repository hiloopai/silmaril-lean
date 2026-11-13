module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Hint
public import Silmaril.Proofs.Wasm.Examples.LRAT.RatEnd
public import Silmaril.Wasm.Examples.Common.Thms

@[expose] public section

/-!
# Sessions of the LRAT checker

Every export of the instantiated checker meets its call specification (`lrat_callSpec`,
`Silmaril.Wasm.Examples.Common.callSpec`) for the abstract state "the DIMACS stream received so
far": a store whose view satisfies `Good xs` is taken to one satisfying `Good (xs ++ c)`, where
`c` is the integer sent by `add_lit` (or the `0` of `end_clause`); `unsat` answers a value that
is nonzero only if the formula of `xs` is unsatisfiable. With the initial invariant
(`lrat_init`, the computed instance's zero memory) and `Common.session_allGood` this gives the
safety of every session (`lrat_session_unsat`).

Every profile, every environment, no determinism assumption. A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Examples.Common
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Logic.SAT

/-! ## The instance -/

theorem lratI_addr (j : Fin lratI.exports.length) : lratI.addr j = j.val := by
  have hj : j.val < 10 := by
    have h8 := lrat_exports.1
    have := j.2
    omega
  unfold ScalarInstance.addr
  rw [lrat_addrs]
  generalize j.val = k at hj ⊢
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | rfl | omega

/-! ## The abstract state -/

/-- The integer of an `i32` argument list. -/
def argInt : List Val → Int
  | [.num ⟨.int .i32, x⟩] => x.toInt
  | _ => 0

/-- The DIMACS integers a call of export `j` with arguments `args` sends: the literal of
`add_lit`, the terminator of `end_clause`, nothing otherwise. -/
def contrib (j : Nat) (args : List Val) : List Int :=
  if j = 0 then [argInt args] else if j = 1 then [0] else []

/-- The DIMACS stream after a call. -/
def nextStream (xs : List Int) (c : Call lratI) : List Int := xs ++ contrib c.1.1.val c.1.2.1

/-- The safety of a call: an `unsat` call answering a nonzero value is right. -/
def CallOk (xs : List Int) (c : Call lratI) : Prop :=
  c.1.1.val = 7 → ∀ v : BitVec 32, Answer.toResult c.2 = .values [Val.i32 v] → v ≠ 0#32 →
    (Dimacs.cnf xs).Unsat

/-- The DIMACS stream sent by a list of calls. -/
def streamOf (l : List (Call lratI)) : List Int := after nextStream [] l

/-- The store represents the DIMACS stream `xs`. -/
def Rep (xs : List Int) (s : Store Nat) : Prop := InvX lratX xs s

/-! ## Views are unique -/

theorem Shape.unique {H : Type} {X : Fix H} {s : Store H} {G G' : List (BitVec 32)}
    {B B' : ByteArray} (h : Shape X s G B) (h' : Shape X s G' B') : G = G' ∧ B = B' := by
  constructor
  · have hg : G.map (fun v => (⟨X.gt, Val.i32 v⟩ : GlobalInst)) =
        G'.map (fun v => (⟨X.gt, Val.i32 v⟩ : GlobalInst)) := h.glob.symm.trans h'.glob
    refine List.map_injective_iff.2 (fun a b hab => ?_) hg
    have h' : Val.i32 a = Val.i32 b := congrArg GlobalInst.value hab
    exact (Silmaril.Wasm.Logic.Hoare.i32_inj h').symm
  · have hm := h.mem.symm.trans h'.mem
    simp only [List.cons.injEq, MemInst.mk.injEq] at hm
    exact hm.1.2

/-! ## The initial invariant -/

theorem leNat_zeros {l : List UInt8} (h : ∀ b ∈ l, b = 0) : Silmaril.Wasm.Logic.Core.leNat l = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [Silmaril.Wasm.Logic.Core.leNat_cons, h b (by simp), ih fun b hb => h b (by simp [hb])]
    rfl

/-- The initial memory reads `0` everywhere. -/
theorem B₀_zero (a : Nat) : wd B₀ a = 0#32 := by
  have hz : ∀ b ∈ B₀.data.toList, b = 0 := by
    have h := lrat_zero.1
    simp only [List.all_eq_true, beq_iff_eq] at h
    exact h
  by_cases ha : a + 4 ≤ B₀.size
  · rw [wd, Silmaril.Wasm.Logic.Core.load_eq ha]
    have hb : ∀ b ∈ Silmaril.Wasm.Logic.Core.bytesAt B₀ ⟨a, 4⟩, b = 0 := fun b hb =>
      hz b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    simp only [leNat_zeros hb, Option.getD_some]
  · rw [wd, Silmaril.Wasm.Logic.Core.load_eq_none (by omega)]
    rfl

theorem lrat_shape₀ : Shape lratX lratS G₀ B₀ := by
  refine ⟨rfl, lrat_globals, rfl, ?_, lrat_zero.2⟩
  obtain ⟨hty, hlen⟩ := lrat_mems
  obtain ⟨mi, hmi⟩ := List.length_eq_one_iff.1 hlen
  have ht : mi.type = lratMt := by
    rw [hmi] at hty
    simpa using hty
  have hB : B₀ = mi.bytes := by
    rw [show B₀ = ((lratS.mems[0]?).map (·.bytes)).getD .empty from rfl, hmi]
    rfl
  show lratS.mems = [⟨lratX.mt, B₀⟩]
  rw [hmi, hB, show lratX.mt = lratMt from rfl, ← ht]

/-- **The initial invariant**: the instantiated checker represents the empty DIMACS stream. -/
theorem lrat_init : Rep [] lratS := by
  refine ⟨G₀, B₀, lrat_shape₀, ?_⟩
  have hbuf : bufWords G₀ B₀ = [] := rfl
  have hmod : ∀ τ, Models τ B₀ := fun τ =>
    models_iff.2 fun id _ hl => absurd (by simp [entryLen, B₀_zero]) hl
  exact {
    size := lrat_zero.2
    mode_le := by decide
    base_le := by decide
    cstart_le := by decide
    top_le := by decide
    cstart_dvd := by decide
    top_dvd := by decide
    stamp_le := by decide
    stale := fun x _ => by rw [B₀_zero]; simp
    tag_le := by simp [tagOf, B₀_zero]
    cov_le := fun _ _ => by simp [covOf, tagOf, B₀_zero]
    entries := fun id _ hl => absurd (by simp [entryLen, B₀_zero]) hl
    sat := fun _ => ⟨fun _ => true, hmod _⟩
    unsat := fun h => absurd rfl h
    input := fun _ => by
      rw [hbuf]; exact ⟨fun _ h => absurd h (List.not_mem_nil), rfl, fun τ _ => hmod τ⟩
    step := fun h => absurd h (by decide) }

/-! ## The functions of the instance -/

/-- The function of export `j` runs the module's function `j`, at its type. -/
theorem lrat_fn (j : Nat) (hj : j < 10) : ∃ (fi : FuncInst Nat) (f : Func) (ty : CCompType),
    lratS.funcs[j]? = some fi ∧ lratModule.funcs[j]? = some f ∧ lratTys[j]? = some ty ∧
    fi.code = .wasm f ∧ fi.module = lratMi ∧ Expand fi.type ty := by
  have h := List.all_eq_true.1 lrat_fnOk j (List.mem_range.2 hj)
  unfold fnOk at h
  split at h
  · rename_i fi f ty hfi hf hty
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, hm⟩, he⟩ := h
    refine ⟨fi, f, ty, hfi, hf, hty, ?_, hm, Expand.iff.2 he⟩
    unfold codeMatches at hc
    split at hc
    · rename_i g hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hb, hl⟩, ht⟩ := hc
      rw [hg]
      have hb' := ibeqs_sound _ _ hb
      cases g; cases f
      simp_all
    · cases hc
  · cases h

/-! ## Arguments -/

theorem export_get {j : Nat} {hj : j < lratI.exports.length} {ft : FnType}
    (h : lratI.exports[j]? = some ft) : lratI.exports.get ⟨j, hj⟩ = ft := by
  rw [List.get_eq_getElem]
  exact Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans h)

theorem args_i32 {args : List Val}
    (h : List.Forall₂ ScalarType.HasVal [.num (.int .i32)] args) : ∃ x, args = [Val.i32 x] := by
  cases h with
  | cons hv hrest =>
    cases hrest
    obtain ⟨bits, rfl⟩ := hv
    exact ⟨bits, rfl⟩

theorem args_nil {args : List Val} (h : List.Forall₂ ScalarType.HasVal [] args) : args = [] :=
  List.forall₂_nil_left_iff.1 h

/-! ## From body postconditions to call specifications -/

/-- An export without results that keeps the invariant meets its call specification. -/
theorem post_of_stepPost {f : lratI.F.Op} (hf : f.1.val ≠ 7) {s : Store Nat}
    {G : List (BitVec 32)} {B : ByteArray} (hS : Shape lratX s G B) {s' : Store Nat} {F : Frame}
    {o : Outcome} (h : stepPost lratX G B (contrib f.1.val f.2.1) s' F o) :
    bodyPost 0 ((callSpec lratI Rep nextStream CallOk f).post s f.2.1) s' F o := by
  obtain ⟨rfl, G', B', hS', hG'⟩ := h
  refine ⟨rfl, fun a hR _ _ _ _ => ?_⟩
  obtain ⟨G₁, B₁, hS₁, hG₁⟩ := hR
  obtain ⟨rfl, rfl⟩ := hS.unique hS₁
  exact ⟨fun h7 => absurd h7 hf, G', B', hS', hG' a hG₁⟩

/-- `unsat` meets its call specification. -/
theorem post_of_unsatPost {f : lratI.F.Op} (hc : contrib f.1.val f.2.1 = []) {s : Store Nat}
    {G : List (BitVec 32)} {B : ByteArray} (hS : Shape lratX s G B) {s' : Store Nat} {F : Frame}
    {o : Outcome} (h : unsatPost lratX G B s' F o) :
    bodyPost 1 ((callSpec lratI Rep nextStream CallOk f).post s f.2.1) s' F o := by
  obtain ⟨v, rfl, hS', hu⟩ := h
  refine ⟨rfl, fun a hR r hr w hw => ?_⟩
  obtain ⟨G₁, B₁, hS₁, hG₁⟩ := hR
  obtain ⟨rfl, rfl⟩ := hS.unique hS₁
  have hr' : r = .values [Val.i32 v] := (Option.some.inj hr).symm
  subst hr'
  have hwr : Answer.toResult w = .values [Val.i32 v] := Answer.toResult_of_ofResult? hw
  refine ⟨fun _ v' hv' hne => ?_, G, B, hS', ?_⟩
  · rw [hwr] at hv'
    simp only [Result.values.injEq, List.cons.injEq, and_true] at hv'
    obtain rfl := Silmaril.Wasm.Logic.Hoare.i32_inj hv'
    exact hu a hG₁ hne
  · show Good (a ++ contrib f.1.val f.2.1) G B
    rw [hc, List.append_nil]
    exact hG₁

/-! ## Every export meets its call specification -/

theorem G_eight {G : List (BitVec 32)} (h : G.length = 8) :
    ∃ m t c S cf sid u n, G = [m, t, c, S, cf, sid, u, n] := by
  match G, h with
  | [m, t, c, S, cf, sid, u, n], _ => exact ⟨m, t, c, S, cf, sid, u, n, rfl⟩

theorem code_eq (body : List Instr) :
    vals ([] : List Val).reverse ++ expression body ++ [] = expression body := by simp

variable {P : Profile} {host : HostSemantics Nat}

/-- A specification from the body, for the checker's functions. -/
theorem spec_of_body {f : lratI.F.Op} {fi : FuncInst Nat} {fn : Func} {ps rs : Ty (.list .val)}
    (hfi : lratS.funcs[f.1.val]? = some fi) (hcode : fi.code = .wasm fn)
    (hexp : Expand fi.type (.func ps rs)) (hlen : f.2.1.length = ps.length)
    (hmod : fi.module = lratMi)
    (hbody : ∀ s m t c S cf sid u n B, Shape lratX s [m, t, c, S, cf, sid, u, n] B →
      ∀ a, Good a [m, t, c, S, cf, sid, u, n] B →
      HWP P host s (Frame.forCall lratX.mi f.2.1 fn.locals) (expression fn.body)
        (bodyPost rs.length ((callSpec lratI Rep nextStream CallOk f).post s f.2.1))) :
    FSpecValid P host (lratI.addr f.1) (callSpec lratI Rep nextStream CallOk f) := by
  rw [lratI_addr]
  refine FSpecValid.of_body_hwp (fun s _ hpre => ?_) hcode hexp
    (fun _ _ hpre => by rw [hpre.1]; exact hlen) fun s args hpre => ?_
  · obtain ⟨-, a, G, B, hS, -⟩ := hpre
    rw [hS.funcs]
    exact hfi
  · obtain ⟨rfl, a, G, B, hS, hG⟩ := hpre
    obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
    rw [hmod]
    exact hbody s m t c S cf sid u n B hS a hG

set_option maxHeartbeats 1000000 in
/-- Export `0` meets its call specification. -/
theorem spec_addLit (hj : 0 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨0, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨0, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨0, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 0 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[0]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (addLit_hwp hX hS hG (x := x))

set_option maxHeartbeats 1000000 in
/-- Export `1` meets its call specification. -/
theorem spec_endClause (hj : 1 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨1, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨1, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨1, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 1 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[1]? = some ⟨[], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain rfl := args_nil hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  have hb := addLit_hwp (P := P) (host := host) hX hS hG (x := 0)
  unfold AddLitHwp at hb
  rw [show ((0 : BitVec 32).toInt) = 0 from rfl] at hb
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) hb

set_option maxHeartbeats 1000000 in
/-- Export `2` meets its call specification. -/
theorem spec_stepBegin (hj : 2 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨2, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨2, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨2, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 2 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[2]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (stepBegin_hwp hX hS hG x)

set_option maxHeartbeats 1000000 in
/-- Export `3` meets its call specification. -/
theorem spec_stepLit (hj : 3 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨3, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨3, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨3, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 3 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[3]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (stepLit_hwp hX hS hG x)

set_option maxHeartbeats 1000000 in
/-- Export `4` meets its call specification. -/
theorem spec_stepHint (hj : 4 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨4, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨4, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨4, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 4 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[4]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (stepHint_hwp hX hS hG x)

set_option maxHeartbeats 1000000 in
/-- Export `5` meets its call specification. -/
theorem spec_stepEnd (hj : 5 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨5, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨5, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨5, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 5 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[5]? = some ⟨[], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain rfl := args_nil hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (stepEnd_hwp hX hS hG)

set_option maxHeartbeats 1000000 in
/-- Export `6` meets its call specification. -/
theorem spec_delete (hj : 6 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨6, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨6, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨6, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 6 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[6]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a _ => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (delete_hwp hX hS x)

set_option maxHeartbeats 1000000 in
/-- Export `7` meets its call specification. -/
theorem spec_unsat (hj : 7 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨7, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨7, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨7, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 7 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[7]? = some ⟨[], [.num (.int .i32)]⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain rfl := args_nil hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a _ => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_unsatPost rfl hS h) (unsat_hwp hX hS)

set_option maxHeartbeats 1000000 in
/-- Export `8` (`rat_begin`) meets its call specification. -/
theorem spec_ratBegin (hj : 8 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨8, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨8, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨8, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 8 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[8]? = some ⟨[.num (.int .i32)], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain ⟨x, rfl⟩ := args_i32 hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (ratBegin_hwp hX hS hG x)

set_option maxHeartbeats 1000000 in
/-- Export `9` (`rat_end`) meets its call specification. -/
theorem spec_ratEnd (hj : 9 < lratI.exports.length) (args : List Val)
    (hargs : List.Forall₂ ScalarType.HasVal (lratI.exports.get ⟨9, hj⟩).params args) :
    FSpecValid P host (lratI.addr ⟨9, hj⟩)
      (callSpec lratI Rep nextStream CallOk ⟨⟨9, hj⟩, ⟨args, hargs⟩⟩) := by
  obtain ⟨fi, fn, ty, hfi, hfn, hty, hcode, hmod, hexp⟩ := lrat_fn 9 (by decide)
  have hargs' := hargs
  rw [export_get (show lratI.exports[9]? = some ⟨[], []⟩ by rw [lrat_exports_eq]; rfl)] at hargs'
  obtain rfl := args_nil hargs'
  simp only [lratModule, lratTys] at hfn hty
  cases hfn; cases hty
  refine spec_of_body hfi hcode hexp rfl hmod fun s m t c S cf sid u n B hS a hG => ?_
  rw [← code_eq]
  have hX := lratX_ok
  exact HWP.mono (fun _ _ _ h => post_of_stepPost (by simp) hS h) (ratEnd_hwp hX hS hG)

/-- **Every export of the checker meets its call specification**, every profile and host. -/
theorem lrat_spec (f : lratI.F.Op) :
    FSpecValid P host (lratI.addr f.1) (callSpec lratI Rep nextStream CallOk f) := by
  obtain ⟨⟨j, hj⟩, args, hargs⟩ := f
  have hj8 : j < 10 := by have := lrat_exports.1; omega
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · exact spec_addLit hj args hargs
  · exact spec_endClause hj args hargs
  · exact spec_stepBegin hj args hargs
  · exact spec_stepLit hj args hargs
  · exact spec_stepHint hj args hargs
  · exact spec_stepEnd hj args hargs
  · exact spec_delete hj args hargs
  · exact spec_unsat hj args hargs
  · exact spec_ratBegin hj args hargs
  · exact spec_ratEnd hj args hargs
  · omega

/-! ## Sessions -/

/-- **Safety of the LRAT checker.** In every closed-world Core 3.0 session of export calls on
the instantiated checker (any order, any arguments, any environment, any profile), every call
of `unsat` that answers a nonzero value is right: the DIMACS formula sent before it (by
`add_lit` and `end_clause`) is unsatisfiable. -/
theorem lrat_session_unsat {K : Env lratI.E} {l : List (Call lratI)}
    (hs : Session P lratI K lratI.store l) {l₁ l₂ : List (Call lratI)} {c : Call lratI}
    (hl : l = l₁ ++ c :: l₂) (hc : c.1.1.val = 7) {v : BitVec 32}
    (hv : Answer.toResult c.2 = .values [Val.i32 v]) (hne : v ≠ 0#32) :
    (Dimacs.cnf (streamOf l₁)).Unsat := by
  have hall := session_allGood (P := P) (K := K) (R := Rep) (next := nextStream) (Good := CallOk)
    (fun f => lrat_spec f) (s := lratI.store) (a := []) (l := l) (lratI_store ▸ lrat_init) hs
  rw [hl] at hall
  exact allGood_append hall hc v hv hne

end Silmaril.Wasm.Examples.LRAT
