module

public import Silmaril.Proofs.Wasm.SSA.OutOfSSA.Inversion

/-!
# Out of SSA: the region terminates when its decompilation does

`term`: if the decompiled code of a region terminates (with any outcome), the
region evaluates. With the forward simulation (`sim`) and determinism of the
fragment, the region's exit then corresponds to the code's outcome, so
`decompileFunc_complete` follows: every terminating outcome of the
decompiled function is an outcome of the SSA function.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.OutOfSSA

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.Wasm (IntType)

/-- A branch to a Wasm label of an outer label is never a branch to the innermost one. -/
theorem LabelOut.not_brk0 {labels : List DLabel} {wd : Nat} {fty : Option IntType}
    {ls : List WVal} {base ℓ : Nat} {v : SVal} {ls' : List WVal} {r : Option WVal}
    (hw : ∀ w L, DLabel.block w L ∈ labels → w < wd)
    (h : LabelOut labels (wd + 1) fty ls base ℓ v (.brk 0 ls' r)) : False := by
  unfold LabelOut at h
  split at h
  · cases h.1
  · rcases h with ⟨-, h⟩ | ⟨_, -, h, -⟩ <;> cases h
  · rename_i w L heq
    obtain ⟨_, h, -⟩ := h
    have := hw w L (List.mem_of_getElem? heq)
    simp only [Out.brk.injEq] at h
    omega
  · exact h

theorem opExpr_static {vars : List VLoc} {o : Op} {a : Tm Prim} {e : Expr} {ty : IntType}
    (h : opExpr vars o a = some (e, ty)) : ∃ A, staticLoc vars a = some A := by
  simp only [opExpr, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨A, hA, -⟩ := h
  exact ⟨A, hA⟩

/-- The region form of the statement. -/
def Term (r : Region Prim) : Prop :=
  ∀ (env : Env WVal) (c : DCtx) (st : DState) (code : List Expr) (st' : DState)
    (ls : List WVal) (o : Out (Option WVal)),
    dR c r st = some (code, st') → VarsOK ls c.vars env → WF c st.next → st'.next ≤ ls.length →
    Seq ls none code o → ∃ l v, Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval instr env r () l v ()

/-- After a fresh assignment, the rest terminates. -/
theorem let₁_op_back {env : Env WVal} {c : DCtx} {st s₂ : DState} {ty : IntType}
    {code' : List Expr} {ls : List WVal} {w : WVal} {r : Region Prim} {o : Out (Option WVal)}
    (ih : Term r)
    (hd : dR { c with vars := .loc st.next ty :: c.vars } r ⟨st.next + 1, ty :: st.types⟩ =
      some (code', s₂))
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : s₂.next ≤ ls.length)
    (hs : Seq (ls.set st.next w) none code' o) :
    ∃ l v, Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval instr (extend env (.atom w)) r () l v () := by
  have hm := dR_mono r hd
  simp only at hm
  have hx : st.next < ls.length := by omega
  have hfr : ∀ x, x < st.next → (ls.set st.next w)[x]? = ls[x]? :=
    fun x hx' => getElem?_set_ne' (by omega)
  exact ih _ _ _ _ _ (ls.set st.next w) o hd
    (varsOK_cons (varsOK_frame hv fun V hV x hxV => hfr x (hwf.vars V hV x hxV))
      (by simp [readL, hx]))
    ⟨fun W hW x hxW => by
      rcases List.mem_cons.1 hW with rfl | hW
      · simp [VLoc.locs] at hxW; simp; omega
      · have := hwf.vars W hW x hxW; simp; omega,
     fun w L hL => ⟨(hwf.labels w L hL).1, fun x hxL => by
      have := (hwf.labels w L hL).2 x hxL; simp; omega⟩⟩
    (by rw [List.length_set]; exact hlen) hs

/-- An abrupt outcome is not a normal completion. -/
private theorem abrupt_ne_ok {o : Out (Option WVal)} (hab : o.Abrupt) {ls : List WVal}
    {r : Option WVal} : o ≠ .ok ls r := by
  rintro rfl
  exact hab

/-- A loop never completes by branching to its own label. -/
private theorem LoopExit.not_brk0 {ty : Option IntType} {ls : List WVal} {r : Option WVal}
    {o : Out (Option WVal)} (h : LoopExit ty (.brk 0 ls r) o) : False := by
  cases h

/-- The first instruction of a sequence runs. -/
private theorem seq_first {ls : List WVal} {r : Option WVal} {e : Expr} {es : List Expr}
    {o : Out (Option WVal)} (h : Seq ls r (e :: es) o) : ∃ o', Exec ls e o' := by
  rcases seq_cons_inv h with ⟨_, _, hx, -⟩ | ⟨hx, -⟩
  · exact ⟨_, hx⟩
  · exact ⟨_, hx⟩

/-- The second of two instructions runs after the first completes normally. -/
private theorem seq_second {ls ls₁ : List WVal} {x y : Expr} {o : Out (Option WVal)}
    (hseq : Seq ls none [x, y] o) (hx : Exec ls x (.ok ls₁ none)) : ∃ o', Exec ls₁ y o' := by
  rcases seq_cons_inv hseq with ⟨ls₂, r₂, hx', hs⟩ | ⟨hx', hab⟩
  · have hls : ls₂ = ls₁ := (Out.ok.inj (Silmaril.Wasm.SSA.Exec.det hx' hx)).1
    obtain ⟨o', hy⟩ := seq_first hs
    exact ⟨o', hls ▸ hy⟩
  · exact (abrupt_ne_ok hab (Silmaril.Wasm.SSA.Exec.det hx' hx)).elim

/-- A region whose innermost label is a Wasm block at depth `w` that exits to that
label runs its code into a branch to the block, with the label's layout holding the
value. -/
private theorem sim_brk0 {env : Env WVal} {c : DCtx} {r : Region Prim} {st st' : DState}
    {code : List Expr} {ls : List WVal} {w : Nat} {L : VLoc} {v : SVal} {out : Out (Option WVal)}
    (hd : dR c r st = some (code, st'))
    (hev : Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval instr env r () 0 v ())
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : st'.next ≤ ls.length)
    (hl : c.labels[0]? = some (.block w L)) (hw : c.wdepth = w + 1) (hs : Seq ls none code out) :
    ∃ ls', out = .brk 0 ls' none ∧ readL ls' L = some v ∧ ls'.length = ls.length ∧
      ∀ x, x < st.next → x ∉ L.locs → ls'[x]? = ls[x]? := by
  obtain ⟨o', hs', hlo⟩ := sim hev c st code st' ls hd hv hwf hlen
  have ho : out = o' := Silmaril.Wasm.SSA.Seq.det hs hs'
  have hlo' : ∃ ls', o' = .brk 0 ls' none ∧ readL ls' L = some v ∧ ls'.length = ls.length ∧
      ∀ x, x < st.next → x ∉ L.locs → ls'[x]? = ls[x]? := by
    simpa only [LabelOut, hl, hw, Nat.add_sub_cancel, Nat.sub_self] using hlo
  rw [ho]
  exact hlo'

open Silmaril.Isotope.LambdaSSA.Semantics in
/-- The loop of a `cfg` block terminates only through a CFG execution. -/
theorem loop_term {env : Env WVal} {bs : Fin 1 → Region Prim} {c : DCtx} {L : VLoc}
    {st₂ st₃ : DState} {cb : List Expr} {base : Nat}
    (hd : dR (loopCtx c L) (bs ⟨0, Nat.one_pos⟩) st₂ = some (cb, st₃))
    (ihb : Term (bs ⟨0, Nat.one_pos⟩))
    (hwf : WF c base) (hLb : ∀ x ∈ L.locs, base ≤ x ∧ x < st₂.next) (hb : base ≤ st₂.next) :
    ∀ {ls : List WVal} {e : Expr} {o : Out (Option WVal)}, Exec ls e o → e = .loop none cb →
      ∀ init, readL ls L = some init → VarsOK ls c.vars env → st₃.next ≤ ls.length →
      ∃ l v, Region.Follow instr env bs 0 init () l v () := by
  intro ls e o h
  have hwfl : WF (loopCtx c L) st₂.next := (hwf.mono hb).loop fun x hx => (hLb x hx).2
  have hw : ∀ w L', DLabel.block w L' ∈ c.labels → w < c.wdepth := fun w L' h =>
    (hwf.labels w L' h).1
  induction h using Exec.rec (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case loop ls ty body out o' hs hx _ =>
    show Expr.loop ty body = .loop none cb → ∀ init, readL ls L = some init →
      VarsOK ls c.vars env → st₃.next ≤ ls.length →
      ∃ l v, Region.Follow instr env bs 0 init () l v ()
    intro heq init hrd hv hlen
    have hs' : Seq ls none cb out := (Expr.loop.inj heq).2 ▸ hs
    obtain ⟨next, middle, hev⟩ := ihb (extend env init) _ _ _ _ ls out hd (varsOK_cons hv hrd)
      hwfl hlen hs'
    -- The body cannot branch back: the loop would not complete with `out`.
    have hn : next ≠ 0 := fun hn => by
      obtain ⟨ls', hout, -⟩ := sim_brk0 hd (hn ▸ hev) (varsOK_cons hv hrd) hwfl hlen rfl rfl hs'
      exact LoopExit.not_brk0 (hout ▸ hx)
    exact ⟨next - 1, middle, .step Nat.one_pos hev (.exit (by omega))⟩
  case loop_back ls ls₂ ty body r o' hs hr _ ih =>
    show Expr.loop ty body = .loop none cb → ∀ init, readL ls L = some init →
      VarsOK ls c.vars env → st₃.next ≤ ls.length →
      ∃ l v, Region.Follow instr env bs 0 init () l v ()
    intro heq init hrd hv hlen
    have hs' : Seq ls none cb (.brk 0 ls₂ r) := (Expr.loop.inj heq).2 ▸ hs
    obtain ⟨next, middle, hev⟩ := ihb (extend env init) _ _ _ _ ls _ hd (varsOK_cons hv hrd)
      hwfl hlen hs'
    -- A branch to an outer label leaves the loop, not to its head.
    have h0 : next = 0 := by
      obtain ⟨o'', hs'', hlo⟩ := sim hev _ _ _ _ ls hd (varsOK_cons hv hrd) hwfl hlen
      have ho : Out.brk 0 ls₂ r = o'' := Silmaril.Wasm.SSA.Seq.det hs' hs''
      match next, hlo with
      | 0, _ => rfl
      | k + 1, hlo => exact (LabelOut.not_brk0 hw (LabelOut.succ.1 (ho ▸ hlo))).elim
    obtain ⟨ls₂', hbrk, hrd₂, hl₂, hfr₂⟩ :=
      sim_brk0 hd (h0 ▸ hev) (varsOK_cons hv hrd) hwfl hlen rfl rfl hs'
    have hls₂ : ls₂ = ls₂' := (Out.brk.inj hbrk).2.1
    have hfr₂' : ∀ x, x < base → ls₂[x]? = ls[x]? := fun x hx =>
      hls₂ ▸ hfr₂ x (by omega) (fun h => by have := (hLb x h).1; omega)
    obtain ⟨l, v, hf⟩ := ih heq middle (hls₂ ▸ hrd₂)
      (varsOK_frame hv fun V hV x hx => hfr₂' x (hwf.vars V hV x hx)) (by rw [hls₂, hl₂]; exact hlen)
    exact ⟨l, v, .step Nat.one_pos (h0 ▸ hev) hf⟩
  all_goals first
    | exact True.intro
    | (intro heq; cases heq)

/-! ## Termination, one region constructor at a time -/

/-- A decompiled branch reads its argument from a static location. -/
private theorem dR_br_static {c : DCtx} {l : Nat} {a : Tm Prim} {st : DState}
    {res : List Expr × DState} (hd : dR c (.br l a) st = some res) :
    ∃ V, staticLoc c.vars a = some V := by
  simp only [dR] at hd
  split at hd
  · split at hd
    · exact ⟨.unit, rfl⟩
    · cases hd
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
    obtain ⟨V, hV, -⟩ := hd
    exact ⟨V, hV⟩
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
    obtain ⟨V, hV, -⟩ := hd
    exact ⟨V, hV⟩
  · cases hd

open Silmaril.Isotope.LambdaSSA.Semantics in
private theorem term_br (l : Nat) (a : Tm Prim) : Term (.br l a) := by
  intro env c st code st' ls o hd hv _ _ _
  obtain ⟨V, hV⟩ := dR_br_static hd
  obtain ⟨v, hev, -⟩ := staticLoc_eval hv a hV
  exact ⟨l, v, .br hev⟩

/-- A fresh assignment `x := o(a)` followed by `code'` runs: the operator returns `w`
and the rest runs on the updated locals, or the operator traps. -/
private theorem localSet_op_inv {ls : List WVal} {x : Nat} {o : Op} {es : List Expr}
    {ws : List WVal} {code' : List Expr} {out : Out (Option WVal)}
    (hargs : Args ls es (.ok ls ws)) (hseq : Seq ls none (.localSet x (.op o es) :: code') out) :
    (∃ w, o.eval ws = some (.val w) ∧ Seq (ls.set x w) none code' out) ∨
      o.eval ws = some .trap := by
  rcases seq_cons_inv hseq with ⟨ls₁, r₁, hx, hs⟩ | ⟨hx, hab⟩
  · rcases exec_localSet_inv hx with ⟨ls', w, he, heq⟩ | ⟨-, hab⟩
    · rcases exec_op_inv he hargs with ⟨w', hev, heq'⟩ | ⟨-, heq'⟩
      · obtain ⟨hls₁, hr₁⟩ : ls₁ = ls'.set x w ∧ r₁ = none := Out.ok.inj heq
        obtain ⟨hls', hw⟩ : ls' = ls ∧ some w = some w' := Out.ok.inj heq'
        have hs' : Seq (ls.set x w') none code' out := by
          rw [← hls', ← Option.some.inj hw, ← hr₁, ← hls₁]
          exact hs
        exact .inl ⟨w', hev, hs'⟩
      · cases heq'
    · exact hab.elim
  · rcases exec_localSet_inv hx with ⟨_, _, _, hout⟩ | ⟨he, hab⟩
    · exact (abrupt_ne_ok hab hout).elim
    · rcases exec_op_inv he hargs with ⟨_, _, hout⟩ | ⟨ht, -⟩
      · exact (abrupt_ne_ok hab hout).elim
      · exact .inr ht

/-- A `let₁` of a non-static term decompiles to a fresh assignment of an operator. -/
private theorem dR_let₁_op_inv {c : DCtx} {t : Tm Prim} {r : Region Prim} {st st' : DState}
    {code : List Expr} (hd : dR c (.let₁ t r) st = some (code, st'))
    (hst : staticLoc c.vars t = none) :
    ∃ o a e ty code', t = .op (.op o) a ∧ opSafe c.vars o a = true ∧
      opExpr c.vars o a = some (e, ty) ∧
      dR { c with vars := .loc st.next ty :: c.vars } r ⟨st.next + 1, ty :: st.types⟩ =
        some (code', st') ∧ code = .localSet st.next e :: code' := by
  simp only [dR, hst] at hd
  split at hd
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, hsafe, ⟨e, ty⟩, hop, ⟨code', s₂⟩, hd, rfl, rfl⟩ := hd
    refine ⟨_, _, e, ty, code', rfl, ?_, hop, hd, rfl⟩
    by_contra hn
    simp [guard, hn] at hsafe
  · cases hd

open Silmaril.Isotope.LambdaSSA.Semantics in
private theorem term_let₁ (t : Tm Prim) (r : Region Prim) (ih : Term r) : Term (.let₁ t r) := by
  intro env c st code st' ls o hd hv hwf hlen hseq
  cases hst : staticLoc c.vars t with
  | some V =>
      show ∃ l v, Region.Eval instr env (.let₁ t r) () l v ()
      have hd' : dR { c with vars := V :: c.vars } r st = some (code, st') := by
        simpa only [dR, hst] using hd
      obtain ⟨v, hev, hrd⟩ := staticLoc_eval hv t hst
      have hwf' : WF { c with vars := V :: c.vars } st.next :=
        ⟨fun W hW x hx => by
          rcases List.mem_cons.1 hW with rfl | hW
          · exact staticLoc_below hwf.vars _ hst x hx
          · exact hwf.vars W hW x hx, hwf.labels⟩
      obtain ⟨l, w, h⟩ := ih (extend env v) _ st code st' ls o hd' (varsOK_cons hv hrd) hwf' hlen hseq
      exact ⟨l, w, .let₁ hev h⟩
  | none =>
      show ∃ l v, Region.Eval instr env (.let₁ t r) () l v ()
      obtain ⟨o', a, e, ty, code', ht, hsafe, hop, hd', hcode⟩ := dR_let₁_op_inv hd hst
      obtain ⟨A, hA⟩ := opExpr_static hop
      obtain ⟨va, hva, hrA⟩ := staticLoc_eval hv a hA
      obtain ⟨es, ws, he, hvaw, hargs⟩ := opExpr_exec hv hop hva
      have hseq' : Seq ls none (.localSet st.next (.op o' es) :: code') o := he ▸ hcode ▸ hseq
      rw [ht]
      rcases localSet_op_inv hargs hseq' with ⟨w, hev, hs⟩ | htrap
      · obtain ⟨l, v, h⟩ := let₁_op_back ih hd' hv hwf hlen hs
        exact ⟨l, v, .let₁ (.op hva (by simp [instr, Prim.run, decodeList_encodeList, hev, hvaw]))
          h⟩
      · exact (opSafe_noTrap hsafe hA (hvaw ▸ hrA) htrap).elim

/-- A `let₂` decompiles its body with the two components of a static pair in scope. -/
private theorem dR_let₂_inv {c : DCtx} {t : Tm Prim} {r : Region Prim} {st st' : DState}
    {code : List Expr} (hd : dR c (.let₂ t r) st = some (code, st')) :
    ∃ A B, staticLoc c.vars t = some (.pair A B) ∧
      dR { c with vars := B :: A :: c.vars } r st = some (code, st') := by
  simp only [dR] at hd
  split at hd
  · exact ⟨_, _, ‹_›, hd⟩
  · cases hd

open Silmaril.Isotope.LambdaSSA.Semantics in
private theorem term_let₂ (t : Tm Prim) (r : Region Prim) (ih : Term r) : Term (.let₂ t r) := by
  intro env c st code st' ls o hd hv hwf hlen hseq
  obtain ⟨A, B, hAB, hd'⟩ := dR_let₂_inv hd
  obtain ⟨v, hev, hrd⟩ := staticLoc_eval hv t hAB
  obtain ⟨va, vb, hA, hB, hv'⟩ := readL_pair.1 hrd
  have hbA : ∀ x ∈ (VLoc.pair A B).locs, x < st.next := staticLoc_below hwf.vars _ hAB
  have hwf' : WF { c with vars := B :: A :: c.vars } st.next :=
    ⟨fun W hW x hx => by
      rcases List.mem_cons.1 hW with rfl | hW
      · exact hbA x (by simp [VLoc.locs, hx])
      rcases List.mem_cons.1 hW with rfl | hW
      · exact hbA x (by simp [VLoc.locs, hx])
      · exact hwf.vars W hW x hx, hwf.labels⟩
  obtain ⟨l, w, h⟩ := ih (extend (extend env va) vb) _ st code st' ls o hd'
    (varsOK_cons (varsOK_cons hv hA) hB) hwf' hlen hseq
  exact ⟨l, w, .let₂ (hv' ▸ hev) h⟩

/-- A `case` decompiles only on a truthiness test or a trapping operator. -/
private theorem dR_case_inv {c : DCtx} {t : Tm Prim} {l r : Region Prim} {st : DState}
    {res : List Expr × DState} (hd : dR c (.case t l r) st = some res) :
    (∃ a, t = .op .truthy a) ∨ ∃ o a, t = .op (.opT o) a := by
  simp only [dR] at hd
  split at hd
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · cases hd

/-- The decompiled form of a truthiness `case`: an `if` on the tested atom. -/
private theorem dR_case_truthy_inv {c : DCtx} {a : Tm Prim} {l r : Region Prim}
    {st st' : DState} {code : List Expr}
    (hd : dR c (.case (.op .truthy a) l r) st = some (code, st')) :
    ∃ A e cl s₁ cr, staticLoc c.vars a = some A ∧ A.atomExpr = some e ∧
      dR { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 } l st = some (cl, s₁) ∧
      dR { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 } r s₁ = some (cr, st') ∧
      code = [.if_ none e cl cr] := by
  simp only [dR, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨A, hA, e, he, ⟨cl, s₁⟩, h₁, ⟨cr, s₂⟩, h₂, rfl, rfl⟩ := hd
  exact ⟨A, e, cl, s₁, cr, hA, he, h₁, h₂, rfl⟩

/-- The branches of an `if` run in a context with one more Wasm label and a unit
variable. -/
private theorem WF.pushIf {c : DCtx} {n : Nat} (h : WF c n) :
    WF { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 } n := by
  refine ⟨fun W hW x hx => ?_, fun w L hL => ⟨?_, (h.labels w L hL).2⟩⟩
  · rcases List.mem_cons.1 hW with rfl | hW
    · simp [VLoc.locs] at hx
    · exact h.vars W hW x hx
  · have := (h.labels w L hL).1
    show w < c.wdepth + 1
    omega

open Silmaril.Isotope.LambdaSSA.Semantics in
private theorem term_case_truthy (a : Tm Prim) (l r : Region Prim) (ihl : Term l)
    (ihr : Term r) : Term (.case (.op .truthy a) l r) := by
  intro env c st code st' ls o hd hv hwf hlen hseq
  obtain ⟨A, e, cl, s₁, cr, hA, he, h₁, h₂, hcode⟩ := dR_case_truthy_inv hd
  obtain ⟨va, hva, hrA⟩ := staticLoc_eval hv a hA
  obtain ⟨out, hx⟩ := seq_first (hcode ▸ hseq)
  obtain ⟨ls₁, cv, b, o', hc, hb, hs, -⟩ : ∃ ls₁ cv b o', Exec ls e (.ok ls₁ (some cv)) ∧
      cv.truthy = some b ∧ Seq ls₁ none (if b then cl else cr) o' ∧ BlockExit none o' out := by
    rcases exec_if_inv hx with h | ⟨hc, hab⟩
    · exact h
    · obtain ⟨w, -, hout⟩ := atomExpr_inv he hrA hc
      exact (abrupt_ne_ok hab hout).elim
  -- The condition is the atom read at `A`.
  obtain ⟨w, hvaw, hcw⟩ := atomExpr_inv he hrA hc
  obtain ⟨hls, hcv⟩ : ls₁ = ls ∧ some cv = some w := Out.ok.inj hcw
  have hT : Tm.Eval instr env (.op .truthy a) () (if b then .inl .unit else .inr .unit) () :=
    .op hva (by simp [instr, Prim.run, hb, hvaw, Option.some.inj hcv.symm])
  have hm : st.next ≤ s₁.next := dR_mono _ h₁
  cases b with
  | true =>
      obtain ⟨l', v, h⟩ := ihl (extend env .unit) _ st cl s₁ ls o' h₁ (varsOK_cons hv rfl)
        hwf.pushIf (by have := dR_mono _ h₂; omega) (by simpa [hls] using hs)
      exact ⟨l', v, .case_inl hT h⟩
  | false =>
      obtain ⟨l', v, h⟩ := ihr (extend env .unit) _ s₁ cr st' ls o' h₂ (varsOK_cons hv rfl)
        (hwf.pushIf.mono hm) hlen (by simpa [hls] using hs)
      exact ⟨l', v, .case_inr hT h⟩

/-- The decompiled form of a trapping-operator `case` whose second branch traps: a
fresh assignment of the operator, then the first branch. -/
private theorem dR_case_opT_inv {c : DCtx} {o : Op} {a : Tm Prim} {l r : Region Prim}
    {st st' : DState} {code : List Expr}
    (hd : dR c (.case (.op (.opT o) a) l r) st = some (code, st')) :
    ∃ e ty code', isTrapExit c r = true ∧ opExpr c.vars o a = some (e, ty) ∧
      dR { c with vars := .loc st.next ty :: c.vars } l ⟨st.next + 1, ty :: st.types⟩ =
        some (code', st') ∧ code = .localSet st.next e :: code' := by
  by_cases hT : isTrapExit c r = true
  · simp only [dR, hT, guard, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, -, ⟨e, ty⟩, hop, ⟨code', s₂⟩, hd, rfl, rfl⟩ := hd
    exact ⟨e, ty, code', hT, hop, hd, rfl⟩
  · simp [dR, hT] at hd

/-- A trap exit is a unit branch. -/
private theorem isTrapExit_br {c : DCtx} {r : Region Prim} (hT : isTrapExit c r = true) :
    ∃ l, r = .br l .unit := by
  cases r with
  | br l a => cases a <;> simp only [isTrapExit, Bool.false_eq_true] at hT; exact ⟨l, rfl⟩
  | _ => simp [isTrapExit] at hT

open Silmaril.Isotope.LambdaSSA.Semantics in
private theorem term_case_opT (o : Op) (a : Tm Prim) (l r : Region Prim) (ihl : Term l) :
    Term (.case (.op (.opT o) a) l r) := by
  intro env c st code st' ls out hd hv hwf hlen hseq
  obtain ⟨e, ty, code', hT, hop, hd', hcode⟩ := dR_case_opT_inv hd
  obtain ⟨A, hA⟩ := opExpr_static hop
  obtain ⟨va, hva, hrA⟩ := staticLoc_eval hv a hA
  obtain ⟨es, ws, he, hvaw, hargs⟩ := opExpr_exec hv hop hva
  have hseq' : Seq ls none (.localSet st.next (.op o es) :: code') out := he ▸ hcode ▸ hseq
  rcases localSet_op_inv hargs hseq' with ⟨w, hev, hs⟩ | htrap
  · obtain ⟨l', v, h⟩ := let₁_op_back ihl hd' hv hwf hlen hs
    exact ⟨l', v, .case_inl
      (.op hva (by simp [instr, Prim.run, decodeList_encodeList, hev, hvaw])) h⟩
  · obtain ⟨l', hr⟩ := isTrapExit_br hT
    rw [hr]
    exact ⟨l', .unit, .case_inr (va := .unit)
      (.op hva (by simp [instr, Prim.run, decodeList_encodeList, htrap, hvaw])) (.br .unit)⟩

private theorem term_case (t : Tm Prim) (l r : Region Prim) (ihl : Term l) (ihr : Term r) :
    Term (.case t l r) := by
  intro env c st code st' ls o hd
  rcases dR_case_inv hd with ⟨a, rfl⟩ | ⟨o', a, rfl⟩
  · exact term_case_truthy a l r ihl ihr env c st code st' ls o hd
  · exact term_case_opT o' a l r ihl env c st code st' ls o hd

/-- Only single-block CFGs decompile. -/
private theorem dR_cfg_one {c : DCtx} {e : Region Prim} {n : Nat} {bs : Fin n → Region Prim}
    {st : DState} {res : List Expr × DState} (hd : dR c (.cfg e n bs) st = some res) : n = 1 := by
  by_contra hn
  simp [dR, hn] at hd

/-- The decompiled form of a CFG whose entry branches to the block: a Wasm `block`
for the entry, then a `loop` for the block. -/
private theorem dR_cfg_loop_inv {c : DCtx} {e : Region Prim} {bs : Fin 1 → Region Prim}
    {st st' : DState} {code : List Expr} (hd : dR c (.cfg e 1 bs) st = some (code, st'))
    (hm : Region.mentionsLabel 0 e = true) :
    ∃ sh ce s₂ cb,
      dR { c with labels := .block c.wdepth (allocShape sh st).1 :: c.labels
                  wdepth := c.wdepth + 1 } e (allocShape sh st).2 = some (ce, s₂) ∧
      dR (loopCtx c (allocShape sh st).1) (bs ⟨0, Nat.one_pos⟩) s₂ = some (cb, st') ∧
      code = [.block none ce, .loop none cb] := by
  simp only [dR, hm, ↓reduceDIte, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨sh, -, ⟨ce, s₂⟩, h₂, ⟨cb, s₃⟩, h₃, rfl, rfl⟩ := hd
  exact ⟨sh, ce, s₂, cb, h₂, h₃, rfl⟩

/-- The decompiled form of a CFG whose entry never reaches the block: a Wasm `block`
for the entry, then `unreachable`. -/
private theorem dR_cfg_trap_inv {c : DCtx} {e : Region Prim} {bs : Fin 1 → Region Prim}
    {st st' : DState} {code : List Expr} (hd : dR c (.cfg e 1 bs) st = some (code, st'))
    (hm : ¬ Region.mentionsLabel 0 e = true) :
    ∃ ce, dR { c with labels := .trap :: c.labels, wdepth := c.wdepth + 1 } e st =
      some (ce, st') ∧ code = [.block none ce, .unreachable] := by
  simp only [dR, hm, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨⟨ce, s₁⟩, h₁, rfl, rfl⟩ := hd
  exact ⟨ce, h₁, rfl⟩

open Silmaril.Isotope.LambdaSSA.Semantics in
/-- A CFG whose entry may branch to the block terminates: either the entry exits, or
it branches into the loop, which terminates by `loop_term`. -/
private theorem term_cfg_loop (e : Region Prim) (bs : Fin 1 → Region Prim) (ihe : Term e)
    (ihb : Term (bs ⟨0, Nat.one_pos⟩)) {env : Env WVal} {c : DCtx} {st st' : DState}
    {code : List Expr} {ls : List WVal} {o : Out (Option WVal)}
    (hd : dR c (.cfg e 1 bs) st = some (code, st')) (hm : Region.mentionsLabel 0 e = true)
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : st'.next ≤ ls.length)
    (hseq : Seq ls none code o) : ∃ l v, Region.Eval instr env (.cfg e 1 bs) () l v () := by
  obtain ⟨sh, ce, s₂, cb, h₂, h₃, hcode⟩ := dR_cfg_loop_inv hd hm
  obtain ⟨hal, hL⟩ := allocShape_spec sh st
  have hm₃ : s₂.next ≤ st'.next := dR_mono _ h₃
  have hm₂ : (allocShape sh st).2.next ≤ s₂.next := dR_mono _ h₂
  have hwf' : WF { c with labels := .block c.wdepth (allocShape sh st).1 :: c.labels
                          wdepth := c.wdepth + 1 } (allocShape sh st).2.next :=
    (hwf.mono hal).push fun x hx => (hL x hx).2
  have hseq' : Seq ls none [.block none ce, .loop none cb] o := hcode ▸ hseq
  obtain ⟨oB, hB⟩ := seq_first hseq'
  obtain ⟨o₁, hce, hbx⟩ := exec_block_inv hB
  obtain ⟨first, init, he⟩ := ihe env _ _ _ _ ls o₁ h₂ hv hwf' (by omega) hce
  by_cases h0 : first = 0
  · show ∃ l v, Region.Eval instr env (.cfg e 1 bs) () l v ()
    -- The entry branches to the block: the Wasm block completes, and the loop runs.
    obtain ⟨ls₁, ho₁, hrd, hl₁, hfr₁⟩ :=
      sim_brk0 h₂ (h0 ▸ he) hv hwf' (by omega) List.getElem?_cons_zero rfl hce
    have hoB : oB = .ok ls₁ none := by
      have hbx' : BlockExit none (.brk 0 ls₁ none) oB := ho₁ ▸ hbx
      cases hbx'
      rfl
    obtain ⟨oL, hLp⟩ := seq_second hseq' (hoB ▸ hB)
    have hfr₁' : ∀ x, x < st.next → ls₁[x]? = ls[x]? := fun x hx =>
      hfr₁ x (by omega) (fun h => by have := (hL x h).1; omega)
    obtain ⟨l, v, hf⟩ := loop_term (bs := bs) (c := c) (L := (allocShape sh st).1)
      (base := st.next) h₃ ihb hwf
      (fun x hx => ⟨(hL x hx).1, by have := (hL x hx).2; omega⟩) (by omega)
      hLp rfl init hrd
      (varsOK_frame hv fun V hV x hx => hfr₁' x (hwf.vars V hV x hx)) (by omega)
    exact ⟨l, v, .cfg (h0 ▸ he) hf⟩
  · exact ⟨first - 1, init, .cfg he (.exit (by omega))⟩

open Silmaril.Isotope.LambdaSSA.Semantics in
/-- A CFG whose entry never reaches the block terminates when its entry does. -/
private theorem term_cfg_trap (e : Region Prim) (bs : Fin 1 → Region Prim) (ihe : Term e)
    {env : Env WVal} {c : DCtx} {st st' : DState} {code : List Expr} {ls : List WVal}
    {o : Out (Option WVal)}
    (hd : dR c (.cfg e 1 bs) st = some (code, st')) (hm : ¬ Region.mentionsLabel 0 e = true)
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : st'.next ≤ ls.length)
    (hseq : Seq ls none code o) : ∃ l v, Region.Eval instr env (.cfg e 1 bs) () l v () := by
  obtain ⟨ce, h₁, hcode⟩ := dR_cfg_trap_inv hd hm
  obtain ⟨oB, hB⟩ := seq_first (hcode ▸ hseq)
  obtain ⟨o₁, hce, -⟩ := exec_block_inv hB
  obtain ⟨first, init, he⟩ := ihe env _ _ _ _ ls o₁ h₁ hv hwf.pushTrap hlen hce
  have h0 : first ≠ 0 := fun h0 => hm (eval_mentions (h0 ▸ he))
  exact ⟨first - 1, init, .cfg he (.exit (by omega))⟩

private theorem term_cfg (e : Region Prim) (n : Nat) (bs : Fin n → Region Prim) (ihe : Term e)
    (ihb : ∀ i, Term (bs i)) : Term (.cfg e n bs) := by
  intro env c st code st' ls o hd hv hwf hlen hseq
  obtain rfl : n = 1 := dR_cfg_one hd
  by_cases hm : Region.mentionsLabel 0 e = true
  · exact term_cfg_loop e bs ihe (ihb _) hd hm hv hwf hlen hseq
  · exact term_cfg_trap e bs ihe hd hm hv hwf hlen hseq

/-- **The region terminates whenever its decompilation terminates.** -/
theorem term : ∀ r : Region Prim, Term r := by
  intro r
  induction r with
  | br l a => exact term_br l a
  | let₁ t r ih => exact term_let₁ t r ih
  | let₂ t r ih => exact term_let₂ t r ih
  | case t l r ihl ihr => exact term_case t l r ihl ihr
  | cfg e n bs ihe ihb => exact term_cfg e n bs ihe ihb

/-- The initial context is well formed below the parameters. -/
private theorem wf_initDCtx (f : SFunc) : WF (initDCtx f) f.params.length := by
  refine ⟨fun V hV x hx => ?_, fun w L hL => by simp [initDCtx] at hL⟩
  obtain ⟨j, hj, hjV⟩ : ∃ j, ∃ h : j < f.params.length, VLoc.loc j f.params[j] = V := by
    simpa only [initDCtx, List.mem_reverse, List.mem_mapIdx] using hV
  have hxj : x = j := by simpa [← hjV, VLoc.locs] using hx
  omega

/-- The function's exits decode to the call outcome of the code's outcome. -/
private theorem decodeOut_of_labelOut {res : Option IntType} {ls : List WVal} {base l : Nat}
    {v : SVal} {out : Out (Option WVal)} {o : FOut}
    (hlo : LabelOut [.ret, .trap] 1 res ls base l v out) (hexit : funcExit res out = some o) :
    decodeOut l v = some o := by
  match l, hlo with
  | 0, hlo =>
      have hret : (v = .unit ∧ out = .ret none) ∨
          ∃ w, v = .atom w ∧ out = .ret (some w) ∧ res.isSome := by
        simpa only [LabelOut, List.getElem?_cons_zero] using hlo
      rcases hret with ⟨hv, ho⟩ | ⟨w, hv, ho, hf⟩
      · rw [hv, ← hexit, ho]
        simp [decodeOut, funcExit, blockRes]
      · rw [hv, ← hexit, ho]
        simp [decodeOut, funcExit, blockRes, hf]
  | 1, hlo =>
      have htrap : out = .trap ∧ v = .unit := by
        simpa only [LabelOut, List.getElem?_cons_succ, List.getElem?_cons_zero] using hlo
      rw [htrap.2, ← hexit, htrap.1]
      rfl
  | k + 2, hlo => exact absurd hlo (by simp [LabelOut])

/-- **Out-of-SSA completeness**: terminating outcomes of the decompiled function are
outcomes of the SSA function. -/
theorem decompileFunc_complete {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g)
    {args : List WVal} {o : FOut} (h : g.Run args o) : f.Run args o := by
  obtain ⟨code, s, hdr, hs, hg⟩ := decompileFunc_spec hd
  obtain ⟨hty, out, hseq, hexit⟩ : FragFunc.Run
      ⟨f.params, s.types.reverse, f.result, code ++ [Expr.unreachable]⟩ args o := hg ▸ h
  have hty' : args.map WVal.type = f.params := hty
  have hl : args.length = f.params.length := by rw [← hty']; simp
  set ls := args ++ s.types.reverse.map WVal.zero
  have hwf : WF (initDCtx f) (⟨f.params.length, []⟩ : DState).next := wf_initDCtx f
  have hlen : s.next ≤ ls.length := by simp [ls, hl, hs]
  have hv : VarsOK ls (initDCtx f).vars (argEnv args) :=
    varsOK_initial (params := f.params) hl (s.types.reverse.map WVal.zero)
  -- The code before the final `unreachable` terminates, with an abrupt outcome or `out`.
  obtain ⟨o₀, hs₀, ho₀⟩ : ∃ o₀, Seq ls none code o₀ ∧ (o₀ = out ∨ ¬ o₀.Abrupt) := by
    rcases seq_append_inv hseq with ⟨h₁, -⟩ | ⟨ls₁, r₁, h₁, -⟩
    · exact ⟨_, h₁, .inl rfl⟩
    · exact ⟨_, h₁, .inr id⟩
  obtain ⟨l, v, hev⟩ := term f.body (argEnv args) (initDCtx f) _ code s ls o₀ hdr hv hwf hlen hs₀
  obtain ⟨o₁, hs₁, hlo⟩ := sim hev _ _ _ _ ls hdr hv hwf hlen
  have ho₁ : o₀ = o₁ := Silmaril.Wasm.SSA.Seq.det hs₀ hs₁
  have hout : o₁ = out := ho₁ ▸ ho₀.resolve_right fun hna => hna (ho₁ ▸ hlo.abrupt)
  exact ⟨hty', l, v, hev, decodeOut_of_labelOut hlo (hout ▸ hexit)⟩

end Silmaril.Proofs.Wasm.SSA.OutOfSSA
