module

public import Silmaril.Proofs.Wasm.SSA.OutOfSSA.Basic

/-!
# Out of SSA: the decompiled code simulates the region

By induction on lambda-SSA evaluation: if a region evaluates to an exit and its
decompilation succeeds, the decompiled body, run on locals in which every SSA
variable in scope reads its value (`VarsOK`), completes with the fragment
outcome of that exit (`LabelOut`). A `cfg` block is a Wasm `loop`; the
induction over CFG transfers (`Follow`) iterates it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.OutOfSSA

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.Wasm (IntType)

/-! ## Allocation is monotone -/

theorem allocShape_spec : ∀ (sh : Shape) (s : DState),
    s.next ≤ (allocShape sh s).2.next ∧
      ∀ x ∈ (allocShape sh s).1.locs, s.next ≤ x ∧ x < (allocShape sh s).2.next
  | .atom t, s => by simp [allocShape, DState.alloc, VLoc.locs]
  | .unit, s => by simp [allocShape, VLoc.locs]
  | .pair a b, s => by
      obtain ⟨ha, ha'⟩ := allocShape_spec a s
      obtain ⟨hb, hb'⟩ := allocShape_spec b (allocShape a s).2
      simp only [allocShape, VLoc.locs, List.mem_append]
      refine ⟨by omega, fun x hx => ?_⟩
      rcases hx with hx | hx
      · have := ha' x hx; omega
      · have := hb' x hx; omega

theorem copyCode_mono {L V : VLoc} {s s' : DState} {code : List Expr}
    (hc : copyCode L V s = some (code, s')) : s.next ≤ s'.next := by
  unfold copyCode at hc
  by_cases hsh : L.shape = V.shape
  swap
  · simp [hsh] at hc
  simp only [hsh, guard, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
  obtain ⟨_, -, xs, hxs, hc⟩ := hc
  by_cases hnd : xs.Nodup
  swap
  · simp [hnd] at hc
  simp only [hnd, ite_true] at hc
  obtain ⟨_, -, hc⟩ := hc
  split at hc
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, _, rfl⟩ := hc
    exact le_rfl
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, _, _, _, rfl⟩ := hc
    rw [(allocTmps_spec _ _).2]
    omega

/-! ## Inverting the decompiler -/

/-- The context of a `cfg` block (inside the Wasm `loop`). -/
def loopCtx (c : DCtx) (L : VLoc) : DCtx :=
  { vars := L :: c.vars, labels := .block c.wdepth L :: c.labels, wdepth := c.wdepth + 1,
    fty := c.fty }

section Inversion

variable {c : DCtx} {s s' : DState} {code : List Expr}

private theorem dR_br_none {l : Nat} {a : Tm Prim} (hl : c.labels[l]? = none)
    (hd : dR c (.br l a) s = some (code, s')) : False := by
  simp [dR, hl] at hd

/-- A branch to the trap exit is `unreachable`. -/
private theorem dR_br_trap {l : Nat} {a : Tm Prim} (hl : c.labels[l]? = some .trap)
    (hd : dR c (.br l a) s = some (code, s')) :
    a = .unit ∧ code = [.unreachable] ∧ s' = s := by
  simp only [dR, hl] at hd
  split at hd
  · simpa [eq_comm] using hd
  · simp at hd

/-- A branch to the return exit returns the located argument, if any. -/
private theorem dR_br_ret {l : Nat} {a : Tm Prim} (hl : c.labels[l]? = some .ret)
    (hd : dR c (.br l a) s = some (code, s')) :
    s' = s ∧ ∃ V, staticLoc c.vars a = some V ∧
      (V = .unit ∧ code = [.return_ []] ∨
        c.fty.isSome = true ∧ ∃ e, V.atomExpr = some e ∧ code = [.return_ [e]]) := by
  simp only [dR, hl, Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
  obtain ⟨V, hV, hd⟩ := hd
  split at hd
  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
    exact ⟨hd.2.symm, _, hV, .inl ⟨rfl, hd.1.symm⟩⟩
  · simp only [guard, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hd
    obtain ⟨_, hf, e, he, hcode, hs⟩ := hd
    split at hf
    · exact ⟨hs.symm, V, hV, .inr ⟨by assumption, e, he, hcode.symm⟩⟩
    · cases hf

/-- A branch to a block copies the argument into the block's layout and branches. -/
private theorem dR_br_block {l w : Nat} {L : VLoc} {a : Tm Prim}
    (hl : c.labels[l]? = some (.block w L)) (hd : dR c (.br l a) s = some (code, s')) :
    ∃ V cc, staticLoc c.vars a = some V ∧ copyCode L V s = some (cc, s') ∧
      code = cc ++ [.br (c.wdepth - 1 - w) []] := by
  simp only [dR, hl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨V, hV, ⟨cc, s''⟩, hcc, hcode, hs⟩ := hd
  exact ⟨V, cc, hV, hs ▸ hcc, hcode.symm⟩

/-- A static binding generates no code. -/
private theorem dR_let₁_static {t : Tm Prim} {r : Region Prim} {V : VLoc}
    (hV : staticLoc c.vars t = some V) :
    dR c (.let₁ t r) s = dR { c with vars := V :: c.vars } r s := by
  simp only [dR, hV]

/-- A non-static binding is an operator, assigned to a fresh local. -/
private theorem dR_let₁_op {t : Tm Prim} {r : Region Prim} (hV : staticLoc c.vars t = none)
    (hd : dR c (.let₁ t r) s = some (code, s')) :
    ∃ o a e ty code', t = .op (.op o) a ∧ opExpr c.vars o a = some (e, ty) ∧
      dR { c with vars := .loc s.next ty :: c.vars } r ⟨s.next + 1, ty :: s.types⟩ =
        some (code', s') ∧
      code = .localSet s.next e :: code' := by
  simp only [dR, hV] at hd
  split at hd
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, -, ⟨e, ty⟩, hop, ⟨code', s₂⟩, hd, hcode, hs⟩ := hd
    exact ⟨_, _, e, ty, code', rfl, hop, hs ▸ hd, hcode.symm⟩
  · simp at hd

/-- A pair destructuring generates no code. -/
private theorem dR_let₂ {t : Tm Prim} {r : Region Prim}
    (hd : dR c (.let₂ t r) s = some (code, s')) :
    ∃ A B, staticLoc c.vars t = some (.pair A B) ∧
      dR { c with vars := B :: A :: c.vars } r s = some (code, s') := by
  simp only [dR] at hd
  split at hd
  · exact ⟨_, _, by assumption, hd⟩
  · simp at hd

/-- A case is a Wasm `if` on a truth value, or an operator whose trap goes to the
right-hand branch, a jump to the trap exit. -/
private theorem dR_case {t : Tm Prim} {l r : Region Prim}
    (hd : dR c (.case t l r) s = some (code, s')) :
    (∃ a A e cl s₁ cr, t = .op .truthy a ∧ staticLoc c.vars a = some A ∧
      A.atomExpr = some e ∧
      dR { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 } l s = some (cl, s₁) ∧
      dR { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 } r s₁ = some (cr, s') ∧
      code = [.if_ none e cl cr]) ∨
    (∃ o a e ty code', t = .op (.opT o) a ∧ isTrapExit c r = true ∧
      opExpr c.vars o a = some (e, ty) ∧
      dR { c with vars := .loc s.next ty :: c.vars } l ⟨s.next + 1, ty :: s.types⟩ =
        some (code', s') ∧
      code = .localSet s.next e :: code') := by
  simp only [dR] at hd
  split at hd
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨A, hA, e, he, ⟨cl, s₁⟩, h₁, ⟨cr, s₂⟩, h₂, hcode, hs⟩ := hd
    exact .inl ⟨_, A, e, cl, s₁, cr, rfl, hA, he, h₁, hs ▸ h₂, hcode.symm⟩
  · simp only [guard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨_, hT, ⟨e, ty⟩, hop, ⟨code', s₂⟩, hd, hcode, hs⟩ := hd
    split at hT
    · exact .inr ⟨_, _, e, ty, code', rfl, by assumption, hop, hs ▸ hd, hcode.symm⟩
    · cases hT
  · simp at hd

/-- A one-block `cfg` is a Wasm `block` around the entry, followed by a `loop` for
the block when the entry can jump to it, and by `unreachable` otherwise. -/
private theorem dR_cfg {e : Region Prim} {n : Nat} {bs : Fin n → Region Prim}
    (hd : dR c (.cfg e n bs) s = some (code, s')) :
    ∃ hn : n = 1,
      (∃ sh ce s₂ cb, Region.mentionsLabel 0 e = true ∧
        dR { c with labels := .block c.wdepth (allocShape sh s).1 :: c.labels,
                    wdepth := c.wdepth + 1 } e (allocShape sh s).2 = some (ce, s₂) ∧
        dR (loopCtx c (allocShape sh s).1) (bs ⟨0, by omega⟩) s₂ = some (cb, s') ∧
        code = [.block none ce, .loop none cb]) ∨
      (∃ ce, Region.mentionsLabel 0 e = false ∧
        dR { c with labels := .trap :: c.labels, wdepth := c.wdepth + 1 } e s = some (ce, s') ∧
        code = [.block none ce, .unreachable]) := by
  simp only [dR] at hd
  split at hd
  · rename_i hn
    refine ⟨hn, ?_⟩
    split at hd
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨sh, -, ⟨ce, s₂⟩, h₂, ⟨cb, s₃⟩, h₃, hcode, hs⟩ := hd
      exact .inl ⟨sh, ce, s₂, cb, by assumption, h₂, hs ▸ h₃, hcode.symm⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨⟨ce, s₁⟩, h₁, hcode, hs⟩ := hd
      exact .inr ⟨ce, by simpa using (by assumption : ¬Region.mentionsLabel 0 e = true),
        hs ▸ h₁, hcode.symm⟩
  · simp at hd

end Inversion

theorem dR_mono : ∀ (r : Region Prim) {c : DCtx} {s s' : DState} {code : List Expr},
    dR c r s = some (code, s') → s.next ≤ s'.next := by
  intro r
  induction r with
  | br l a =>
      intro c s s' code hd
      rcases hl : c.labels[l]? with _ | (_ | _ | ⟨w, L⟩)
      · exact (dR_br_none hl hd).elim
      · exact le_of_eq (congrArg DState.next (dR_br_trap hl hd).2.2).symm
      · exact le_of_eq (congrArg DState.next (dR_br_ret hl hd).1).symm
      · obtain ⟨V, cc, -, hcc, -⟩ := dR_br_block hl hd
        exact copyCode_mono hcc
  | let₁ t r ih =>
      intro c s s' code hd
      cases hV : staticLoc c.vars t with
      | some V => exact ih ((dR_let₁_static hV).symm.trans hd)
      | none =>
          obtain ⟨o, a, e, ty, code', -, -, hd', -⟩ := dR_let₁_op hV hd
          have h : s.next + 1 ≤ s'.next := ih hd'
          omega
  | let₂ t r ih =>
      intro c s s' code hd
      obtain ⟨A, B, -, hd'⟩ := dR_let₂ hd
      exact ih hd'
  | case t l r ihl ihr =>
      intro c s s' code hd
      rcases dR_case hd with ⟨a, A, e, cl, s₁, cr, -, -, -, h₁, h₂, -⟩ |
        ⟨o, a, e, ty, code', -, -, -, hd', -⟩
      · exact (ihl h₁).trans (ihr h₂)
      · have h : s.next + 1 ≤ s'.next := ihl hd'
        omega
  | cfg e n bs ihe ihb =>
      intro c s s' code hd
      obtain ⟨hn, ⟨sh, ce, s₂, cb, -, h₂, h₃, -⟩ | ⟨ce, -, h₁, -⟩⟩ := dR_cfg hd
      · exact ((allocShape_spec sh s).1.trans (ihe h₂)).trans (ihb _ h₃)
      · exact ihe h₁

/-! ## Invariants -/

/-- Allocation bounds of a context: locations in scope lie below `n`, and Wasm
label levels are in range. -/
structure WF (c : DCtx) (n : Nat) : Prop where
  vars : ∀ V ∈ c.vars, ∀ x ∈ V.locs, x < n
  labels : ∀ w L, DLabel.block w L ∈ c.labels → w < c.wdepth ∧ ∀ x ∈ L.locs, x < n

theorem WF.mono {c : DCtx} {n m : Nat} (h : WF c n) (hnm : n ≤ m) : WF c m :=
  ⟨fun V hV x hx => by have := h.vars V hV x hx; omega,
   fun w L hL => ⟨(h.labels w L hL).1, fun x hx => by have := (h.labels w L hL).2 x hx; omega⟩⟩

/-- The fragment outcome of the SSA exit `ℓ` with value `v`, for code started on
the locals `ls` with allocation base `base`. -/
def LabelOut (labels : List DLabel) (wdepth : Nat) (fty : Option IntType) (ls : List WVal)
    (base ℓ : Nat) (v : SVal) (o : Out (Option WVal)) : Prop :=
  match labels[ℓ]? with
  | some .trap => o = .trap ∧ v = .unit
  | some .ret => (v = .unit ∧ o = .ret none) ∨ ∃ w, v = .atom w ∧ o = .ret (some w) ∧ fty.isSome
  | some (.block w L) => ∃ ls', o = .brk (wdepth - 1 - w) ls' none ∧ readL ls' L = some v ∧
      ls'.length = ls.length ∧ ∀ x, x < base → x ∉ L.locs → ls'[x]? = ls[x]?
  | none => False

variable {labels : List DLabel} {wd : Nat} {fty : Option IntType} {ls : List WVal}
  {base ℓ : Nat} {v : SVal} {o : Out (Option WVal)}

theorem LabelOut.abrupt (h : LabelOut labels wd fty ls base ℓ v o) : o.Abrupt := by
  unfold LabelOut at h
  split at h
  · rw [h.1]; trivial
  · rcases h with ⟨-, rfl⟩ | ⟨w, -, rfl, -⟩ <;> trivial
  · obtain ⟨ls', rfl, -⟩ := h; trivial
  · exact h.elim

theorem LabelOut.mono {base' : Nat} (h : LabelOut labels wd fty ls base ℓ v o) (hb : base' ≤ base) :
    LabelOut labels wd fty ls base' ℓ v o := by
  unfold LabelOut at h ⊢
  split at h
  · simp [*]
  · simp [*]
  · obtain ⟨ls', h1, h2, h3, h4⟩ := h
    exact ⟨ls', h1, h2, h3, fun x hx => h4 x (by omega)⟩
  · simp_all

theorem LabelOut.trans {ls₀ : List WVal} (h : LabelOut labels wd fty ls base ℓ v o)
    (hl : ls.length = ls₀.length) (hf : ∀ x, x < base → ls[x]? = ls₀[x]?) :
    LabelOut labels wd fty ls₀ base ℓ v o := by
  unfold LabelOut at h ⊢
  split at h
  · simp [*]
  · simp [*]
  · obtain ⟨ls', h1, h2, h3, h4⟩ := h
    exact ⟨ls', h1, h2, h3.trans hl, fun x hx hxL => (h4 x hx hxL).trans (hf x hx)⟩
  · simp_all

theorem LabelOut.succ {X : DLabel} :
    LabelOut (X :: labels) wd fty ls base (ℓ + 1) v o ↔ LabelOut labels wd fty ls base ℓ v o := by
  simp [LabelOut]

theorem LabelOut.blockExit (h : LabelOut labels (wd + 1) fty ls base ℓ v o)
    (hw : ∀ w L, DLabel.block w L ∈ labels → w < wd) :
    ∃ o', BlockExit none o o' ∧ LabelOut labels wd fty ls base ℓ v o' := by
  unfold LabelOut at h ⊢
  split at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨.trap, .trap, by simp [*]⟩
  · rename_i heq
    rcases h with ⟨h1, rfl⟩ | ⟨w, h1, rfl, h2⟩
    · exact ⟨_, .ret, by simp [h1]⟩
    · exact ⟨_, .ret, by simp [h1, h2]⟩
  · rename_i w L heq
    obtain ⟨ls', rfl, h2, h3, h4⟩ := h
    have := hw w L (List.mem_of_getElem? heq)
    have e : wd + 1 - 1 - w = (wd - 1 - w) + 1 := by omega
    rw [e]
    exact ⟨_, .brk, ⟨ls', rfl, h2, h3, h4⟩⟩
  · exact h.elim

theorem LabelOut.loopExit (h : LabelOut labels (wd + 1) fty ls base ℓ v o)
    (hw : ∀ w L, DLabel.block w L ∈ labels → w < wd) :
    ∃ o', LoopExit none o o' ∧ LabelOut labels wd fty ls base ℓ v o' := by
  unfold LabelOut at h ⊢
  split at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨.trap, .trap, by simp [*]⟩
  · rename_i heq
    rcases h with ⟨h1, rfl⟩ | ⟨w, h1, rfl, h2⟩
    · exact ⟨_, .ret, by simp [h1]⟩
    · exact ⟨_, .ret, by simp [h1, h2]⟩
  · rename_i w L heq
    obtain ⟨ls', rfl, h2, h3, h4⟩ := h
    have := hw w L (List.mem_of_getElem? heq)
    have e : wd + 1 - 1 - w = (wd - 1 - w) + 1 := by omega
    rw [e]
    exact ⟨_, .brk, ⟨ls', rfl, h2, h3, h4⟩⟩
  · exact h.elim

/-! ## The simulation -/

theorem WF.push {c : DCtx} {n : Nat} (h : WF c n) {L : VLoc} (hL : ∀ x ∈ L.locs, x < n) :
    WF { c with labels := .block c.wdepth L :: c.labels, wdepth := c.wdepth + 1 } n := by
  refine ⟨h.vars, fun w L' hL' => ?_⟩
  rcases List.mem_cons.1 hL' with he | hL'
  · cases he; exact ⟨by simp, hL⟩
  · exact ⟨by have := (h.labels w L' hL').1; simp; omega, (h.labels w L' hL').2⟩

theorem WF.pushTrap {c : DCtx} {n : Nat} (h : WF c n) :
    WF { c with labels := .trap :: c.labels, wdepth := c.wdepth + 1 } n := by
  refine ⟨h.vars, fun w L' hL' => ?_⟩
  rcases List.mem_cons.1 hL' with he | hL'
  · cases he
  · exact ⟨by have := (h.labels w L' hL').1; simp; omega, (h.labels w L' hL').2⟩

theorem WF.loop {c : DCtx} {n : Nat} (h : WF c n) {L : VLoc} (hL : ∀ x ∈ L.locs, x < n) :
    WF (loopCtx c L) n := by
  refine ⟨fun V hV x hx => ?_, (h.push hL).labels⟩
  rcases List.mem_cons.1 hV with rfl | hV
  · exact hL x hx
  · exact h.vars V hV x hx

/-- One fresh assignment followed by a simulated rest. -/
theorem let₁_op_step {env : Env WVal} {c : DCtx} {st s₂ : DState} {ty : IntType}
    {code' : List Expr} {ls : List WVal} {e : Expr} {w : WVal} {r : Region Prim} {l : Nat}
    {v : SVal}
    (ih : ∀ (c : DCtx) (st : DState) (code : List Expr) (st' : DState) (ls : List WVal),
      dR c r st = some (code, st') → VarsOK ls c.vars (extend env (.atom w)) → WF c st.next →
      st'.next ≤ ls.length →
      ∃ o, Seq ls none code o ∧ LabelOut c.labels c.wdepth c.fty ls st.next l v o)
    (hd : dR { c with vars := .loc st.next ty :: c.vars } r ⟨st.next + 1, ty :: st.types⟩ =
      some (code', s₂))
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : s₂.next ≤ ls.length)
    (hex : Exec ls e (.ok ls (some w))) :
    ∃ o, Seq ls none (.localSet st.next e :: code') o ∧
      LabelOut c.labels c.wdepth c.fty ls st.next l v o := by
  have hm := dR_mono r hd
  simp only at hm
  have hx : st.next < ls.length := by omega
  have hfr : ∀ x, x < st.next → (ls.set st.next w)[x]? = ls[x]? :=
    fun x hx' => getElem?_set_ne' (by omega)
  obtain ⟨o, hseq, hlo⟩ := ih _ _ _ _ (ls.set st.next w) hd
    (varsOK_cons (varsOK_frame hv fun V hV x hxV => hfr x (hwf.vars V hV x hxV))
      (by simp [readL, hx]))
    ⟨fun W hW x hxW => by
      rcases List.mem_cons.1 hW with rfl | hW
      · simp [VLoc.locs] at hxW; simp; omega
      · have := hwf.vars W hW x hxW; simp; omega,
     fun w L hL => ⟨(hwf.labels w L hL).1, fun x hxL => by
      have := (hwf.labels w L hL).2 x hxL; simp; omega⟩⟩
    (by rw [List.length_set]; exact hlen)
  exact ⟨o, .cons (.localSet hex) hseq,
    (hlo.mono (by simp)).trans (List.length_set ..) hfr⟩


/-! ### Evaluating decompiled terms -/

section Terms

open Silmaril.Isotope.LambdaSSA.Semantics

variable {env : Env WVal} {ls : List WVal} {vars : List VLoc}

/-- A decompiled operator computes the operator's value. -/
private theorem op_exec (hv : VarsOK ls vars env) {o : Op} {a : Tm Prim} {e : Expr}
    {ty : IntType} (hop : opExpr vars o a = some (e, ty)) {v : SVal}
    (ht : Tm.Eval instr env (.op (.op o) a) () v ()) :
    ∃ w, v = .atom w ∧ Exec ls e (.ok ls (some w)) := by
  cases ht with
  | op ha step =>
    obtain ⟨es, ws, rfl, rfl, hargs⟩ := opExpr_exec hv hop ha
    simp only [instr, Prim.run, decodeList_encodeList, Option.bind_some] at step
    split at step
    · rename_i w hev
      exact ⟨w, (Option.some.inj step).symm, .op hargs hev⟩
    · simp at step

/-- A decompiled trapping operator computes the operator's value or traps. -/
private theorem opT_exec (hv : VarsOK ls vars env) {o : Op} {a : Tm Prim} {e : Expr}
    {ty : IntType} (hop : opExpr vars o a = some (e, ty)) {v : SVal}
    (ht : Tm.Eval instr env (.op (.opT o) a) () v ()) :
    (∃ w, v = .inl (.atom w) ∧ Exec ls e (.ok ls (some w))) ∨
      (v = .inr .unit ∧ Exec ls e .trap) := by
  cases ht with
  | op ha step =>
    obtain ⟨es, ws, rfl, rfl, hargs⟩ := opExpr_exec hv hop ha
    simp only [instr, Prim.run, decodeList_encodeList, Option.bind_some] at step
    split at step
    · rename_i w hev
      exact .inl ⟨w, (Option.some.inj step).symm, .op hargs hev⟩
    · rename_i hev
      exact .inr ⟨(Option.some.inj step).symm, .op_trap hargs hev⟩
    · simp at step

/-- A decompiled truth test reads the tested value. -/
private theorem truthy_exec (hv : VarsOK ls vars env) {a : Tm Prim} {A : VLoc} {e : Expr}
    (hA : staticLoc vars a = some A) (he : A.atomExpr = some e) {v : SVal}
    (ht : Tm.Eval instr env (.op .truthy a) () v ()) :
    ∃ w b, Exec ls e (.ok ls (some w)) ∧ w.truthy = some b ∧
      v = if b then .inl .unit else .inr .unit := by
  cases ht with
  | op ha step =>
    obtain ⟨w, hw, hex⟩ := atomExpr_exec he (staticLoc_sound hv ha hA)
    have hrun : w.truthy.map (fun b => if b then (.inl .unit : SVal) else .inr .unit) = some v := by
      simpa only [instr, hw, Prim.run] using step
    obtain ⟨b, hb, hbv⟩ := Option.map_eq_some_iff.1 hrun
    exact ⟨w, b, hex, hb, hbv.symm⟩

/-- A jump to the trap exit evaluates to the trap label with no value. -/
private theorem isTrapExit_eval {c : DCtx} {r : Region Prim} (hT : isTrapExit c r = true)
    {l : Nat} {v : SVal} (hr : Region.Eval instr env r () l v ()) :
    c.labels[l]? = some .trap ∧ v = .unit := by
  cases r with
  | br l' a =>
      cases a <;> simp only [isTrapExit, beq_iff_eq, Bool.false_eq_true] at hT
      cases hr with
      | br hu => cases hu; exact ⟨hT, rfl⟩
  | _ => simp [isTrapExit] at hT

/-- With a single block, a transfer to a label other than the block leaves the
`cfg` with the transferred value. -/
private theorem follow_exit {n : Nat} {blocks : Fin n → Region Prim} {first l : Nat}
    {init v : SVal} (hf : Region.Follow instr env blocks first init () l v ()) (hn : n = 1)
    (h0 : first ≠ 0) : first = l + 1 ∧ v = init := by
  cases hf with
  | exit outside => exact ⟨by omega, rfl⟩
  | step inside _ _ => omega

end Terms

/-! ### Well-formed contexts -/

private theorem WF.cons {c : DCtx} {n : Nat} (h : WF c n) {V : VLoc}
    (hV : ∀ x ∈ V.locs, x < n) : WF { c with vars := V :: c.vars } n :=
  ⟨fun W hW x hx => (List.mem_cons.1 hW).elim (fun e => hV x (e ▸ hx)) (h.vars W · x hx),
    h.labels⟩

private theorem WF.deeper {c : DCtx} {n : Nat} (h : WF c n) :
    WF { c with wdepth := c.wdepth + 1 } n :=
  ⟨h.vars, fun w L hL => ⟨Nat.lt_succ_of_lt (h.labels w L hL).1, (h.labels w L hL).2⟩⟩

/-- An exit to the block label just pushed is a branch to it. -/
private theorem LabelOut.head_block {labels : List DLabel} {wd : Nat} {L : VLoc}
    {fty : Option IntType} {ls : List WVal} {base : Nat} {v : SVal} {o : Out (Option WVal)}
    (h : LabelOut (.block wd L :: labels) (wd + 1) fty ls base 0 v o) :
    ∃ ls', o = .brk 0 ls' none ∧ readL ls' L = some v ∧ ls'.length = ls.length ∧
      ∀ x, x < base → x ∉ L.locs → ls'[x]? = ls[x]? := by
  have e : wd + 1 - 1 - wd = 0 := by omega
  simpa only [LabelOut, List.getElem?_cons_zero, e] using h

/-! ### The cases of the simulation -/

section Cases

open Silmaril.Isotope.LambdaSSA.Semantics

/-- The simulation claim for a region evaluated in `env` to exit `l` with value `v`. -/
private def SimR (env : Env WVal) (r : Region Prim) (l : Nat) (v : SVal) : Prop :=
  ∀ (c : DCtx) (st : DState) (code : List Expr) (st' : DState) (ls : List WVal),
    dR c r st = some (code, st') → VarsOK ls c.vars env → WF c st.next →
    st'.next ≤ ls.length →
    ∃ o, Seq ls none code o ∧ LabelOut c.labels c.wdepth c.fty ls st.next l v o

/-- The simulation claim for the transfers of a one-block `cfg`, entered at the
block with `init`: the Wasm `loop` simulates them. -/
private def SimF (env : Env WVal) {n : Nat} (blocks : Fin n → Region Prim) (first : Nat)
    (init : SVal) (out : Nat) (v : SVal) : Prop :=
  ∀ (c : DCtx) (L : VLoc) (st₂ st₃ : DState) (cb : List Expr) (ls : List WVal) (base : Nat),
    n = 1 → first = 0 →
    (∀ h0 : 0 < n, dR (loopCtx c L) (blocks ⟨0, h0⟩) st₂ = some (cb, st₃)) →
    readL ls L = some init → VarsOK ls c.vars env → WF c base →
    (∀ x ∈ L.locs, base ≤ x ∧ x < st₂.next) → base ≤ st₂.next → st₃.next ≤ ls.length →
    ∃ o, Exec ls (.loop none cb) o ∧ LabelOut c.labels c.wdepth c.fty ls base out v o

variable {env : Env WVal}

private theorem sim_br {l : Nat} {a : Tm Prim} {v : SVal}
    (harg : Tm.Eval instr env a () v ()) : SimR env (.br l a) l v := by
  intro c st code st' ls hd hv hwf hlen
  rcases hl : c.labels[l]? with _ | (_ | _ | ⟨w, L⟩)
  · exact (dR_br_none hl hd).elim
  · obtain ⟨ha, hcode, -⟩ := dR_br_trap hl hd
    have hvu : v = .unit := by cases ha; cases harg; rfl
    rw [hcode]
    exact ⟨.trap, .abrupt .unreachable trivial, by simp [LabelOut, hl, hvu]⟩
  · obtain ⟨-, V, hV, ⟨hVu, hcode⟩ | ⟨hf, e, he, hcode⟩⟩ := dR_br_ret hl hd
    · have hvu : v = .unit := by simpa [readL, hVu, eq_comm] using staticLoc_sound hv harg hV
      rw [hcode]
      exact ⟨.ret none, .abrupt (.return_ .nil) trivial, by simp [LabelOut, hl, hvu]⟩
    · obtain ⟨w, hvw, hex⟩ := atomExpr_exec he (staticLoc_sound hv harg hV)
      rw [hcode]
      exact ⟨.ret (some w), .abrupt (.return_ (.cons hex .nil)) trivial,
        by simp [LabelOut, hl, hf, hvw]⟩
  · obtain ⟨V, cc, hV, hcc, hcode⟩ := dR_br_block hl hd
    have hLb : ∀ x ∈ L.locs, x < st.next := (hwf.labels w L (List.mem_of_getElem? hl)).2
    obtain ⟨-, ls', r', hseq, hrd, hl', hfr⟩ :=
      copy_exec hcc (staticLoc_sound hv harg hV) (staticLoc_below hwf.vars _ hV) hLb hlen none
    rw [hcode]
    exact ⟨_, seq_append hseq (.abrupt (.br .nil) trivial),
      by simp only [LabelOut, hl]; exact ⟨ls', rfl, hrd, hl', hfr⟩⟩

private theorem sim_let₁ {t : Tm Prim} {r : Region Prim} {va v : SVal} {l : Nat}
    (ht : Tm.Eval instr env t () va ()) (ih : SimR (extend env va) r l v) :
    SimR env (.let₁ t r) l v := by
  intro c st code st' ls hd hv hwf hlen
  cases hV : staticLoc c.vars t with
  | some V =>
      exact ih { c with vars := V :: c.vars } st code st' ls ((dR_let₁_static hV).symm.trans hd)
        (varsOK_cons hv (staticLoc_sound hv ht hV)) (hwf.cons (staticLoc_below hwf.vars _ hV))
        hlen
  | none =>
      obtain ⟨o, a, e, ty, code', hto, hop, hd', hcode⟩ := dR_let₁_op hV hd
      obtain ⟨w, hvw, hex⟩ := op_exec hv hop (hto ▸ ht)
      rw [hcode]
      exact let₁_op_step (hvw ▸ ih) hd' hv hwf hlen hex

private theorem sim_let₂ {t : Tm Prim} {r : Region Prim} {va vb v : SVal} {l : Nat}
    (ht : Tm.Eval instr env t () (.pair va vb) ()) (ih : SimR (extend (extend env va) vb) r l v) :
    SimR env (.let₂ t r) l v := by
  intro c st code st' ls hd hv hwf hlen
  obtain ⟨A, B, hAB, hd'⟩ := dR_let₂ hd
  obtain ⟨va', vb', hA, hB, he⟩ := readL_pair.1 (staticLoc_sound hv ht hAB)
  have hva : va = va' ∧ vb = vb' := by simpa using he
  have hbA : ∀ x ∈ (VLoc.pair A B).locs, x < st.next := staticLoc_below hwf.vars _ hAB
  have hwf' : WF { c with vars := B :: A :: c.vars } st.next :=
    (hwf.cons fun x hx => hbA x (by simp [VLoc.locs, hx])).cons
      fun x hx => hbA x (by simp [VLoc.locs, hx])
  exact ih { c with vars := B :: A :: c.vars } st code st' ls hd' (varsOK_cons (varsOK_cons hv (hva.1 ▸ hA)) (hva.2 ▸ hB))
    hwf' hlen

private theorem sim_case_inl {t : Tm Prim} {rl rr : Region Prim} {va v : SVal} {l : Nat}
    (ht : Tm.Eval instr env t () (.inl va) ()) (ih : SimR (extend env va) rl l v) :
    SimR env (.case t rl rr) l v := by
  intro c st code st' ls hd hv hwf hlen
  rcases dR_case hd with ⟨a, A, e, cl, s₁, cr, hta, hA, he, h₁, h₂, hcode⟩ |
    ⟨o, a, e, ty, code', hto, -, hop, hd', hcode⟩
  · show ∃ o, Seq ls none code o ∧ LabelOut c.labels c.wdepth c.fty ls st.next l v o
    obtain ⟨w, b, hex, hb, hbv⟩ := truthy_exec hv hA he (hta ▸ ht)
    have hbt : b = true ∧ va = .unit := by cases b <;> simp_all [eq_comm]
    obtain ⟨o, hseq, hlo⟩ := ih _ st cl s₁ ls h₁ (varsOK_cons hv (hbt.2 ▸ rfl))
      (hwf.deeper.cons (by simp [VLoc.locs])) ((dR_mono _ h₂).trans hlen)
    obtain ⟨o', hbe, hlo'⟩ := hlo.blockExit (fun w L hL => (hwf.labels w L hL).1)
    rw [hcode]
    exact ⟨o', .abrupt (.if_ (b := true) hex (hbt.1 ▸ hb) hseq hbe) hlo'.abrupt, hlo'⟩
  · rcases opT_exec hv hop (hto ▸ ht) with ⟨w, hvw, hex⟩ | ⟨hvt, -⟩
    · rw [hcode]
      exact let₁_op_step (Value.inl.inj hvw ▸ ih) hd' hv hwf hlen hex
    · exact absurd hvt (by simp)

private theorem sim_case_inr {t : Tm Prim} {rl rr : Region Prim} {va v : SVal} {l : Nat}
    (ht : Tm.Eval instr env t () (.inr va) ()) (hr : Region.Eval instr (extend env va) rr () l v ())
    (ih : SimR (extend env va) rr l v) :
    SimR env (.case t rl rr) l v := by
  intro c st code st' ls hd hv hwf hlen
  rcases dR_case hd with ⟨a, A, e, cl, s₁, cr, hta, hA, he, h₁, h₂, hcode⟩ |
    ⟨o, a, e, ty, code', hto, hT, hop, -, hcode⟩
  · show ∃ o, Seq ls none code o ∧ LabelOut c.labels c.wdepth c.fty ls st.next l v o
    obtain ⟨w, b, hex, hb, hbv⟩ := truthy_exec hv hA he (hta ▸ ht)
    have hbf : b = false ∧ va = .unit := by cases b <;> simp_all [eq_comm]
    have hm : st.next ≤ s₁.next := dR_mono _ h₁
    obtain ⟨o, hseq, hlo⟩ := ih _ s₁ cr st' ls h₂ (varsOK_cons hv (hbf.2 ▸ rfl))
      ((hwf.mono hm).deeper.cons (by simp [VLoc.locs])) hlen
    obtain ⟨o', hbe, hlo'⟩ := (hlo.mono hm).blockExit (fun w L hL => (hwf.labels w L hL).1)
    rw [hcode]
    exact ⟨o', .abrupt (.if_ (b := false) hex (hbf.1 ▸ hb) hseq hbe) hlo'.abrupt, hlo'⟩
  · rcases opT_exec hv hop (hto ▸ ht) with ⟨w, hvw, -⟩ | ⟨-, hex⟩
    · exact absurd hvw (by simp)
    · obtain ⟨hl, hvu⟩ := isTrapExit_eval hT hr
      rw [hcode]
      exact ⟨.trap, .abrupt (.localSet_abrupt hex trivial) trivial, by simp [LabelOut, hl, hvu]⟩

/-- A `cfg` whose entry can jump to its block: the entry runs in a Wasm `block`,
then the block runs as a Wasm `loop`. -/
private theorem sim_cfg_loop {entry : Region Prim} {n : Nat} {blocks : Fin n → Region Prim}
    {initial v : SVal} {first l : Nat}
    (hf : Region.Follow instr env blocks first initial () l v ())
    (ihe : SimR env entry first initial) (ihf : SimF env blocks first initial l v)
    (hn : n = 1) {c : DCtx} {L : VLoc} {st s₁ s₂ st' : DState} {ce cb : List Expr}
    {ls : List WVal} (hal : st.next ≤ s₁.next) (hL : ∀ x ∈ L.locs, st.next ≤ x ∧ x < s₁.next)
    (h₂ : dR { c with labels := .block c.wdepth L :: c.labels, wdepth := c.wdepth + 1 } entry s₁ =
      some (ce, s₂))
    (h₃ : dR (loopCtx c L) (blocks ⟨0, by omega⟩) s₂ = some (cb, st'))
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : st'.next ≤ ls.length) :
    ∃ o, Seq ls none [.block none ce, .loop none cb] o ∧
      LabelOut c.labels c.wdepth c.fty ls st.next l v o := by
  have hm₂ : s₁.next ≤ s₂.next := dR_mono _ h₂
  have hm₃ : s₂.next ≤ st'.next := dR_mono _ h₃
  obtain ⟨o, hseq, hlo⟩ := ihe _ _ _ _ ls h₂ hv
    ((hwf.mono hal).push fun x hx => (hL x hx).2) (by omega)
  by_cases h0 : first = 0
  · obtain ⟨ls₁, ho, hrd, hl₁, hfr₁⟩ := LabelOut.head_block (by simpa only [h0] using hlo)
    have hfr₁' : ∀ x, x < st.next → ls₁[x]? = ls[x]? := fun x hx =>
      hfr₁ x (by omega) (fun h => by have := (hL x h).1; omega)
    obtain ⟨o', hloop, hlo'⟩ := ihf c _ s₂ st' cb ls₁ st.next hn h0 (fun _ => h₃) hrd
      (varsOK_frame hv fun V hV x hx => hfr₁' x (hwf.vars V hV x hx)) hwf
      (fun x hx => ⟨(hL x hx).1, by have := (hL x hx).2; omega⟩) (by omega) (by omega)
    exact ⟨o', .cons (.block (ho ▸ hseq) (.brk0 nofun)) (.abrupt hloop hlo'.abrupt),
      hlo'.trans hl₁ hfr₁'⟩
  · obtain ⟨hfl, hvi⟩ := follow_exit hf hn h0
    have hlo₁ : LabelOut c.labels (c.wdepth + 1) c.fty ls st.next l v o := by
      simpa only [hfl, hvi, LabelOut.succ] using hlo.mono hal
    obtain ⟨o', hbe, hlo'⟩ := hlo₁.blockExit (fun w L hL => (hwf.labels w L hL).1)
    exact ⟨o', .abrupt (.block hseq hbe) hlo'.abrupt, hlo'⟩

/-- A `cfg` whose entry never jumps to its block: the entry runs in a Wasm `block`
whose fallthrough is unreachable. -/
private theorem sim_cfg_trap {entry : Region Prim} {n : Nat} {blocks : Fin n → Region Prim}
    {initial v : SVal} {first l : Nat}
    (he : Region.Eval instr env entry () first initial ())
    (hf : Region.Follow instr env blocks first initial () l v ())
    (ihe : SimR env entry first initial) (hn : n = 1) {c : DCtx} {st st' : DState}
    {ce : List Expr} {ls : List WVal} (hment : Region.mentionsLabel 0 entry = false)
    (h₁ : dR { c with labels := .trap :: c.labels, wdepth := c.wdepth + 1 } entry st =
      some (ce, st'))
    (hv : VarsOK ls c.vars env) (hwf : WF c st.next) (hlen : st'.next ≤ ls.length) :
    ∃ o, Seq ls none [.block none ce, .unreachable] o ∧
      LabelOut c.labels c.wdepth c.fty ls st.next l v o := by
  obtain ⟨o, hseq, hlo⟩ := ihe _ _ _ _ ls h₁ hv hwf.pushTrap hlen
  have h0 : first ≠ 0 := fun h => by simpa [h, hment] using eval_mentions he
  obtain ⟨hfl, hvi⟩ := follow_exit hf hn h0
  have hlo₁ : LabelOut c.labels (c.wdepth + 1) c.fty ls st.next l v o := by
    simpa only [hfl, hvi, LabelOut.succ] using hlo
  obtain ⟨o', hbe, hlo'⟩ := hlo₁.blockExit (fun w L hL => (hwf.labels w L hL).1)
  exact ⟨o', .abrupt (.block hseq hbe) hlo'.abrupt, hlo'⟩

private theorem sim_cfg {entry : Region Prim} {n : Nat} {blocks : Fin n → Region Prim}
    {initial v : SVal} {first l : Nat}
    (he : Region.Eval instr env entry () first initial ())
    (hf : Region.Follow instr env blocks first initial () l v ())
    (ihe : SimR env entry first initial) (ihf : SimF env blocks first initial l v) :
    SimR env (.cfg entry n blocks) l v := by
  intro c st code st' ls hd hv hwf hlen
  obtain ⟨hn, ⟨sh, ce, s₂, cb, -, h₂, h₃, hcode⟩ | ⟨ce, hment, h₁, hcode⟩⟩ := dR_cfg hd
  · rw [hcode]
    exact sim_cfg_loop hf ihe ihf hn (allocShape_spec sh st).1 (allocShape_spec sh st).2 h₂ h₃
      hv hwf hlen
  · rw [hcode]
    exact sim_cfg_trap he hf ihe hn hment h₁ hv hwf hlen

/-- One transfer to the block: one iteration of the Wasm `loop`. -/
private theorem sim_step {n label next out : Nat} {blocks : Fin n → Region Prim}
    {current middle value : SVal} (inside : label < n)
    (tail : Region.Follow instr env blocks next middle () out value ())
    (ihh : SimR (extend env current) (blocks ⟨label, inside⟩) next middle)
    (iht : SimF env blocks next middle out value) :
    SimF env blocks label current out value := by
  intro c L st₂ st₃ cb ls base hn h0 hd hrd hv hwf hLb hb hlen
  have hd0 : dR (loopCtx c L) (blocks ⟨label, inside⟩) st₂ = some (cb, st₃) := by
    rw [show (⟨label, inside⟩ : Fin n) = ⟨0, by omega⟩ from Fin.ext h0]
    exact hd _
  obtain ⟨o, hseq, hlo⟩ := ihh (loopCtx c L) st₂ cb st₃ ls hd0 (varsOK_cons hv hrd)
    ((hwf.mono hb).loop fun x hx => (hLb x hx).2) hlen
  by_cases hn0 : next = 0
  · obtain ⟨ls₂, ho, hrd₂, hl₂, hfr₂⟩ := LabelOut.head_block (by simpa only [hn0, loopCtx] using hlo)
    have hfr₂' : ∀ x, x < base → ls₂[x]? = ls[x]? := fun x hx =>
      hfr₂ x (by omega) (fun h => by have := (hLb x h).1; omega)
    obtain ⟨o', hloop, hlo'⟩ := iht c L st₂ st₃ cb ls₂ base hn hn0 hd hrd₂
      (varsOK_frame hv fun V hV x hx => hfr₂' x (hwf.vars V hV x hx)) hwf hLb hb (by omega)
    exact ⟨o', .loop_back (ho ▸ hseq) hloop, hlo'.trans hl₂ hfr₂'⟩
  · obtain ⟨hfl, hvi⟩ := follow_exit tail hn hn0
    have hlo₁ : LabelOut c.labels (c.wdepth + 1) c.fty ls base out value o := by
      simpa only [hfl, hvi, loopCtx, LabelOut.succ] using hlo.mono hb
    obtain ⟨o', hle, hlo'⟩ := hlo₁.loopExit (fun w L hL => (hwf.labels w L hL).1)
    exact ⟨o', .loop hseq hle, hlo'⟩

end Cases

open Silmaril.Isotope.LambdaSSA.Semantics in
/-- **Simulation.** A region's evaluation is matched by its decompilation. -/
theorem sim {env : Env WVal} {r : Region Prim} {s₀ s₀' : Unit} {l : Nat} {v : SVal}
    (h : Region.Eval instr env r s₀ l v s₀') :
    ∀ (c : DCtx) (st : DState) (code : List Expr) (st' : DState) (ls : List WVal),
      dR c r st = some (code, st') → VarsOK ls c.vars env → WF c st.next →
      st'.next ≤ ls.length →
      ∃ o, Seq ls none code o ∧ LabelOut c.labels c.wdepth c.fty ls st.next l v o := by
  induction h using Region.Eval.rec
    (motive_2 := fun env _ blocks first init _ out v _ _ => SimF env blocks first init out v) with
  | br harg => exact sim_br harg
  | let₁ ht _ ih => exact sim_let₁ ht ih
  | let₂ ht _ ih => exact sim_let₂ ht ih
  | case_inl ht _ ih => exact sim_case_inl ht ih
  | case_inr ht hr ih => exact sim_case_inr ht hr ih
  | cfg he hf ihe ihf => exact sim_cfg he hf ihe ihf
  | exit outside => intro c L st₂ st₃ cb ls base hn h0; omega
  | step inside _ tail ihh iht => exact sim_step inside tail ihh iht

end Silmaril.Proofs.Wasm.SSA.OutOfSSA
