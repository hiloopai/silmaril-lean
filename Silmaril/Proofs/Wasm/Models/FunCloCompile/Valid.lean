module

public import Silmaril.Wasm.Models.FunCloCompile.Defs
public import Silmaril.Wasm.Models.FunCompile.Thms

/-!
# Compiling FunClo: the compiled module validates

A typing derivation (`InstrsOk`) of the code of every scoped term (`Sc d e`: its variables are
below `d`), by induction on the term (`ty_compile`), reusing FunCompile's instruction-group
lemmas (`Silmaril.Proofs.Wasm.Models.FunCompile.Valid`). The new groups are the environment list
(`ty_envCode`), `call 1` (`ty_call`), the entries and the dispatch of `apply` (`ty_unpack`,
`ty_entry`, `ty_dispatch`). `funcOk_main` and `funcOk_apply` give `Func_ok` of both functions,
and `moduleValid` gives `ModuleValid (moduleOf p)` for every well-typed program within Wasm's
limits. Well-typed programs are scoped (`sc_of_hasTy`), and so is every body of their closure
table (`sc_table`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunCloCompile
open Silmaril.Wasm.Models.FunClo (Tm Prog HasTy tableLocals)
open Silmaril.Wasm.Models.FunCompile (anyref dBox dMain lx fx boxIdx unbox getField)
open Silmaril.Proofs.Wasm.Models.FunCompile (anyC seqP consP frameP subP HasTypes Good Good.mono
  Good.withLabel Good.local Good.lim lx_toNat ty_localGet ty_localSet ty_const ty_constBox ty_box
  ty_unbox ty_castBox ty_getBox ty_newBox ty_if frame1 ty_getField ok_anyC ok_i32 depth_le_left
  depth_le_right localsOk)

/-! ## Scoping -/

/-- `e`'s variables are below `n` (a `fix` body sees two more). -/
def Sc : Nat → Tm → Prop
  | n, .var i => i < n
  | _, .int _ | _, .bool _ => True
  | n, .arith _ a b | n, .cmp _ a b | n, .pair a b | n, .app a b => Sc n a ∧ Sc n b
  | n, .ite c t e => Sc n c ∧ Sc n t ∧ Sc n e
  | n, .let_ a b => Sc n a ∧ Sc (n + 1) b
  | n, .fst e | n, .snd e | n, .inl e | n, .inr e => Sc n e
  | n, .case e l r => Sc n e ∧ Sc (n + 1) l ∧ Sc (n + 1) r
  | n, .fix b => Sc (n + 2) b

/-- **Well-typed terms are scoped.** -/
theorem sc_of_hasTy {Γ : List FunClo.Ty} {e : Tm} {τ : FunClo.Ty} (h : HasTy Γ e τ) :
    Sc Γ.length e := by
  induction h with
  | var hi => exact (List.getElem?_eq_some_iff.1 hi).1
  | int => trivial
  | bool => trivial
  | arith _ _ _ iha ihb => exact ⟨iha, ihb⟩
  | cmp _ _ _ iha ihb => exact ⟨iha, ihb⟩
  | ite _ _ _ ihc iht ihe => exact ⟨ihc, iht, ihe⟩
  | let_ _ _ iha ihb => exact ⟨iha, ihb⟩
  | pair _ _ iha ihb => exact ⟨iha, ihb⟩
  | fst _ ih => exact ih
  | snd _ ih => exact ih
  | inl _ _ ih => exact ih
  | inr _ _ ih => exact ih
  | case _ _ _ ihe ihl ihr => exact ⟨ihe, ihl, ihr⟩
  | fix _ ih => exact ih
  | app _ _ ihf iha => exact ⟨ihf, iha⟩

/-- The bodies of the `fix` subterms of a scoped term are scoped. -/
theorem sc_fixes : ∀ (e : Tm) {d : Nat}, Sc d e → ∀ {d' : Nat} {b : Tm}, (d', b) ∈ e.fixes d →
    Sc (d' + 2) b
  | .var _, _, _, _, _, h => by simp [Tm.fixes] at h
  | .int _, _, _, _, _, h => by simp [Tm.fixes] at h
  | .bool _, _, _, _, _, h => by simp [Tm.fixes] at h
  | .arith _ a c, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    exacts [sc_fixes a hs.1 h, sc_fixes c hs.2 h]
  | .cmp _ a c, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    exacts [sc_fixes a hs.1 h, sc_fixes c hs.2 h]
  | .pair a c, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    exacts [sc_fixes a hs.1 h, sc_fixes c hs.2 h]
  | .app a c, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    exacts [sc_fixes a hs.1 h, sc_fixes c hs.2 h]
  | .let_ a c, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    exacts [sc_fixes a hs.1 h, sc_fixes c hs.2 h]
  | .ite c t e, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      exacts [sc_fixes c hs.1 h, sc_fixes t hs.2.1 h]
    · exact sc_fixes e hs.2.2 h
  | .case e l r, _, hs, _, _, h => by
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      exacts [sc_fixes e hs.1 h, sc_fixes l hs.2.1 h]
    · exact sc_fixes r hs.2.2 h
  | .fst e, _, hs, _, _, h => sc_fixes e hs h
  | .snd e, _, hs, _, _, h => sc_fixes e hs h
  | .inl e, _, hs, _, _, h => sc_fixes e hs h
  | .inr e, _, hs, _, _, h => sc_fixes e hs h
  | .fix c, _, hs, _, _, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; exact hs
    · exact sc_fixes c hs h

/-- The bodies of the closure table of a well-typed program are scoped. -/
theorem sc_table {p : Prog} (hp : p.WellTyped) {d : Nat} {b : Tm} (h : (d, b) ∈ p.table) :
    Sc (d + 2) b :=
  sc_fixes p.body (sc_of_hasTy hp.1) h

theorem le_foldr_max' {l : List Nat} {n : Nat} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

theorem mem_table_locals' {L : List (Nat × Tm)} {d : Nat} {b : Tm} (h : (d, b) ∈ L) :
    d + b.depth + 1 ≤ tableLocals L :=
  le_foldr_max' (List.mem_map.2 ⟨(d, b), h, rfl⟩)

/-! ## Instruction groups -/

/-- The context is `Good` for the module's types and `apply` is function `1`. -/
def GoodF (C : Context) (n : Nat) : Prop := Good C [dMain, dApply] n ∧ C.funcs[1]? = some dApply

theorem GoodF.mono {C : Context} {n m : Nat} (h : GoodF C n) (hm : m ≤ n) : GoodF C m :=
  ⟨h.1.mono hm, h.2⟩

theorem GoodF.withLabel {C : Context} {n : Nat} (h : GoodF C n) (l : List CValType) :
    GoodF (C.withLabel l) n :=
  ⟨h.1.withLabel l, h.2⟩

theorem ty_envCode {C : Context} {n : Nat} (hg : GoodF C n) :
    ∀ j, j ≤ n → InstrsOk C (envCode j) (.plain [] [anyC])
  | 0, _ => ty_constBox hg.1.1 _
  | j + 1, hj => seqP (ty_envCode hg j (by omega))
      (seqP (frame1 hg.1.1 (ty_localGet (hg.1.local (by omega) hj) (hg.1.lim hj)) (ok_anyC _))
        (ty_newBox hg.1.1))

theorem ty_call {C : Context} (hf : C.funcs[1]? = some dApply) :
    InstrsOk C [.call ⟨1⟩] (.plain [anyC, anyC] [anyC]) :=
  .instr (InstrOk.call (ps := .cons anyC (.cons anyC .nil)) (rs := .cons anyC .nil) hf ⟨rfl⟩)

/-! ## The code of every scoped term -/

/-- The code of `case`, from the code of its parts. -/
theorem ty_case (L : List (Nat × Tm)) {e l r : Tm}
    (ihe : ∀ {d : Nat} {C : Context}, Sc d e → GoodF C (d + e.depth) →
      InstrsOk C (compile L d e) (.plain [] [anyC]))
    (ihl : ∀ {d : Nat} {C : Context}, Sc d l → GoodF C (d + l.depth) →
      InstrsOk C (compile L d l) (.plain [] [anyC]))
    (ihr : ∀ {d : Nat} {C : Context}, Sc d r → GoodF C (d + r.depth) →
      InstrsOk C (compile L d r) (.plain [] [anyC])) {d : Nat} {C : Context}
    (hs : Sc d (.case e l r)) (hg : GoodF C (d + (Tm.case e l r).depth)) :
    InstrsOk C (compile L d (.case e l r)) (.plain [] [anyC]) := by
  have hdep : (Tm.case e l r).depth = max e.depth (max l.depth r.depth + 1) := rfl
  have hm : max l.depth r.depth + 1 ≤ max e.depth (max l.depth r.depth + 1) := le_max_right _ _
  have hml : l.depth ≤ max l.depth r.depth := le_max_left _ _
  have hmr : r.depth ≤ max l.depth r.depth := le_max_right _ _
  have hg₁ : Good (C.withLabel [anyC]) [dMain, dApply] (d + 1) :=
    (hg.1.mono (by omega)).withLabel [anyC]
  have hl : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) l) (.plain [] [anyC]) :=
    seqP (ty_getField hg₁ (by omega) le_rfl (by omega))
      (seqP (ty_localSet hg₁.1 (hg₁.local (by omega) le_rfl) (hg₁.lim le_rfl))
        (ihl hs.2.1 ((hg.mono (by omega)).withLabel [anyC])))
  have hr : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) r) (.plain [] [anyC]) :=
    seqP (ty_getField hg₁ (by omega) le_rfl (by omega))
      (seqP (ty_localSet hg₁.1 (hg₁.local (by omega) le_rfl) (hg₁.lim le_rfl))
        (ihr hs.2.2 ((hg.mono (by omega)).withLabel [anyC])))
  exact seqP (seqP (seqP (ihe hs.1 (hg.mono depth_le_left))
    (seqP (ty_localSet hg.1.1 (hg.1.local (by omega) (by omega)) (hg.1.lim (by omega)))
      (ty_getField hg.1 (by omega) (by omega) (by omega)))) (ty_unbox hg.1.1))
    (ty_if hg.1.1 hr hl)

/-- **The code of every scoped term has type `[] → [anyref]`.** -/
theorem ty_compile (L : List (Nat × Tm)) : ∀ (e : Tm) {d : Nat} {C : Context}, Sc d e →
    GoodF C (d + e.depth) → InstrsOk C (compile L d e) (.plain [] [anyC])
  | .var i, d, C, hs, hg =>
    have hi : i < d := hs
    ty_localGet (hg.1.local (by omega) (by simp [Tm.depth])) (hg.1.lim (by simp [Tm.depth]))
  | .int _, _, _, _, hg => ty_constBox hg.1.1 _
  | .bool _, _, _, _, hg => ty_constBox hg.1.1 _
  | .arith op a b, _, _, hs, hg =>
    seqP (seqP (seqP (seqP (ty_compile L a hs.1 (hg.mono depth_le_left)) (ty_unbox hg.1.1))
      (frame1 hg.1.1 (ty_compile L b hs.2 (hg.mono depth_le_right)) (ok_i32 _)))
      (frame1 hg.1.1 (ty_unbox hg.1.1) (ok_i32 _)))
      (consP (.numeric (.intBinOp .i32 _)) (ty_box hg.1.1))
  | .cmp op a b, _, _, hs, hg =>
    seqP (seqP (seqP (seqP (ty_compile L a hs.1 (hg.mono depth_le_left)) (ty_unbox hg.1.1))
      (frame1 hg.1.1 (ty_compile L b hs.2 (hg.mono depth_le_right)) (ok_i32 _)))
      (frame1 hg.1.1 (ty_unbox hg.1.1) (ok_i32 _)))
      (consP (.numeric (.intRelOp .i32 _)) (ty_box hg.1.1))
  | .ite c t e, _, _, hs, hg =>
    seqP (seqP (ty_compile L c hs.1 (hg.mono depth_le_left)) (ty_unbox hg.1.1))
      (ty_if hg.1.1
        (ty_compile L t hs.2.1 ((hg.mono (le_trans depth_le_left depth_le_right)).withLabel _))
        (ty_compile L e hs.2.2 ((hg.mono (le_trans depth_le_right depth_le_right)).withLabel _)))
  | .let_ a b, d, C, hs, hg => by
    have hdep : (Tm.let_ a b).depth = max a.depth (b.depth + 1) := rfl
    have hm : b.depth + 1 ≤ max a.depth (b.depth + 1) := le_max_right _ _
    exact seqP (ty_compile L a hs.1 (hg.mono depth_le_left))
      (seqP (ty_localSet hg.1.1 (hg.1.local (by omega) (by omega)) (hg.1.lim (by omega)))
        (ty_compile L b hs.2 (hg.mono (by omega))))
  | .pair a b, _, _, hs, hg =>
    seqP (seqP (ty_compile L a hs.1 (hg.mono depth_le_left))
      (frame1 hg.1.1 (ty_compile L b hs.2 (hg.mono depth_le_right)) (ok_anyC _)))
      (ty_newBox hg.1.1)
  | .fst e, _, _, hs, hg =>
    seqP (ty_compile L e hs hg) (consP (ty_castBox hg.1.1) (ty_getBox hg.1.1 (by omega)))
  | .snd e, _, _, hs, hg =>
    seqP (ty_compile L e hs hg) (consP (ty_castBox hg.1.1) (ty_getBox hg.1.1 (by omega)))
  | .inl e, d, C, hs, hg =>
    show InstrsOk C ([.intConst .i32 0, .refI31] ++ (compile L d e ++ [.structNew boxIdx])) _ from
    seqP (ty_constBox hg.1.1 _)
      (seqP (frame1 hg.1.1 (ty_compile L e hs hg) (ok_anyC _)) (ty_newBox hg.1.1))
  | .inr e, d, C, hs, hg =>
    show InstrsOk C ([.intConst .i32 1, .refI31] ++ (compile L d e ++ [.structNew boxIdx])) _ from
    seqP (ty_constBox hg.1.1 _)
      (seqP (frame1 hg.1.1 (ty_compile L e hs hg) (ok_anyC _)) (ty_newBox hg.1.1))
  | .case e l r, _, _, hs, hg =>
    ty_case L (fun h g => ty_compile L e h g) (fun h g => ty_compile L l h g)
      (fun h g => ty_compile L r h g) hs hg
  | .fix _, d, _, _, hg =>
    seqP (seqP (ty_constBox hg.1.1 _)
      (frame1 hg.1.1 (ty_envCode hg d (by simp [Tm.depth])) (ok_anyC _))) (ty_newBox hg.1.1)
  | .app f a, _, _, hs, hg =>
    seqP (seqP (ty_compile L f hs.1 (hg.mono depth_le_left))
      (frame1 hg.1.1 (ty_compile L a hs.2 (hg.mono depth_le_right)) (ok_anyC _)))
      (ty_call hg.2)

/-! ## `apply` -/

/-- The context is `GoodF` with local `0` a set `anyref` too. -/
def GoodA (C : Context) (n : Nat) : Prop := GoodF C n ∧ C.locals[0]? = some ⟨.set, anyC⟩

theorem GoodA.withLabel {C : Context} {n : Nat} (h : GoodA C n) (l : List CValType) :
    GoodA (C.withLabel l) n :=
  ⟨h.1.withLabel l, h.2⟩

/-- Field `i` of the `$box` in local `x`, for any set `anyref` local. -/
theorem ty_getFieldAt {C : Context} {ts : List DefType} {x i : Nat}
    (hΔ : HasTypes C (dBox :: ts)) (hx : C.locals[x]? = some ⟨.set, anyC⟩) (hlim : x < 2 ^ 32)
    (hi : i < 2) : InstrsOk C (getField x i) (.plain [] [anyC]) :=
  consP (.variable (.localGet (by rw [lx_toNat hlim]; exact hx)))
    (consP (ty_castBox hΔ) (ty_getBox hΔ hi))

theorem ty_unpack {C : Context} {n c : Nat} (hg : GoodF C n) (hc : 1 ≤ c) (hcn : c ≤ n) :
    ∀ j, j < c → InstrsOk C (unpack c j) (.plain [] [])
  | 0, _ => .nil
  | j + 1, hj =>
    show InstrsOk C (getField c 1 ++ .localSet (lx (j + 1)) :: (getField c 0 ++
      .localSet (lx c) :: unpack c j)) _ from
    seqP (ty_getField hg.1 hc hcn (by omega))
      (seqP (ty_localSet hg.1.1 (hg.1.local (by omega) (by omega)) (hg.1.lim (by omega)))
        (seqP (ty_getField hg.1 hc hcn (by omega))
          (seqP (ty_localSet hg.1.1 (hg.1.local hc hcn) (hg.1.lim hcn))
            (ty_unpack hg hc hcn j (by omega)))))

theorem ty_entry (L : List (Nat × Tm)) {C : Context} {n d : Nat} {b : Tm} (hg : GoodA C n)
    (hs : Sc (d + 2) b) (hn : d + 2 + b.depth ≤ n) :
    InstrsOk C (entry L d b) (.plain [] [anyC]) := by
  have hg1 := hg.1.1
  unfold entry
  simp only [List.append_assoc]
  show InstrsOk C ([.localGet (lx 1)] ++ ([.localSet (lx (d + 2))] ++ (getField 0 1 ++
    ([.localSet (lx (d + 1))] ++ (unpack (d + 1) d ++ ([.localGet (lx 0)] ++
      ([.localSet (lx (d + 1))] ++ compile L (d + 2) b))))))) _
  have h0lim : (0 : Nat) < 2 ^ 32 := by decide
  exact seqP (ty_localGet (hg1.local le_rfl (by omega)) (hg1.lim (by omega)))
    (seqP (ty_localSet hg1.1 (hg1.local (by omega) (by omega)) (hg1.lim (by omega)))
      (seqP (ty_getFieldAt hg1.1 hg.2 h0lim (by omega))
        (seqP (ty_localSet hg1.1 (hg1.local (by omega) (by omega)) (hg1.lim (by omega)))
          (seqP (ty_unpack (hg.1.mono (by omega : d + 1 ≤ n)) (by omega) le_rfl d (by omega))
            (seqP (ty_localGet hg.2 h0lim)
              (seqP (ty_localSet hg1.1 (hg1.local (by omega) (by omega)) (hg1.lim (by omega)))
                (ty_compile L b hs (hg.1.mono hn))))))))

/-- **The dispatch of `apply` has type `[] → [anyref]`.** -/
theorem ty_dispatch (L : List (Nat × Tm)) {n : Nat}
    (hL : ∀ d b, (d, b) ∈ L → Sc (d + 2) b ∧ d + 2 + b.depth ≤ n) :
    ∀ (rest : List (Nat × Tm)) (k : Nat) {C : Context}, (∀ x ∈ rest, x ∈ L) → GoodA C n →
      InstrsOk C (dispatch L k rest) (.plain [] [anyC])
  | [], _, C, _, hg => .instr (.parametric (.unreachable (InstrTypeOk.check_sound (by
      unfold InstrTypeOk.check; rw [hg.1.1.1]; rfl))))
  | (d, b) :: rest, k, C, hr, hg => by
    have hdb := hL d b (hr _ List.mem_cons_self)
    have h0lim : (0 : Nat) < 2 ^ 32 := by decide
    show InstrsOk C ((getField 0 0 ++ unbox) ++ ([.intConst .i32 (BitVec.ofNat 32 k)] ++
      (.intRelOp .i32 .eq :: [.if_ (.value anyref) (entry L d b) (dispatch L (k + 1) rest)]))) _
    exact seqP (seqP (ty_getFieldAt hg.1.1.1 hg.2 h0lim (by omega)) (ty_unbox hg.1.1.1))
      (seqP (frame1 hg.1.1.1 (.instr (ty_const _)) (ok_i32 _))
        (consP (.numeric (.intRelOp .i32 .eq))
          (ty_if hg.1.1.1 (ty_entry L (hg.withLabel _) hdb.1 hdb.2)
            (ty_dispatch L hL rest (k + 1) (fun x hx => hr x (List.mem_cons_of_mem _ hx))
              (hg.withLabel _)))))

/-! ## Functions and modules -/

/-- The body context of `apply` with `n` `anyref` locals. -/
def applyCtx (C : Context) (n : Nat) : Context :=
  C.funcBody [anyC, anyC] [anyC] (List.replicate n ⟨.set, anyC⟩)

theorem applyCtx_good {C : Context} (hΔ : HasTypes C (dBox :: [dMain, dApply]))
    (hf : C.funcs[1]? = some dApply) {n : Nat} (hn : n + 1 < 2 ^ 32) :
    GoodA (applyCtx C n) (n + 1) := by
  refine ⟨⟨⟨hΔ, hn, fun x h₁ h₂ => ?_⟩, hf⟩, by simp [applyCtx, Context.funcBody]⟩
  rcases x with _ | _ | y
  · omega
  · simp [applyCtx, Context.funcBody]
  · simp [applyCtx, Context.funcBody, show y < n by omega]

/-- `Func_ok` of `apply`. -/
theorem funcOk_apply {C : Context} (hΔ : HasTypes C (dBox :: [dMain, dApply]))
    (hf : C.funcs[1]? = some dApply) {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) :
    FuncOk C (applyFunc p.table) dApply := by
  have hd : C.type? (applyFunc p.table).type = some dApply := by
    simp [Context.type?, hΔ.types, applyFunc, Idx.toNat]
  have hg := applyCtx_good hΔ hf (n := tableLocals p.table) (by unfold Prog.Fits at hfit; omega)
  have hL : ∀ d b, (d, b) ∈ p.table → Sc (d + 2) b ∧ d + 2 + b.depth ≤ tableLocals p.table + 1 :=
    fun d b h => ⟨sc_table hp h, by have := mem_table_locals' h; omega⟩
  exact .mk (ps := .cons anyC (.cons anyC .nil)) (rs := .cons anyC .nil) (lts :=
    List.replicate (tableLocals p.table) ⟨.set, anyC⟩) hd ⟨rfl⟩ (localsOk hΔ _)
    (ty_dispatch p.table hL p.table 0 (fun _ h => h) hg)

/-- The body context of `main` with `n` `anyref` locals. -/
def mainCtx (C : Context) (n : Nat) : Context :=
  C.funcBody [.i32] [.i32] (List.replicate n ⟨.set, anyC⟩)

theorem mainCtx_good {C : Context} (hΔ : HasTypes C (dBox :: [dMain, dApply]))
    (hf : C.funcs[1]? = some dApply) {n : Nat} (hn : n < 2 ^ 32) : GoodF (mainCtx C n) n := by
  refine ⟨⟨hΔ, hn, fun x h₁ h₂ => ?_⟩, hf⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  simp [mainCtx, Context.funcBody, show y < n by omega]

/-- `Func_ok` of `main`. -/
theorem funcOk_main {C : Context} (hΔ : HasTypes C (dBox :: [dMain, dApply]))
    (hf : C.funcs[1]? = some dApply) {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) :
    FuncOk C (mainFunc p) dMain := by
  have hd : C.type? (mainFunc p).type = some dMain := by
    simp [Context.type?, hΔ.types, mainFunc, Idx.toNat]
  have hg : GoodF (mainCtx C (p.body.depth + 1)) (p.body.depth + 1) :=
    mainCtx_good hΔ hf (by unfold Prog.Fits at hfit; omega)
  have h0 : (mainCtx C (p.body.depth + 1)).locals[0]? = some ⟨.set, .i32⟩ := by
    simp [mainCtx, Context.funcBody]
  have hpro : InstrsOk (mainCtx C (p.body.depth + 1))
      [.localGet (lx 0), .refI31, .localSet (lx 1)] (.plain [] []) :=
    consP (.variable (.localGet (by rw [lx_toNat (by decide)]; exact h0)))
      (seqP (ty_box hg.1.1) (ty_localSet hg.1.1 (hg.1.local le_rfl (by omega))
        (hg.1.lim (by omega))))
  have hc : InstrsOk (mainCtx C (p.body.depth + 1)) (compile p.table 1 p.body)
      (.plain [] [anyC]) :=
    ty_compile p.table p.body (sc_of_hasTy hp.1) (hg.mono (by omega))
  exact .mk (ps := .cons .i32 .nil) (rs := .cons .i32 .nil)
    (lts := List.replicate (p.body.depth + 1) ⟨.set, anyC⟩) hd ⟨rfl⟩ (localsOk hΔ _)
    (seqP (seqP hpro hc) (ty_unbox hg.1.1))

/-- The context `C` of `Module_ok` for a compiled module. -/
def modCtx (p : Prog) : Context :=
  moduleCtx (moduleOf p) (moduleCtx' (moduleOf p) modTypes [] [dMain, dApply]) [] [] [] [] []

theorem typesOk : TypesOk {} recTypes modTypes :=
  typesCheck?_sound (fun _ _ _ h => RecTypeOkAt.check_sound h) (by decide)

/-- **The compiled module of an accepted program validates**, with no imports and the export
`main : [i32] → [i32]`. -/
theorem moduleOk {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) :
    ModuleOk (moduleOf p) ⟨[], [.func dMain]⟩ :=
  ModuleOk.mk (fdts := [dMain, dApply]) (jts := []) (gts := []) (tts := [])
    (rts := []) (C' := moduleCtx' (moduleOf p) modTypes [] [dMain, dApply]) (C := modCtx p)
    typesOk .nil rfl rfl .nil .nil (fun _ h => absurd h List.not_mem_nil) .nil
    (.cons (funcOk_main (C := modCtx p) rfl rfl hp hfit)
      (.cons (funcOk_apply (C := modCtx p) rfl rfl hp hfit) .nil))
    (fun _ h => absurd h List.not_mem_nil) .nil (fun _ h => by cases h) (.cons (.func rfl) .nil)
    (List.nodup_singleton "main")

/-- **The compiled module of an accepted program validates.** -/
theorem moduleValid {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) : ModuleValid (moduleOf p) :=
  ⟨_, moduleOk hp hfit⟩

end Silmaril.Proofs.Wasm.Models.FunCloCompile
