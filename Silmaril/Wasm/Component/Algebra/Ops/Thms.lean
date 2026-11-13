module

public import Silmaril.Wasm.Component.Algebra.Ops.Defs
public import Silmaril.Wasm.Component.Algebra.Term.Thms
public import Silmaril.Games.PairProj.Thms

/-!
# Composition operators: laws and congruence

## Handler and wiring lemmas

* `implsH_fwds`, `implsH_fwds_exact`: forwarding wiring is a shift then masks;
* `ext_comp_shiftH`: an extended environment seen only through the new node's functions
  is the new node on top of the old environment (`Strategy.pair_comp_ofHom_inr`);
* `maskH_comp_implsH`: wiring programs over `e` functions do not see beyond `e`.

## The meaning of each operator

* `denU_ident`: the identity component is the mask (copycat) of its imports;
* `denU_seq`: **plugging is composition of strategies**, with no side condition:
  `(seq c₁ c₂).denU C = (c₁.denU C).comp (c₂.denU C)`;
* `denU_wrap`, `denU_reimport`: instantiation with arguments is the wiring handler
  below the component;
* `denU_select`: hiding is the selection handler above the component;
* `denU_renameExports`, `denU_renameImports`: renaming does not change the strategy.

## Laws (a presentation of the algebra, up to `CompEquiv`)

* category: `seq_assoc`, `seq_ident_left`, `seq_ident_right`;
* renaming: `renameExports_equiv`, `renameImports_equiv`, `renameExports_comp`,
  `renameImports_comp`;
* hiding: `select_range`, `select_select`;
* promotion and merging: `reimport_range`, `reimport_reimport`.

## Congruence

`seq_congr`, `par_congr`, `wrap_congr`, `reimport_congr`, `select_congr`,
`renameExports_congr`, `renameImports_congr`, and their refinement versions
(`seq_mono`, `par_mono`, `wrap_mono`, `select_mono`).
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

/-! ## Lists of wiring -/

theorem length_reexport : ∀ (b : Nat) (xs : List Export), (reexport b xs).length = xs.length
  | _, [] => rfl
  | b, _ :: xs => by simp only [reexport, List.length_cons, length_reexport (b + 1) xs]

theorem fwds_succ (b n : Nat) : fwds b (n + 1) = Impl.fwd b :: fwds (b + 1) n := by
  simp only [fwds, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  congr 1
  omega

theorem map_impl_reexport :
    ∀ (b : Nat) (xs : List Export), (reexport b xs).map Export.impl = fwds b xs.length
  | b, [] => by simp only [reexport, List.map_nil, List.length_nil, fwds, List.range_zero]
  | b, x :: xs => by
    simp only [reexport, List.map_cons, List.length_cons, fwds_succ, map_impl_reexport (b + 1) xs]

theorem fwds_zero (n : Nat) : fwds 0 n = (List.range n).map Impl.fwd := by
  simp only [fwds, Nat.zero_add]

theorem length_fwds (b n : Nat) : (fwds b n).length = n := by
  simp only [fwds, List.length_map, List.length_range]

theorem map_impl_keptExports (b : Nat) (xs : List Export) :
    ∀ keep : List Nat, (keptExports b xs keep).map Export.impl =
      (keep.filter (· < xs.length)).map fun j => Impl.fwd (b + j)
  | [] => rfl
  | j :: keep => by
    have ih := map_impl_keptExports b xs keep
    by_cases hj : j < xs.length
    · have hs : xs[j]? = some xs[j] := List.getElem?_eq_getElem hj
      simp only [keptExports, List.filterMap_cons, hs, Option.map_some, List.map_cons,
        List.filter_cons, hj, decide_true, ↓reduceIte] at ih ⊢
      rw [ih]
    · have hs : xs[j]? = none := List.getElem?_eq_none (by omega)
      simp only [keptExports, List.filterMap_cons, hs, Option.map_none, List.filter_cons, hj,
        decide_false, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      exact ih

theorem length_keptExports (b : Nat) (xs : List Export) (keep : List Nat) :
    (keptExports b xs keep).length = (keep.filter (· < xs.length)).length := by
  rw [← List.length_map (f := Export.impl), map_impl_keptExports, List.length_map]

/-! ## Handler lemmas -/

theorem implsH_fwds {b e : Nat} (hb : b ≤ e) (n : Nat) :
    implsH e (fwds b n) = (shiftH b).comp ((maskH (e - b)).comp (maskH n)) := by
  funext q
  obtain ⟨i, a⟩ := q
  by_cases hi : i < n
  · have hr : (fwds b n)[i]? = some (Impl.fwd (b + i)) := by
      simp only [fwds, List.getElem?_map, List.getElem?_range hi, Option.map_some]
    by_cases hb' : b + i < e
    · have hi' : i < e - b := by omega
      simp only [implsH, hr, Impl.prog, runChain, Target.prog, hb', ↓reduceIte, Handler.comp,
        maskH, hi, hi', Prog.interp_call, Prog.interp_pure, Prog.bind_pure, shiftH]
    · have hi' : ¬ i < e - b := by omega
      simp only [implsH, hr, Impl.prog, runChain, Target.prog, hb', ↓reduceIte, Handler.comp,
        maskH, hi, hi', Prog.interp_call, Prog.interp_pure, Prog.bind_pure]
  · have hr : (fwds b n)[i]? = none := List.getElem?_eq_none (by simpa [length_fwds] using hi)
    simp only [implsH, hr, Handler.comp, maskH, Target.prog, hi, ↓reduceIte, Prog.interp_pure]

theorem implsH_fwds_exact (b n : Nat) :
    implsH (b + n) (fwds b n) = (shiftH b).comp (maskH n) := by
  rw [implsH_fwds (Nat.le_add_right b n), Nat.add_sub_cancel_left, maskH_comp_maskH]

theorem splitH_comp_shiftH (e : Nat) :
    (splitH e).comp (shiftH e) = Handler.ofHom (Sig.Hom.inr sigU sigU) := by
  funext q
  obtain ⟨i, a⟩ := q
  have hi : ¬ e + i < e := by omega
  have he : e + i - e = i := by omega
  simp only [Handler.comp, shiftH, splitH, Prog.interp_call, Prog.interp_pure, Prog.bind_pure,
    hi, ↓reduceIte]
  rw [he]
  rfl

/-- An extended environment observed through the new node only. -/
theorem ext_comp_shiftH {X : Sig.{0}} (e : Nat) (D : Strategy X sigU) (N : Strategy sigU sigU) :
    (ext e D N).comp (Strategy.ofHandler (shiftH e)) = D.comp N := by
  rw [ext, Strategy.comp_assoc, Strategy.comp_assoc, ← Strategy.ofHandler_comp,
    splitH_comp_shiftH, Strategy.pair_comp_ofHom_inr]

/-- `ext_comp_shiftH` below a further strategy. -/
theorem ext_comp_shiftH_comp {X Y : Sig.{0}} (e : Nat) (D : Strategy X sigU)
    (N : Strategy sigU sigU) (S : Strategy sigU Y) :
    (ext e D N).comp ((Strategy.ofHandler (shiftH e)).comp S) = (D.comp N).comp S := by
  rw [← Strategy.comp_assoc, ext_comp_shiftH]

theorem Target.prog_interp_maskH (e : Nat) (t : Target) (y : Payload) :
    (t.prog e y).interp (maskH e) = t.prog e y := by
  cases t with
  | const res => rfl
  | call r =>
    by_cases hr : r < e
    · simp only [Target.prog, hr, ↓reduceIte, Prog.interp_call, Prog.interp_pure,
        Prog.bind_pure, maskH]
    · simp only [Target.prog, hr, ↓reduceIte, Prog.interp_pure]

/-- Wiring programs over `e` functions do not see beyond `e`. -/
theorem maskH_comp_implsH (e : Nat) (ims : List Impl) :
    (maskH e).comp (implsH e ims) = implsH e ims := by
  funext q
  simp only [Handler.comp, implsH]
  cases ims[q.1]? with
  | none => rfl
  | some im =>
    simp only [Impl.prog, runChain_interp, Target.prog_interp_maskH]

theorem implsH_comp_selectH_shift (b k : Nat) (keep : List Nat) :
    implsH (b + k) ((keep.filter (· < k)).map fun j => Impl.fwd (b + j)) =
      (shiftH b).comp (selectH (keep.filter (· < k))) := by
  funext q
  obtain ⟨i, a⟩ := q
  simp only [implsH, List.getElem?_map, Handler.comp, selectH]
  cases h : (keep.filter (· < k))[i]? with
  | none => simp only [Option.map_none, Prog.interp_pure]
  | some j =>
    have hj : j < k := by
      have hm := List.mem_of_getElem? h
      simpa using (List.mem_filter.1 hm).2
    have hj' : b + j < b + k := by omega
    simp only [Option.map_some, Impl.prog, runChain, Target.prog, hj', ↓reduceIte,
      Prog.interp_call, Prog.interp_pure, Prog.bind_pure, shiftH]

/-! ## Strategy-level helpers -/

variable [CoreModule M]

/-- Forwarding all imports into a component is the component. -/
theorem fwds_comp_denU (C : CoreSem M) (c : Comp M) :
    (Strategy.ofHandler (implsH c.imports.length (fwds 0 c.imports.length))).comp (c.denU C) =
      c.denU C := by
  rw [fwds_zero, implsH_fwd, maskH_comp_denU]

/-- An environment observed through the forwarding of its last node's exports. -/
theorem ext_comp_reexport {X : Sig.{0}} (e : Nat) (D : Strategy X sigU) (N : Strategy sigU sigU)
    (xs : List Export) :
    (ext e D N).comp (Strategy.ofHandler (exportsH (e + xs.length) (reexport e xs))) =
      (D.comp N).comp (Strategy.ofHandler (maskH xs.length)) := by
  rw [exportsH, map_impl_reexport, implsH_fwds_exact, Strategy.ofHandler_comp,
    ← Strategy.comp_assoc, ext_comp_shiftH]

/-! ## The meaning of each operator -/

/-- The identity component is copycat on its imports, masked. -/
theorem denU_ident (C : CoreSem M) (I : Iface) :
    (ident I : Comp M).denU C = Strategy.ofHandler (maskH I.length) := by
  have hx : (reexport 0 (ifaceExports I)).map Export.impl = (List.range I.length).map Impl.fwd := by
    rw [map_impl_reexport, fwds_zero, ifaceExports, List.length_map]
  simp only [ident, Comp.denU, denNodes, envAfter, exportsH, hx, implsH_fwd]
  rw [← Strategy.ofHandler_comp, maskH_comp_maskH]

/-- **Plugging is composition of strategies.** -/
theorem denU_seq (C : CoreSem M) (c₁ c₂ : Comp M) :
    (seq c₁ c₂).denU C = (c₁.denU C).comp (c₂.denU C) := by
  have hN₁ : (Strategy.ofHandler (maskH c₁.imports.length)).comp
      ((Strategy.ofHandler (implsH c₁.imports.length (fwds 0 c₁.imports.length))).comp
        (c₁.denU C)) = c₁.denU C := by
    rw [fwds_comp_denU, maskH_comp_denU]
  have hA : implsH (c₁.imports.length + c₁.exports.length)
      (fwds c₁.imports.length c₂.imports.length) =
      (shiftH c₁.imports.length).comp ((maskH c₁.exports.length).comp
        (maskH c₂.imports.length)) := by
    rw [implsH_fwds (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have hT : Comp.denU C (seq c₁ c₂) =
      ((ext (c₁.imports.length + c₁.exports.length)
        (ext c₁.imports.length (Strategy.ofHandler (maskH c₁.imports.length))
          ((Strategy.ofHandler (implsH c₁.imports.length (fwds 0 c₁.imports.length))).comp
            (c₁.denU C)))
        ((Strategy.ofHandler (implsH (c₁.imports.length + c₁.exports.length)
          (fwds c₁.imports.length c₂.imports.length))).comp (c₂.denU C))).comp
      (Strategy.ofHandler (exportsH (c₁.imports.length + c₁.exports.length + c₂.exports.length)
        (reexport (c₁.imports.length + c₁.exports.length) c₂.exports)))) := by
    simp only [seq, Comp.denU, denNodes, Node.den, Node.width, envAfter]
  rw [hT, ext_comp_reexport, Strategy.comp_assoc, Strategy.comp_assoc, denU_comp_maskH, hA,
    Strategy.ofHandler_comp, Strategy.ofHandler_comp, ← Strategy.comp_assoc (ext _ _ _),
    ext_comp_shiftH_comp, hN₁, Strategy.comp_assoc, Strategy.comp_assoc, maskH_comp_denU,
    ← Strategy.comp_assoc, denU_comp_maskH]

/-- **Instantiation with arguments** is the wiring handler below the component. -/
theorem denU_wrap (C : CoreSem M) (I : Iface) (args : List Impl) (c : Comp M) :
    (wrap I args c).denU C = (Strategy.ofHandler (implsH I.length args)).comp (c.denU C) := by
  have hT : (wrap I args c).denU C =
      (ext I.length (Strategy.ofHandler (maskH I.length))
        ((Strategy.ofHandler (implsH I.length args)).comp (c.denU C))).comp
        (Strategy.ofHandler (exportsH (I.length + c.exports.length) (reexport I.length c.exports)))
      := by
    simp only [wrap, Comp.denU, denNodes, Node.den, Node.width, envAfter]
  rw [hT, ext_comp_reexport, Strategy.comp_assoc, Strategy.comp_assoc, denU_comp_maskH,
    ← Strategy.comp_assoc, ← Strategy.ofHandler_comp, maskH_comp_implsH]

/-- Promotion and merging of imports. -/
theorem denU_reimport (C : CoreSem M) (I : Iface) (ρ : List Nat) (c : Comp M) :
    (reimport I ρ c).denU C =
      (Strategy.ofHandler (implsH I.length (ρ.map Impl.fwd))).comp (c.denU C) :=
  denU_wrap C I _ c

/-- **Hiding** is the selection of the kept exports above the component. -/
theorem denU_select (C : CoreSem M) (keep : List Nat) (c : Comp M) :
    (select keep c).denU C =
      (c.denU C).comp (Strategy.ofHandler (selectH (keep.filter (· < c.exports.length)))) := by
  have hx : exportsH (c.imports.length + c.exports.length)
      (keptExports c.imports.length c.exports keep) =
      (shiftH c.imports.length).comp (selectH (keep.filter (· < c.exports.length))) := by
    rw [exportsH, map_impl_keptExports, implsH_comp_selectH_shift]
  have hT : (select keep c).denU C =
      (ext c.imports.length (Strategy.ofHandler (maskH c.imports.length))
        ((Strategy.ofHandler (implsH c.imports.length (fwds 0 c.imports.length))).comp
          (c.denU C))).comp
        (Strategy.ofHandler (exportsH (c.imports.length + c.exports.length)
          (keptExports c.imports.length c.exports keep))) := by
    simp only [select, Comp.denU, denNodes, Node.den, Node.width, envAfter]
  rw [hT, hx, Strategy.ofHandler_comp, ← Strategy.comp_assoc, ext_comp_shiftH, fwds_comp_denU,
    maskH_comp_denU]

theorem denU_renameExports (C : CoreSem M) (f : String → String) (c : Comp M) :
    (renameExports f c).denU C = c.denU C := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [renameExports, Comp.denU, exportsH, List.map_map, Function.comp_def]

theorem denU_renameImports (C : CoreSem M) (f : String → String) (c : Comp M) :
    (renameImports f c).denU C = c.denU C := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [renameImports, Comp.denU, List.length_map]

/-! ## Sizes -/

omit [CoreModule M] in
theorem sizes_seq (c₁ c₂ : Comp M) :
    (seq c₁ c₂).imports = c₁.imports ∧ (seq c₁ c₂).exports.length = c₂.exports.length :=
  ⟨rfl, length_reexport _ _⟩

omit [CoreModule M] in
theorem sizes_wrap (I : Iface) (args : List Impl) (c : Comp M) :
    (wrap I args c).imports = I ∧ (wrap I args c).exports.length = c.exports.length :=
  ⟨rfl, length_reexport _ _⟩

omit [CoreModule M] in
theorem sameSizes_renameExports (f : String → String) (c : Comp M) :
    SameSizes (renameExports f c) c := by
  obtain ⟨I, ns, xs⟩ := c
  exact ⟨rfl, List.length_map _⟩

omit [CoreModule M] in
theorem sameSizes_renameImports (f : String → String) (c : Comp M) :
    SameSizes (renameImports f c) c := by
  obtain ⟨I, ns, xs⟩ := c
  exact ⟨List.length_map _, rfl⟩

/-! ## Laws -/

/-- **Associativity of plugging.** -/
theorem seq_assoc (C : CoreSem M) (c₁ c₂ c₃ : Comp M) :
    CompEquiv C (seq (seq c₁ c₂) c₃) (seq c₁ (seq c₂ c₃)) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · rw [(sizes_seq _ _).2, (sizes_seq _ _).2, (sizes_seq _ _).2]
  · rw [denU_seq, denU_seq, denU_seq, denU_seq, Strategy.comp_assoc]

/-- The identity is a left unit of plugging. -/
theorem seq_ident_left (C : CoreSem M) (c : Comp M) : CompEquiv C (seq (ident c.imports) c) c := by
  refine ⟨⟨rfl, (sizes_seq _ _).2⟩, ?_⟩
  rw [denU_seq, denU_ident, maskH_comp_denU]

/-- The identity is a right unit of plugging. -/
theorem seq_ident_right (C : CoreSem M) (c : Comp M) :
    CompEquiv C (seq c (ident (exportIface c))) c := by
  have hk : (ident (exportIface c) : Comp M).exports.length = c.exports.length := by
    simp only [ident, Comp.exports_mk, length_reexport, ifaceExports, exportIface,
      List.length_map]
  refine ⟨⟨rfl, (sizes_seq _ _).2.trans hk⟩, ?_⟩
  rw [denU_seq, denU_ident]
  have hl : (exportIface c).length = c.exports.length := List.length_map _
  rw [hl, denU_comp_maskH]

/-- Renaming exports is an equivalence. -/
theorem renameExports_equiv (C : CoreSem M) (f : String → String) (c : Comp M) :
    CompEquiv C (renameExports f c) c :=
  ⟨sameSizes_renameExports f c, denU_renameExports C f c⟩

/-- Renaming imports is an equivalence. -/
theorem renameImports_equiv (C : CoreSem M) (f : String → String) (c : Comp M) :
    CompEquiv C (renameImports f c) c :=
  ⟨sameSizes_renameImports f c, denU_renameImports C f c⟩

omit [CoreModule M] in
/-- Renamings compose. -/
theorem renameExports_comp (f g : String → String) (c : Comp M) :
    renameExports f (renameExports g c) = renameExports (f ∘ g) c := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [renameExports, List.map_map, Function.comp_def]

omit [CoreModule M] in
theorem renameImports_comp (f g : String → String) (c : Comp M) :
    renameImports f (renameImports g c) = renameImports (f ∘ g) c := by
  obtain ⟨I, ns, xs⟩ := c
  simp only [renameImports, List.map_map, Function.comp_def]

/-- Keeping every export, in order, is the component. -/
theorem select_range (C : CoreSem M) (c : Comp M) :
    (select (List.range c.exports.length) c).denU C = c.denU C := by
  have hf : (List.range c.exports.length).filter (· < c.exports.length) =
      List.range c.exports.length :=
    List.filter_eq_self.2 fun j hj => by simpa using hj
  have hs : selectH (List.range c.exports.length) = maskH c.exports.length := by
    funext q
    obtain ⟨i, a⟩ := q
    by_cases hi : i < c.exports.length
    · simp only [selectH, List.getElem?_range hi, maskH, Target.prog, hi, ↓reduceIte]
    · have hn : (List.range c.exports.length)[i]? = none := List.getElem?_eq_none (by simpa using hi)
      simp only [selectH, hn, maskH, Target.prog, hi, ↓reduceIte]
  rw [denU_select, hf, hs, denU_comp_maskH]

/-- Promotion with the identity wiring is the component. -/
theorem reimport_range (C : CoreSem M) (c : Comp M) :
    CompEquiv C (reimport c.imports (List.range c.imports.length) c) c := by
  refine ⟨⟨rfl, (sizes_wrap _ _ _).2⟩, ?_⟩
  rw [denU_reimport, implsH_fwd, maskH_comp_denU]

/-- **Promotions compose**: re-importing twice is re-importing along the composite
(merging is associative). -/
theorem reimport_reimport (C : CoreSem M) (I J : Iface) (ρ ρ' : List Nat) (c : Comp M)
    (hρ : ρ.length = J.length) (hρ' : ∀ r ∈ ρ', r < ρ.length) :
    CompEquiv C (reimport I ρ (reimport J ρ' c)) (reimport I (ρ'.map fun r => ρ.getD r 0) c) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [reimport, wrap, Comp.exports_mk, length_reexport]
  · have hJ : J.length = (ρ.map Impl.fwd).length := by rw [List.length_map, hρ]
    have hs : (ρ'.map Impl.fwd).map (Impl.subst (ρ.map Impl.fwd)) =
        (ρ'.map fun r => ρ.getD r 0).map Impl.fwd := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r hr
      have hlt := hρ' r hr
      simp only [Function.comp_apply, Impl.subst, List.getElem?_map,
        List.getElem?_eq_getElem hlt, Option.map_some, List.getD_eq_getElem?_getD,
        Option.getD_some, List.nil_append]
    rw [denU_reimport, denU_reimport, denU_reimport, ← Strategy.comp_assoc,
      ← Strategy.ofHandler_comp, hJ, implsH_comp_subst, hs]

/-! ## Congruence -/

/-- **Plugging is monotone.** -/
theorem seq_mono {C : CoreSem M} {c₁ c₁' c₂ c₂' : Comp M} (h₁ : CompRefines C c₁ c₁')
    (h₂ : CompRefines C c₂ c₂') : CompRefines C (seq c₁ c₂) (seq c₁' c₂') := by
  refine ⟨⟨h₁.1.1, ?_⟩, ?_⟩
  · rw [(sizes_seq _ _).2, (sizes_seq _ _).2, h₂.1.2]
  · rw [denU_seq, denU_seq]
    exact Strategy.comp_mono h₁.2 h₂.2

/-- **Plugging equivalent components gives equivalent compositions.** -/
theorem seq_congr {C : CoreSem M} {c₁ c₁' c₂ c₂' : Comp M} (h₁ : CompEquiv C c₁ c₁')
    (h₂ : CompEquiv C c₂ c₂') : CompEquiv C (seq c₁ c₂) (seq c₁' c₂') :=
  compEquiv_iff_refines.2 ⟨seq_mono h₁.refines h₂.refines, seq_mono h₁.symm.refines h₂.symm.refines⟩

theorem wrap_mono {C : CoreSem M} (I : Iface) (args : List Impl) {c c' : Comp M}
    (h : CompRefines C c c') : CompRefines C (wrap I args c) (wrap I args c') := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · rw [(sizes_wrap _ _ _).2, (sizes_wrap _ _ _).2, h.1.2]
  · rw [denU_wrap, denU_wrap]
    exact Strategy.comp_mono le_rfl h.2

/-- Instantiation with arguments is a congruence. -/
theorem wrap_congr {C : CoreSem M} (I : Iface) (args : List Impl) {c c' : Comp M}
    (h : CompEquiv C c c') : CompEquiv C (wrap I args c) (wrap I args c') :=
  compEquiv_iff_refines.2 ⟨wrap_mono I args h.refines, wrap_mono I args h.symm.refines⟩

/-- Promotion and merging of imports is a congruence. -/
theorem reimport_congr {C : CoreSem M} (I : Iface) (ρ : List Nat) {c c' : Comp M}
    (h : CompEquiv C c c') : CompEquiv C (reimport I ρ c) (reimport I ρ c') :=
  wrap_congr I _ h

theorem select_mono {C : CoreSem M} (keep : List Nat) {c c' : Comp M} (h : CompRefines C c c') :
    CompRefines C (select keep c) (select keep c') := by
  refine ⟨⟨h.1.1, ?_⟩, ?_⟩
  · simp only [select, Comp.exports_mk, length_keptExports, h.1.2]
  · rw [denU_select, denU_select, h.1.2]
    exact Strategy.comp_mono h.2 le_rfl

/-- Hiding is a congruence. -/
theorem select_congr {C : CoreSem M} (keep : List Nat) {c c' : Comp M} (h : CompEquiv C c c') :
    CompEquiv C (select keep c) (select keep c') :=
  compEquiv_iff_refines.2 ⟨select_mono keep h.refines, select_mono keep h.symm.refines⟩

/-- Renaming is a congruence. -/
theorem renameExports_congr {C : CoreSem M} (f : String → String) {c c' : Comp M}
    (h : CompEquiv C c c') : CompEquiv C (renameExports f c) (renameExports f c') :=
  (renameExports_equiv C f c).trans (h.trans (renameExports_equiv C f c').symm)

theorem renameImports_congr {C : CoreSem M} (f : String → String) {c c' : Comp M}
    (h : CompEquiv C c c') : CompEquiv C (renameImports f c) (renameImports f c') :=
  (renameImports_equiv C f c).trans (h.trans (renameImports_equiv C f c').symm)

/-- The meaning of independent instantiation, unfolded: it depends on the arguments only
through their sizes and meanings. -/
theorem denU_par (C : CoreSem M) (c₁ c₂ : Comp M) :
    (par c₁ c₂).denU C =
      ((ext (c₁.imports.length + c₂.imports.length + c₁.exports.length)
        (ext (c₁.imports.length + c₂.imports.length)
          (Strategy.ofHandler (maskH (c₁.imports.length + c₂.imports.length)))
          ((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length)
            (fwds 0 c₁.imports.length))).comp (c₁.denU C)))
        ((Strategy.ofHandler (implsH (c₁.imports.length + c₂.imports.length + c₁.exports.length)
          (fwds c₁.imports.length c₂.imports.length))).comp (c₂.denU C))).comp
      (Strategy.ofHandler (implsH
        (c₁.imports.length + c₂.imports.length + c₁.exports.length + c₂.exports.length)
        (fwds (c₁.imports.length + c₂.imports.length)
          (c₁.exports.length + c₂.exports.length))))) := by
  simp only [par, Comp.denU, denNodes, Node.den, Node.width, envAfter, exportsH,
    map_impl_reexport, List.length_append]

theorem par_mono {C : CoreSem M} {c₁ c₁' c₂ c₂' : Comp M} (h₁ : CompRefines C c₁ c₁')
    (h₂ : CompRefines C c₂ c₂') : CompRefines C (par c₁ c₂) (par c₁' c₂') := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [par, Comp.imports_mk, List.length_append, h₁.1.1, h₂.1.1]
  · simp only [par, Comp.exports_mk, length_reexport, List.length_append, h₁.1.2, h₂.1.2]
  · rw [denU_par, denU_par, h₁.1.1, h₁.1.2, h₂.1.1, h₂.1.2]
    exact Strategy.comp_mono (ext_mono _ (ext_mono _ le_rfl (Strategy.comp_mono le_rfl h₁.2))
      (Strategy.comp_mono le_rfl h₂.2)) le_rfl

/-- **Independent instantiation is a congruence.** -/
theorem par_congr {C : CoreSem M} {c₁ c₁' c₂ c₂' : Comp M} (h₁ : CompEquiv C c₁ c₁')
    (h₂ : CompEquiv C c₂ c₂') : CompEquiv C (par c₁ c₂) (par c₁' c₂') :=
  compEquiv_iff_refines.2 ⟨par_mono h₁.refines h₂.refines, par_mono h₁.symm.refines h₂.symm.refines⟩

end Silmaril.Wasm.Component.Algebra
