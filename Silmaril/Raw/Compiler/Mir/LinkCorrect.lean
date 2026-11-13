module

public import Silmaril.Compiler.Mir.LinkCheck.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # The checked link refines the independent Mir semantics

`check_sound`: when `LinkCheck.check L base us l` holds, the linked program `l`
satisfies the conclusion of the contract `Contract.link` for `us`: under the placement
`LinkCheck.place L l`, which is valid, every non-stuck behaviour of `MirSem` from the
entry is a behaviour of `l.prog` from function 0 with the image loaded at `dataBase`.

The proof is a lock-step simulation (`Silmaril.LockstepSim`) from `MirSem.Step` to
`Lir.Step l.prog`. A Mir state is related to the Lir state at the same block and index
of the Lir function that implements its function, with the same frame and memory; a
suspended Mir caller is related to its Lir activation, and, after an indirect call, also
to the activation of the dispatcher in between (`StackRel.indirect`). Each Mir step is
one Lir step, except an indirect call (the dispatcher's comparisons, then the call) and
the return from it (through the dispatcher). The initial memories are equal
(`initMem_eq`), since the image is exactly the bytes of the placed objects. -/

@[expose] public section

namespace Silmaril.Compile.Mir.LinkCorrect

open Silmaril.Machine
open Silmaril.Compile.Contract
open Silmaril.Compile.Mir.LinkCheck

/-! ## Lists, arrays and frames -/

theorem zip_all_getElem {α β : Type} {p : α × β → Bool} {xs : List α} {ys : List β}
    (h : (xs.zip ys).all p = true) {i : Nat} (hx : i < xs.length) (hy : i < ys.length) :
    p (xs[i], ys[i]) = true := by
  rw [List.all_eq_true] at h
  have hi : i < (xs.zip ys).length := by simp [List.length_zip]; omega
  have := h _ (List.getElem_mem hi)
  simpa [List.getElem_zip] using this

theorem zip_all_mem {α β : Type} {p : α × β → Bool} {xs : List α} {ys : List β}
    (h : (xs.zip ys).all p = true) (hl : ys.length = xs.length) {x : α} (hx : x ∈ xs) :
    ∃ y, p (x, y) = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨_, zip_all_getElem h hi (hl ▸ hi)⟩

/-- Writing `v` at `o + i` for `i < m`, in order. -/
theorem getElem?_foldl_set {α : Type} (o m : Nat) (v : Nat → α) (arr : Array α) (j : Nat) :
    ((List.range m).foldl (fun a i => a.setIfInBounds (o + i) (v i)) arr)[j]? =
      if o ≤ j ∧ j < o + m ∧ j < arr.size then some (v (j - o)) else arr[j]? := by
  induction m with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    rw [ite_eq_right (by omega)]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.getElem?_setIfInBounds, ih]
    have hs : ((List.range m).foldl (fun a i => a.setIfInBounds (o + i) (v i)) arr).size =
        arr.size := by
      clear ih
      induction (List.range m) using List.reverseRecOn with
      | nil => rfl
      | append_singleton xs x ih => simp [List.foldl_append, ih]
    by_cases hj : o + m = j
    · subst hj
      by_cases hlt : o + m < arr.size
      · simp [hs, hlt]
      · simp [hs, hlt]
    · simp only [hj, ite_false]
      by_cases hc : o ≤ j ∧ j < o + m ∧ j < arr.size
      · rw [ite_eq_left hc, ite_eq_left (by omega)]
      · rw [ite_eq_right hc, ite_eq_right (by omega)]

/-- Writing `v` at `o + i` for `i < m`, in order (`Nat.fold`). -/
theorem getElem?_fold_set {α : Type} (o m : Nat) (v : Nat → α) (arr : Array α) (j : Nat) :
    (Nat.fold m (fun i _ a => a.setIfInBounds (o + i) (v i)) arr)[j]? =
      if o ≤ j ∧ j < o + m ∧ j < arr.size then some (v (j - o)) else arr[j]? := by
  rw [Nat.fold_eq_finRange_foldl]
  have : (List.finRange m).foldl (fun acc (x : Fin m) => acc.setIfInBounds (o + x.1) (v x.1)) arr =
      (List.range m).foldl (fun a i => a.setIfInBounds (o + i) (v i)) arr := by
    rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  simp only at this ⊢
  rw [this, getElem?_foldl_set]

theorem size_foldl_set {α : Type} (o : Nat) (v : Nat → α) (arr : Array α) (xs : List Nat) :
    (xs.foldl (fun a i => a.setIfInBounds (o + i) (v i)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp

section Frames

open Lir

theorem writeAll_isSome {fr : Frame Nat} {locs : List (Loc Nat)} {vals : List Word}
    (h : locs.length = vals.length) : (fr.writeAll locs vals).isSome := by
  induction locs generalizing fr vals with
  | nil => cases vals <;> simp_all [Frame.writeAll]
  | cons l ls ih =>
    cases vals with
    | nil => simp at h
    | cons v vs => simpa [Frame.writeAll] using ih (by simpa using h)

theorem writeAll_length {fr fr' : Frame Nat} {locs : List (Loc Nat)} {vals : List Word}
    (h : fr.writeAll locs vals = some fr') : locs.length = vals.length := by
  induction locs generalizing fr vals with
  | nil => cases vals <;> simp_all [Frame.writeAll]
  | cons l ls ih =>
    cases vals with
    | nil => simp [Frame.writeAll] at h
    | cons v vs => simpa using ih (by simpa [Frame.writeAll] using h)

theorem readAll_length {fr : Frame Nat} {locs : List (Loc Nat)} {vals : List Word}
    (h : fr.readAll locs = some vals) : locs.length = vals.length := by
  unfold Frame.readAll at h
  induction locs generalizing vals with
  | nil => simp at h; simp [h]
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : fr.read x <;> simp [hx] at h
    cases hxs : List.mapM fr.read xs <;> simp [hxs] at h
    subst h
    simp [ih hxs]

theorem writeAll_regs_other {fr fr' : Frame Nat} {rs : List Nat} {vals : List Word} {r : Nat}
    (h : fr.writeAll (rs.map .reg) vals = some fr') (hr : r ∉ rs) : fr'.regs r = fr.regs r := by
  induction rs generalizing fr vals with
  | nil => cases vals <;> simp_all [Frame.writeAll]
  | cons x xs ih =>
    cases vals with
    | nil => simp [Frame.writeAll] at h
    | cons v vs =>
      simp only [List.map_cons, Frame.writeAll] at h
      simp only [List.mem_cons, not_or] at hr
      rw [ih h hr.2]
      simp [Frame.write, hr.1]

theorem readAll_writeAll {fr fr' : Frame Nat} {rs : List Nat} {vals : List Word}
    (hn : rs.Nodup) (h : fr.writeAll (rs.map .reg) vals = some fr') :
    fr'.readAll (rs.map .reg) = some vals := by
  induction rs generalizing fr vals with
  | nil => cases vals <;> simp_all [Frame.writeAll, Frame.readAll]
  | cons x xs ih =>
    cases vals with
    | nil => simp [Frame.writeAll] at h
    | cons v vs =>
      simp only [List.map_cons, Frame.writeAll] at h
      rw [List.nodup_cons] at hn
      have h1 := ih hn.2 h
      have h2 := writeAll_regs_other h hn.1
      simp only [Frame.readAll, List.map_cons, List.mapM_cons] at h1 ⊢
      simp [h1, Frame.read, h2, Frame.write]

theorem readAll_set_other {fr : Frame Nat} {rs : List Nat} {r : Nat} {w : Word} (hr : r ∉ rs) :
    (fr.set r w).readAll (rs.map .reg) = fr.readAll (rs.map .reg) := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hr
    simp only [Frame.readAll, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih hr.2]
    have : x ≠ r := fun h => hr.1 h.symm
    simp [Frame.read, this]

theorem readAll_cons_reg {fr : Frame Nat} {t : Nat} {args : List Nat} {v : Word}
    {vals : List Word} (ht : fr.get t = some v) (h : fr.readAll (args.map .reg) = some vals) :
    fr.readAll ((t :: args).map .reg) = some (v :: vals) := by
  simp only [Frame.readAll, List.map_cons, List.mapM_cons] at h ⊢
  simp only [Frame.get] at ht
  simp [Frame.read, ht, h]

theorem readAll_cons_reg_inv {fr : Frame Nat} {t : Nat} {args : List Nat} {vals : List Word}
    (h : fr.readAll ((t :: args).map .reg) = some vals) :
    ∃ v vs, vals = v :: vs ∧ fr.get t = some v ∧ fr.readAll (args.map .reg) = some vs := by
  simp only [Frame.readAll, List.map_cons, List.mapM_cons, Frame.read] at h
  cases hx : fr.regs t with
  | none => simp [hx] at h
  | some v =>
    cases hxs : List.mapM fr.read (args.map .reg) with
    | none => simp [hx, hxs] at h
    | some vs =>
      simp [hx, hxs] at h
      exact ⟨v, vs, h.symm, hx, by simp [Frame.readAll, hxs]⟩

end Frames

/-! ## The facts the check establishes -/

variable (L : Layout) (base : Nat) (us : Array Mir.Unit) (l : Linked)

/-- The instruction check the link check runs. -/
abbrev iok : Instr × Lir.Instr Nat → Bool :=
  instrOK (MirSem.funcDefs us) (MirSem.dataDefs us) (place L l) l
    (dispOK L l (takenLive (MirSem.funcDefs us) l (Std.HashSet.ofList (takenNames us))))

structure Facts : Prop where
  heapFunc : MirSem.funcOf us MirSem.heapSymbol = none
  heapData : MirSem.dataOf us MirSem.heapSymbol = none
  entry : ∀ f, (MirSem.funcDefs us).head? = some f → l.funcs[f.name]? = some 0
  func : ∀ n j, l.funcs[n]? = some j →
    funcEntryOK L (MirSem.funcDefs us) (MirSem.dataDefs us) l (iok L us l) n j = true
  nodup : (l.funcs.toList.map (·.2)).Nodup
  data : ∀ n a, l.data[n]? = some a →
    dataEntryOK (MirSem.funcDefs us) (MirSem.dataDefs us) (place L l) n = true
  placedOK : ∀ x ∈ placed (MirSem.dataDefs us) (place L l), placedOK l (place L l) x = true
  pairwise : (placed (MirSem.dataDefs us) (place L l)).Pairwise fun x y => disjoint x y = true
  dataEnd : l.dataEnd ≤ MirSem.need us base
  image : ∀ k (hk : k < l.image.size),
    (expectedImage (MirSem.funcDefs us) (MirSem.dataDefs us) (place L l) l)[k]? =
      some (BitVec.ofNat 8 (l.image[k]'hk).toNat)

theorem Facts.of_check (h : check L base us l = true) : Facts L base us l := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, ?_, ?_, h5, ?_, h7, h8, h9, ?_⟩
  · intro f hf
    simpa [hf] using h3
  · intro n j hj
    exact h4 (n, j) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hj)
  · intro n a ha
    exact h6 (n, a) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ha)
  · intro k hk
    rw [Nat.all_eq_finRange_all, List.all_eq_true] at h10
    simpa using h10 ⟨k, hk⟩ (List.mem_finRange _)


/-- Lir function `j` of the link implements the Mir function `f`. -/
def Impl (f : Func) (j : Nat) : Prop :=
  ∃ lf, l.prog.funcs[j]? = some lf ∧ funcOK (iok L us l) f lf = true

variable {L base us l}

theorem funcOK_spec {iok : Instr × Lir.Instr Nat → Bool} {f : Func} {lf : Lir.Func Nat}
    (h : funcOK iok f lf = true) :
    lf.params = f.params.map .reg ∧ lf.entry = 0 ∧ lf.blocks.length = f.blocks.size ∧
      (f.blocks.toList.zip lf.blocks).all (blockOK iok) = true := by
  simpa [funcOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using h

theorem blockOK_spec {iok : Instr × Lir.Instr Nat → Bool} {b : Block} {lb : Lir.Block Nat}
    (h : blockOK iok (b, lb) = true) :
    lb.term = b.term ∧ lb.instrs.length = b.instrs.size ∧
      (b.instrs.toList.zip lb.instrs).all iok = true := by
  simpa [blockOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using h

/-- Every instruction of an implemented function passed the instruction check. -/
theorem Impl.instr_mem {f : Func} {j : Nat} (h : Impl L us l f j) {b : Block}
    (hb : b ∈ f.blocks.toList) {i : Instr} (hi : i ∈ b.instrs.toList) :
    ∃ li, iok L us l (i, li) = true := by
  obtain ⟨lf, -, hok⟩ := h
  obtain ⟨-, -, hlen, hall⟩ := funcOK_spec hok
  obtain ⟨lb, hlb⟩ := zip_all_mem hall (by simp [hlen]) hb
  obtain ⟨-, hilen, hiall⟩ := blockOK_spec hlb
  exact zip_all_mem hiall (by simp [hilen]) hi

/-- The fetched Lir code at a point of an implemented function. -/
theorem Impl.fetch {f : Func} {j : Nat} (h : Impl L us l f j) {lab : Nat} {b : Block}
    (hb : f.blocks[lab]? = some b) :
    (∀ i mi, b.instrs[i]? = some mi →
      ∃ li, l.prog.fetch ⟨j, lab, i⟩ = some (.instr li) ∧ iok L us l (mi, li) = true) ∧
    l.prog.fetch ⟨j, lab, b.instrs.size⟩ = some (.term b.term) := by
  obtain ⟨lf, hlf, hok⟩ := h
  obtain ⟨-, -, hlen, hall⟩ := funcOK_spec hok
  obtain ⟨hlab, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  have hlab' : lab < lf.blocks.length := hlen ▸ hlab
  have hbk := zip_all_getElem hall (by simpa using hlab) hlab'
  simp only [Array.getElem_toList] at hbk
  obtain ⟨hterm, hilen, hiall⟩ := blockOK_spec hbk
  have hblock : l.prog.block? j lab = some lf.blocks[lab] := by
    simp [Lir.Prog.block?, Lir.Prog.func?, hlf, hlab']
  refine ⟨fun i mi hmi => ?_, ?_⟩
  · obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hmi
    have hi' : i < lf.blocks[lab].instrs.length := hilen ▸ hi
    refine ⟨_, Lir.Prog.fetch_eq_instr hblock (List.getElem?_eq_getElem hi'), ?_⟩
    have := zip_all_getElem hiall (by simpa using hi) hi'
    simpa using this
  · rw [Lir.Prog.fetch_eq_term hblock (by simp [hilen]), hterm]

theorem funcOf_of_filter {us : Array Mir.Unit} {n : String} {f : Func}
    (h : (MirSem.funcDefs us).filter (·.name == n) = [f]) :
    MirSem.funcOf us n = some f ∧ ∀ g ∈ MirSem.funcDefs us, g.name = n → g = f := by
  refine ⟨?_, fun g hg hn => ?_⟩
  · simp only [MirSem.funcOf, ← List.head?_filter, h, List.head?_cons]
  · have : g ∈ (MirSem.funcDefs us).filter (·.name == n) := by simp [hg, hn]
    simpa [h] using this

/-- An entry of the link's function table. -/
theorem Facts.funcEntry (F : Facts L base us l) {n : String} {j : Nat} (hj : l.funcs[n]? = some j) :
    n ≠ MirSem.heapSymbol ∧ MirSem.dataOf us n = none ∧ 0 < L.funcPtrBase + 16 * j ∧
      L.funcPtrBase + 16 * j < 2 ^ 64 ∧
      ∃ f, MirSem.funcOf us n = some f ∧ (∀ g ∈ MirSem.funcDefs us, g.name = n → g = f) ∧
        Impl L us l f j := by
  have h := F.func n j hj
  simp only [funcEntryOK, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  split at h5
  · rename_i f lf hf hlf
    obtain ⟨hfo, huniq⟩ := funcOf_of_filter hf
    exact ⟨f, hfo, huniq, lf, hlf, h5⟩
  · cases h5

theorem place_data (s : String) :
    (place L l).data s = if s = MirSem.heapSymbol then none else l.data[s]? := rfl

theorem place_func (s : String) :
    (place L l).func s = l.funcs[s]?.map fun i => L.funcPtrBase + 16 * i := rfl

theorem symValue_eq (P : MirSem.Placement) (s : String) :
    LinkCheck.symValue (MirSem.funcDefs us) (MirSem.dataDefs us) P s = MirSem.symValue us P s :=
  rfl

/-- An entry of the link's data table. -/
theorem Facts.dataEntry (F : Facts L base us l) {n : String} {a : Nat} (ha : l.data[n]? = some a)
    (hn : n ≠ MirSem.heapSymbol) :
    MirSem.funcOf us n = none ∧ ∃ d, MirSem.dataOf us n = some d ∧
      ∀ r ∈ d.relocs, (MirSem.symValue us (place L l) r.sym).isSome := by
  have h := F.data n a ha
  simp only [dataEntryOK, Bool.or_eq_true, beq_iff_eq, hn, false_or, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  split at h2
  · rename_i d hd
    simp only [List.all_eq_true] at h2
    exact ⟨d, hd, h2⟩
  · cases h2

/-- Every symbol reachable from the entry has a value. -/
theorem Facts.reach (F : Facts L base us l) {s : String} (h : MirSem.Reach us s) :
    (MirSem.symValue us (place L l) s).isSome := by
  induction h with
  | @entry f hf =>
    have h0 := F.entry f hf
    obtain ⟨hne, hd, -, -, g, hg, -⟩ := F.funcEntry h0
    simp [MirSem.symValue, hne, hd, hg, place_func, h0]
  | @func n s f b i _ hfn hb hi hs ih =>
    -- `n` is a linked function: its instructions passed the check
    have hn : n ≠ MirSem.heapSymbol := by
      rintro rfl; rw [F.heapFunc] at hfn; cases hfn
    simp only [MirSem.symValue, hn, ite_false] at ih
    cases hdn : MirSem.dataOf us n with
    | some d =>
      rw [hdn, place_data, ite_eq_right hn] at ih
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ih
      rw [(F.dataEntry ha hn).1] at hfn; cases hfn
    | none =>
      rw [hdn, hfn] at ih
      simp only [Option.isSome_some, ite_true, place_func, Option.isSome_map] at ih
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp ih
      obtain ⟨-, -, -, -, f', hf', -, himpl⟩ := F.funcEntry hj
      rw [hfn] at hf'; cases hf'
      obtain ⟨li, hli⟩ := himpl.instr_mem hb hi
      cases i with
      | op o => simp [MirSem.instrRefs] at hs
      | fop => simp [MirSem.instrRefs] at hs
      | addr d t off =>
        simp only [MirSem.instrRefs, List.mem_singleton] at hs; subst hs
        simp only [iok, instrOK, symValue_eq] at hli
        split at hli
        · rename_i v hv; simp [hv]
        · cases hli
      | call c args res =>
        simp only [MirSem.instrRefs, List.mem_singleton] at hs; subst hs
        simp only [iok, instrOK] at hli
        split at hli
        · rename_i j' hj'
          obtain ⟨hne, hd, -, -, g, hg, -⟩ := F.funcEntry hj'
          simp [MirSem.symValue, hne, hd, hg, place_func, hj']
        · cases hli
      | callIndirect t args res => simp [MirSem.instrRefs] at hs
  | @data n d r _ hdn hr ih =>
    have hn : n ≠ MirSem.heapSymbol := by
      rintro rfl; rw [F.heapData] at hdn; cases hdn
    simp only [MirSem.symValue, hn, ite_false, hdn, place_data] at ih
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ih
    obtain ⟨-, d', hd', hall⟩ := F.dataEntry ha hn
    rw [hdn] at hd'; cases hd'
    exact hall r hr


theorem pairwise_mem {α : Type} {R : α → α → Prop} {xs : List α} (h : xs.Pairwise R) {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (hne : x ≠ y) : R x y ∨ R y x := by
  induction xs with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact absurd (hx'.trans hy'.symm) hne
    · rw [hx']; exact .inl (h.1 _ hy')
    · rw [hy']; exact .inr (h.1 _ hx')
    · exact ih h.2 hx' hy'

theorem mem_placed {ds : List Data} {P : MirSem.Placement} {d : Data} {a : Nat} (hd : d ∈ ds)
    (ha : P.data d.name = some a) : (d, a) ∈ placed ds P := by
  simp only [placed, List.mem_filterMap]
  exact ⟨d, hd, by simp [ha]⟩

theorem placedOK_spec {P : MirSem.Placement} {x : Data × Nat} (h : placedOK l P x = true) :
    0 < x.2 ∧ x.2 + x.1.size ≤ P.heap ∧ (x.1.align ≤ 1 ∨ x.2 % x.1.align = 0) ∧
      l.dataBase ≤ x.2 ∧ x.2 + x.1.size ≤ l.dataBase + l.image.size := by
  simpa [placedOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, and_assoc]
    using h

theorem disjoint_spec {x y : Data × Nat} (h : disjoint x y = true) :
    x.1.name ≠ y.1.name ∧ (x.2 + x.1.size ≤ y.2 ∨ y.2 + y.1.size ≤ x.2) := by
  simpa [disjoint, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_eq] using h

/-- The placement of the link is valid. -/
theorem Facts.valid (F : Facts L base us l) {memSize : Nat} (hm : MirSem.need us base ≤ memSize) :
    (place L l).Valid us memSize := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hr hd
    have hv := F.reach hr
    have hs : s ≠ MirSem.heapSymbol := by
      rintro rfl; rw [F.heapData] at hd; cases hd
    obtain ⟨d, hd'⟩ := Option.isSome_iff_exists.mp hd
    simpa [MirSem.symValue, hs, hd'] using hv
  · intro s hr hd hf
    have hv := F.reach hr
    have hs : s ≠ MirSem.heapSymbol := by
      rintro rfl; rw [F.heapFunc] at hf; cases hf
    rw [Option.isNone_iff_eq_none] at hd
    simpa [MirSem.symValue, hs, hd, hf] using hv
  · intro d hd a ha
    obtain ⟨h1, h2, h3, -⟩ := placedOK_spec (F.placedOK _ (mem_placed hd ha))
    exact ⟨h1, h2, h3⟩
  · intro d hd d' hd' hne a a' ha ha'
    have hx := mem_placed hd ha
    have hy := mem_placed hd' ha'
    have hxy : (d, a) ≠ (d', a') := fun h => hne (by cases h; rfl)
    rcases pairwise_mem F.pairwise hx hy hxy with h | h
    · exact (disjoint_spec h).2
    · exact (disjoint_spec h).2.symm
  · exact Nat.le_trans F.dataEnd hm
  · intro s a ha
    simp only [place_func, Option.map_eq_some_iff] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨-, -, h1, h2, -⟩ := F.funcEntry hj
    exact ⟨h1, h2⟩
  · intro s s' a ha ha'
    simp only [place_func, Option.map_eq_some_iff] at ha ha'
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨j', hj', hjj⟩ := ha'
    have : j' = j := by omega
    subst this
    have h1 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hj
    have h2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hj'
    have := List.inj_on_of_nodup_map F.nodup h1 h2 rfl
    cases this; rfl

/-! ## The initial memory -/

theorem foldl_relocs (fs : List Func) (ds : List Data) (P : MirSem.Placement) (size : Nat)
    (rs : List Reloc) (arr : Array (BitVec 8)) (g : Nat → BitVec 8) (hs : arr.size = size)
    (hg : ∀ j < size, arr[j]? = some (g j)) :
    (rs.foldl (fun arr r =>
      (List.range 8).foldl (fun arr i =>
        arr.setIfInBounds (r.offset + i) (LittleEndian.wordByte (relocWord fs ds P r) i)) arr)
      arr).size = size ∧ ∀ j < size,
    (rs.foldl (fun arr r =>
      (List.range 8).foldl (fun arr i =>
        arr.setIfInBounds (r.offset + i) (LittleEndian.wordByte (relocWord fs ds P r) i)) arr)
      arr)[j]? = some (rs.foldl (fun acc r j =>
        if r.offset ≤ j ∧ j < r.offset + 8 then
          LittleEndian.wordByte (relocWord fs ds P r) (j - r.offset)
        else acc j) g j) := by
  induction rs generalizing arr g with
  | nil => exact ⟨hs, hg⟩
  | cons r rs ih =>
    simp only [List.foldl_cons]
    refine ih _ _ (by rw [size_foldl_set, hs]) ?_
    intro j hj
    rw [getElem?_foldl_set]
    by_cases hc : r.offset ≤ j ∧ j < r.offset + 8
    · rw [ite_eq_left ⟨hc.1, hc.2, hs ▸ hj⟩, ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc, hg j hj]

theorem objectBytes_get (fs : List Func) (ds : List Data) (P : MirSem.Placement) (d : Data)
    {j : Nat} (hj : j < d.size) :
    (objectBytes fs ds P d)[j]? = some (d.relocs.foldl (fun acc r j =>
        if r.offset ≤ j ∧ j < r.offset + 8 then
          LittleEndian.wordByte (relocWord fs ds P r) (j - r.offset)
        else acc j)
        (fun j => if h : j < d.init.size then BitVec.ofNat 8 d.init[j].toNat else 0) j) := by
  unfold objectBytes
  refine (foldl_relocs fs ds P d.size d.relocs _ _ (by simp) ?_).2 j hj
  intro j hj
  simp [hj]

theorem objectBytes_size (fs : List Func) (ds : List Data) (P : MirSem.Placement) (d : Data) :
    (objectBytes fs ds P d).size = d.size := by
  unfold objectBytes
  refine (foldl_relocs fs ds P d.size d.relocs _
    (fun j => if h : j < d.init.size then BitVec.ofNat 8 d.init[j].toNat else 0) (by simp) ?_).1
  intro j hj
  simp [hj]


theorem writeObject_get (img : Array (BitVec 8)) (off size : Nat) (bs : Array (BitVec 8))
    (k : Nat) : (writeObject img off size bs)[k]? =
      if off ≤ k ∧ k < off + size ∧ k < img.size then some (bs[k - off]?.getD 0) else img[k]? :=
  getElem?_fold_set off size (fun j => bs[j]?.getD 0) img k

theorem writeObject_size (img : Array (BitVec 8)) (off size : Nat) (bs : Array (BitVec 8)) :
    (writeObject img off size bs).size = img.size := by
  unfold writeObject
  rw [Nat.fold_eq_finRange_foldl]
  generalize List.finRange size = xs
  induction xs generalizing img with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp

/-- Whether placed object `x` covers address `a`. -/
def covers (a : Nat) (x : Data × Nat) : Bool := decide (x.2 ≤ a ∧ a < x.2 + x.1.size)

theorem foldl_writeObject (fs : List Func) (ds : List Data) (P : MirSem.Placement) (db : Nat)
    (xs : List (Data × Nat)) (img : Array (BitVec 8))
    (hpw : xs.Pairwise fun x y => disjoint x y = true)
    (hin : ∀ x ∈ xs, db ≤ x.2 ∧ x.2 + x.1.size ≤ db + img.size) {k : Nat} (hk : k < img.size) :
    (xs.foldl (fun img x => writeObject img (x.2 - db) x.1.size (objectBytes fs ds P x.1)) img)[k]? =
      match xs.find? (covers (db + k)) with
      | some x => some ((objectBytes fs ds P x.1)[db + k - x.2]?.getD 0)
      | none => img[k]? := by
  induction xs generalizing img with
  | nil => rfl
  | cons x xs ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.foldl_cons]
    have hin' : ∀ y ∈ xs, db ≤ y.2 ∧ y.2 + y.1.size ≤ db +
        (writeObject img (x.2 - db) x.1.size (objectBytes fs ds P x.1)).size := by
      intro y hy; rw [writeObject_size]; exact hin y (List.mem_cons_of_mem _ hy)
    rw [ih _ hpw.2 hin' (by rw [writeObject_size]; exact hk), List.find?_cons]
    have hx := hin x (List.mem_cons_self ..)
    by_cases hc : covers (db + k) x = true
    · have hnone : xs.find? (covers (db + k)) = none := by
        rw [List.find?_eq_none]
        intro y hy hcy
        have hd := (disjoint_spec (hpw.1 y hy)).2
        simp only [covers, decide_eq_true_eq] at hc hcy
        omega
      have hc' := hc
      simp only [covers, decide_eq_true_eq] at hc'
      simp only [hnone, hc]
      rw [writeObject_get, ite_eq_left (by omega), show k - (x.2 - db) = db + k - x.2 by omega]
    · simp only [Bool.not_eq_true] at hc
      have hc' := hc
      simp only [covers, decide_eq_false_iff_not] at hc'
      simp only [hc]
      cases xs.find? (covers (db + k)) with
      | some y => rfl
      | none =>
        simp only
        rw [writeObject_get, ite_eq_right (by omega)]

theorem Facts.find_covers (F : Facts L base us l) {a : Nat} {x : Data × Nat}
    (hx : x ∈ placed (MirSem.dataDefs us) (place L l)) (hc : covers a x = true) :
    (placed (MirSem.dataDefs us) (place L l)).find? (covers a) = some x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨x, hx, hc⟩ : ((placed (MirSem.dataDefs us) (place L l)).find?
      (covers a)).isSome)
  rw [hy]
  have hym := List.mem_of_find?_eq_some hy
  have hyc := List.find?_some hy
  by_contra hne
  have hne' : y ≠ x := fun h => hne (by rw [h])
  simp only [covers, decide_eq_true_eq] at hc hyc
  rcases pairwise_mem F.pairwise hym hx hne' with h | h <;>
    · have := (disjoint_spec h).2; omega

/-- The initial memory of `MirSem` under the link's placement is the linked image. -/
theorem Facts.initMem_eq (F : Facts L base us l) (memSize : Nat) :
    MirSem.initMem us (place L l) memSize = linkedMem l memSize := by
  unfold MirSem.initMem linkedMem
  congr 1
  funext a
  have himg := fun k (hk : k < (Array.replicate l.image.size (0 : BitVec 8)).size) =>
    foldl_writeObject (MirSem.funcDefs us) (MirSem.dataDefs us) (place L l)
    l.dataBase (placed (MirSem.dataDefs us) (place L l)) (Array.replicate l.image.size 0)
    F.pairwise (fun x hx => by
      obtain ⟨-, -, -, h1, h2⟩ := placedOK_spec (F.placedOK x hx)
      exact ⟨h1, by simpa using h2⟩) hk
  have hexp := F.image
  unfold expectedImage at hexp
  split
  · next d hq =>
    have hd := List.find?_some hq
    have hmem := List.mem_of_find?_eq_some hq
    cases hb : (place L l).data d.name with
    | none => rw [hb] at hd; cases hd
    | some b =>
      rw [hb] at hd
      simp only [decide_eq_true_eq] at hd
      have hpl := mem_placed hmem hb
      have hfind := F.find_covers (a := a) hpl (by simp [covers, hd])
      obtain ⟨-, -, -, h1, h2⟩ := placedOK_spec (F.placedOK _ hpl)
      simp only at h1 h2
      rw [Option.getD_some, dite_eq_left (by omega)]
      have := himg (a - l.dataBase) (by simp; omega)
      rw [show l.dataBase + (a - l.dataBase) = a by omega, hfind] at this
      rw [hexp _ (by omega)] at this
      simp only [Option.some.injEq] at this
      rw [this, objectBytes_get _ _ _ _ (by omega)]
      rfl
  · next hq =>
    have hfind : (placed (MirSem.dataDefs us) (place L l)).find? (covers a) = none := by
      rw [List.find?_eq_none]
      intro x hx hc
      obtain ⟨d, hd, hdx⟩ := List.mem_filterMap.mp hx
      cases hb : (place L l).data d.name with
      | none => rw [hb] at hdx; cases hdx
      | some b =>
        rw [hb] at hdx
        cases hdx
        have := List.find?_eq_none.mp hq d hd
        rw [hb] at this
        simp only [covers, decide_eq_true_eq] at hc this
        exact this hc
    split
    · rename_i h
      have := himg (a - l.dataBase) (by simpa using (by omega : a - l.dataBase < l.image.size))
      rw [show l.dataBase + (a - l.dataBase) = a by omega, hfind] at this
      rw [hexp _ (by omega)] at this
      rw [Array.getElem?_replicate, ite_eq_left (by omega)] at this
      simp only [Option.some.injEq] at this
      rw [← this]
    · rfl


/-! ## Dispatchers -/

/-- The argument registers of a dispatcher's call. -/
def dargs (n : Nat) : List (Lir.Loc Nat) := (List.range n).map fun j => .reg (j + 1)

/-- The result registers of a dispatcher's call. -/
def dres (n r : Nat) : List (Lir.Loc Nat) := (List.range r).map fun j => .reg (n + 3 + j)

theorem flatMap_zipIdx_get {α β : Type} (F : α × Nat → List β) (g : α → Nat → β)
    (h : α → Nat → β) (hF : ∀ x i, F (x, i) = [g x i, h x i]) (xs : List α) (s i : Nat)
    (hi : i < xs.length) :
    ((xs.zipIdx s).flatMap F)[2 * i]? = some (g xs[i] (s + i)) ∧
      ((xs.zipIdx s).flatMap F)[2 * i + 1]? = some (h xs[i] (s + i)) := by
  induction xs generalizing s i with
  | nil => cases hi
  | cons x xs ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, hF]
    cases i with
    | zero => simp
    | succ i =>
      have := ih (s + 1) i (by simpa using hi)
      rw [show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by omega]
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      rw [show s + (i + 1) = s + 1 + i by omega]
      exact this

theorem length_flatMap_zipIdx {α β : Type} (F : α × Nat → List β) (g : α → Nat → β)
    (h : α → Nat → β) (hF : ∀ x i, F (x, i) = [g x i, h x i]) (xs : List α) (s : Nat) :
    ((xs.zipIdx s).flatMap F).length = 2 * xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.zipIdx_cons, List.flatMap_cons, hF]; simp [ih]; omega

theorem dispatcher_blocks (n r : Nat) (cands : List (Nat × Nat)) (i : Nat)
    (hi : i < cands.length) :
    (dispatcher n r cands).blocks[2 * i]? =
        some ⟨[.op (.const (n + 1) (BitVec.ofNat 64 cands[i].2)),
          .op (.binary (.cmp .eq) (n + 2) 0 (n + 1))], .branch (n + 2) (2 * i + 1) (2 * i + 2)⟩ ∧
      (dispatcher n r cands).blocks[2 * i + 1]? =
        some ⟨[.call cands[i].1 (dargs n) (dres n r)], .ret (dres n r)⟩ := by
  let F : (Nat × Nat) × Nat → List (Lir.Block Nat) := fun x =>
    [⟨[.op (.const (n + 1) (BitVec.ofNat 64 x.1.2)), .op (.binary (.cmp .eq) (n + 2) 0 (n + 1))],
        .branch (n + 2) (2 * x.2 + 1) (2 * x.2 + 2)⟩,
      ⟨[.call x.1.1 (dargs n) (dres n r)], .ret (dres n r)⟩]
  have hb : (dispatcher n r cands).blocks = (cands.zipIdx.flatMap F) ++ [⟨[], .trap⟩] := rfl
  have hF : ∀ x i, F (x, i) = [_, _] := fun x i => rfl
  have hlen := length_flatMap_zipIdx F _ _ hF cands 0
  obtain ⟨h1, h2⟩ := flatMap_zipIdx_get F _ _ hF cands 0 i hi
  rw [hb, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  simp only [Nat.zero_add] at h1 h2
  exact ⟨h1, h2⟩


theorem dargs_eq (n : Nat) : dargs n = ((List.range n).map (· + 1)).map .reg := by
  simp [dargs, List.map_map, Function.comp_def]

theorem dres_eq (n r : Nat) : dres n r = ((List.range r).map (n + 3 + ·)).map .reg := by
  simp [dres, List.map_map, Function.comp_def]

theorem dframe_regs0 (fr : Lir.Frame Nat) (n : Nat) (a b : Lir.Word) :
    ((fr.set (n + 1) a).set (n + 2) b).regs 0 = fr.regs 0 := by
  simp

theorem dframe_args (fr : Lir.Frame Nat) (n : Nat) (a b : Lir.Word) :
    ((fr.set (n + 1) a).set (n + 2) b).readAll (dargs n) = fr.readAll (dargs n) := by
  rw [dargs_eq, readAll_set_other (by simp), readAll_set_other (by simp)]

/-- One candidate of a dispatcher: compare the pointer, branch. -/
theorem dispatch_cand {k n r : Nat} {cands : List (Nat × Nat)}
    (hk : l.prog.funcs[k]? = some (dispatcher n r cands)) {i : Nat} (hi : i < cands.length)
    {fr : Lir.Frame Nat} {v : Lir.Word} (hv : fr.regs 0 = some v)
    (st : List (Lir.Activation Nat)) (mem : Lir.Memory) :
    Relation.TransGen (Lir.Step l.prog) ⟨⟨k, 2 * i, 0⟩, fr, st, mem⟩
      ⟨⟨k, if v = BitVec.ofNat 64 cands[i].2 then 2 * i + 1 else 2 * i + 2, 0⟩,
        (fr.set (n + 1) (BitVec.ofNat 64 cands[i].2)).set (n + 2)
          (Lir.ofBool (v == BitVec.ofNat 64 cands[i].2)), st, mem⟩ := by
  obtain ⟨h1, -⟩ := dispatcher_blocks n r cands i hi
  have hblk : l.prog.block? k (2 * i) = some ⟨[.op (.const (n + 1) (BitVec.ofNat 64 cands[i].2)),
      .op (.binary (.cmp .eq) (n + 2) 0 (n + 1))], .branch (n + 2) (2 * i + 1) (2 * i + 2)⟩ := by
    simp only [Lir.Prog.block?, Lir.Prog.func?, hk, Option.bind_some, h1]
  have s1 : Lir.Step l.prog ⟨⟨k, 2 * i, 0⟩, fr, st, mem⟩
      ⟨⟨k, 2 * i, 1⟩, fr.set (n + 1) (BitVec.ofNat 64 cands[i].2), st, mem⟩ :=
    (Lir.Transition.op (Lir.Prog.fetch_eq_instr hblk rfl) rfl).step_eq
  have s2 : Lir.Step l.prog ⟨⟨k, 2 * i, 1⟩, fr.set (n + 1) (BitVec.ofNat 64 cands[i].2), st, mem⟩
      ⟨⟨k, 2 * i, 2⟩, (fr.set (n + 1) (BitVec.ofNat 64 cands[i].2)).set (n + 2)
          (Lir.ofBool (v == BitVec.ofNat 64 cands[i].2)), st, mem⟩ :=
    (Lir.Transition.op (Lir.Prog.fetch_eq_instr hblk rfl)
      (by simp [Lir.Op.exec, Lir.Frame.get, hv, Lir.Binop.eval, Lir.Cond.eval])).step_eq
  have hf3 : l.prog.fetch ⟨k, 2 * i, 2⟩ = some (.term (.branch (n + 2) (2 * i + 1) (2 * i + 2))) :=
    Lir.Prog.fetch_eq_term (pt := ⟨k, 2 * i, 2⟩) hblk rfl
  have s3 := (Lir.Transition.branch (p := l.prog) (c := n + 2) (l₁ := 2 * i + 1)
      (l₂ := 2 * i + 2) (x := Lir.ofBool (v == BitVec.ofNat 64 cands[i].2))
      (s := ⟨⟨k, 2 * i, 2⟩, (fr.set (n + 1)
      (BitVec.ofNat 64 cands[i].2)).set (n + 2) (Lir.ofBool (v == BitVec.ofNat 64 cands[i].2)),
      st, mem⟩) hf3 (by simp [Lir.Frame.get])).step_eq
  have hlab : (if Lir.ofBool (v == BitVec.ofNat 64 cands[i].2) = 0 then 2 * i + 2 else 2 * i + 1) =
      (if v = BitVec.ofNat 64 cands[i].2 then 2 * i + 1 else 2 * i + 2) := by
    by_cases hc : v = BitVec.ofNat 64 cands[i].2 <;> simp [hc, Lir.ofBool]
  rw [hlab] at s3
  exact .tail (.tail (.single s1) s2) s3

/-- A dispatcher runs its comparisons until a candidate matches. -/
theorem dispatch_loop {k n r : Nat} {cands : List (Nat × Nat)}
    (hk : l.prog.funcs[k]? = some (dispatcher n r cands)) {v : Lir.Word} {ig : Nat}
    (hfirst : ∀ m (hm : m < cands.length), BitVec.ofNat 64 cands[m].2 = v → cands[m].1 = ig)
    (st : List (Lir.Activation Nat)) (mem : Lir.Memory) {vals : List Lir.Word} :
    ∀ d i (fr : Lir.Frame Nat), cands.length - i = d →
      (∃ m, ∃ _ : m < cands.length, i ≤ m ∧ BitVec.ofNat 64 cands[m].2 = v) →
      fr.regs 0 = some v → fr.readAll (dargs n) = some vals →
      ∃ m fr', ∃ hm : m < cands.length, cands[m].1 = ig ∧ fr'.readAll (dargs n) = some vals ∧
        Relation.TransGen (Lir.Step l.prog) ⟨⟨k, 2 * i, 0⟩, fr, st, mem⟩
          ⟨⟨k, 2 * m + 1, 0⟩, fr', st, mem⟩ := by
  intro d
  induction d with
  | zero =>
    intro i fr hd hex
    obtain ⟨m, hm, him, -⟩ := hex
    omega
  | succ d ih =>
    intro i fr hd hex hv hvals
    have hi : i < cands.length := by obtain ⟨m, hm, him, -⟩ := hex; omega
    have hstep := dispatch_cand hk hi hv st mem
    by_cases hc : v = BitVec.ofNat 64 cands[i].2
    · rw [ite_eq_left hc] at hstep
      exact ⟨i, _, hi, hfirst i hi hc.symm, by rw [dframe_args]; exact hvals, hstep⟩
    · rw [ite_eq_right hc] at hstep
      obtain ⟨m, hm, him, hmv⟩ := hex
      have him' : i + 1 ≤ m := by
        rcases Nat.lt_or_eq_of_le him with h | h
        · omega
        · subst h; exact absurd hmv.symm hc
      obtain ⟨m', fr'', hm', hig, hvals', hsteps⟩ := ih (i + 1)
        ((fr.set (n + 1) (BitVec.ofNat 64 cands[i].2)).set (n + 2)
          (Lir.ofBool (v == BitVec.ofNat 64 cands[i].2))) (by omega) ⟨m, hm, him', hmv⟩
        (by rw [dframe_regs0]; exact hv) (by rw [dframe_args]; exact hvals)
      rw [show 2 * (i + 1) = 2 * i + 2 by omega] at hsteps
      exact ⟨m', fr'', hm', hig, hvals', hstep.trans hsteps⟩


/-! ## Indirect calls -/

theorem target_spec {P : MirSem.Placement} {v : Lir.Word} {n r : Nat} {g : Func}
    (h : MirSem.target us P v n r = some g) :
    g ∈ MirSem.funcDefs us ∧ MirSem.taken us g.name = true ∧
      (∃ a, P.func g.name = some a ∧ BitVec.ofNat 64 a = v) ∧ g.params.length = n ∧
      g.results = r := by
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨ht, hf⟩, hn⟩, hr⟩ := hp
  refine ⟨hm, ht, ?_, hn, hr⟩
  revert hf
  cases P.func g.name with
  | none => intro hf; cases hf
  | some a => intro hf; exact ⟨a, rfl, by simpa using hf⟩

theorem mem_takenNames {n : String} (h : MirSem.taken us n = true) : n ∈ takenNames us := by
  simp only [MirSem.taken, Array.any_eq_true', Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨u, hu, hf | hd⟩ := h
  · obtain ⟨f, hf, b, hb, i, hi, hs⟩ := hf
    simp only [takenNames, List.mem_flatMap, List.mem_append, List.mem_filterMap]
    refine ⟨u, Array.mem_toList_iff.mpr hu, .inl ⟨f, Array.mem_toList_iff.mpr hf, b,
      Array.mem_toList_iff.mpr hb, i, Array.mem_toList_iff.mpr hi, ?_⟩⟩
    split at hs
    · simpa using hs
    · cases hs
  · obtain ⟨d, hd, r, hr, hs⟩ := hd
    simp only [takenNames, List.mem_flatMap, List.mem_append, List.mem_map]
    exact ⟨u, Array.mem_toList_iff.mpr hu, .inr ⟨d, Array.mem_toList_iff.mpr hd, r, hr,
      by simpa using hs⟩⟩

/-- What a checked dispatcher call gives: the dispatcher, the Lir function of the Mir
target, and a candidate with its pointer, the only one. -/
theorem Facts.dispatch (F : Facts L base us l) {k n r : Nat}
    (hd : dispOK L l (takenLive (MirSem.funcDefs us) l (Std.HashSet.ofList (takenNames us)))
      k n r = true)
    {v : Lir.Word} {g : Func} (hg : MirSem.target us (place L l) v n r = some g) :
    ∃ cands ig, l.prog.funcs[k]? = some (dispatcher n r cands) ∧ Impl L us l g ig ∧
      (∀ m (hm : m < cands.length), BitVec.ofNat 64 cands[m].2 = v → cands[m].1 = ig) ∧
      (∃ m, ∃ _ : m < cands.length, 0 ≤ m ∧ BitVec.ofNat 64 cands[m].2 = v) := by
  obtain ⟨hgm, htaken, ⟨a, ha, hav⟩, hn, hr⟩ := target_spec hg
  simp only [place_func, Option.map_eq_some_iff] at ha
  obtain ⟨ig, hig, rfl⟩ := ha
  obtain ⟨-, -, -, hbound, f, hf, huniq, himpl⟩ := F.funcEntry hig
  have hfg : g = f := huniq g hgm rfl
  subst hfg
  unfold dispOK at hd
  split at hd
  · cases hd
  · rename_i fn hfn
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
      Bool.or_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨⟨hdisp, hcands⟩, htl⟩ := hd
    refine ⟨candsOf fn.blocks, ig, hdisp ▸ hfn, himpl, ?_, ?_⟩
    · intro m hm hmv
      obtain ⟨h1, h2⟩ := hcands _ (List.getElem_mem hm)
      rw [← hav, h1] at hmv
      have := congrArg BitVec.toNat hmv
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h1 ▸ h2),
        Nat.mod_eq_of_lt hbound] at this
      omega
    · have hmem : (ig, g.params.length, g.results) ∈
          takenLive (MirSem.funcDefs us) l (Std.HashSet.ofList (takenNames us)) := by
        simp only [takenLive, List.mem_filterMap]
        refine ⟨(g.name, ig), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hig, ?_⟩
        have hc : (Std.HashSet.ofList (takenNames us)).contains g.name = true := by
          rw [Std.HashSet.contains_ofList, List.contains_iff_mem]
          exact mem_takenNames htaken
        simp only [hc, ite_true]
        show (MirSem.funcOf us g.name).map _ = _
        rw [hf]; rfl
      have := htl _ hmem
      simp only [hn, hr, beq_self_eq_true, Bool.and_self, Bool.true_eq_false, false_or] at this
      obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem this
      exact ⟨m, hm, Nat.zero_le _, by rw [hmeq, ← hav]⟩


/-! ## The simulation -/

variable (L us l) in
/-- A suspended Mir caller and the Lir point of its call. -/
def CallerOK (a : MirSem.Act) (j : Nat) : Prop :=
  Impl L us l a.func j ∧ ∃ f args,
    l.prog.fetch ⟨j, a.label, a.index⟩ = some (.instr (.call f args (a.results.map .reg)))

variable (l) in
/-- Label `lab` of Lir function `k` is the call block of a dispatcher with `r` results. -/
def DispAt (k lab r : Nat) : Prop :=
  ∃ n fid, l.prog.fetch ⟨k, lab, 0⟩ = some (.instr (.call fid (dargs n) (dres n r))) ∧
    l.prog.fetch ⟨k, lab, 1⟩ = some (.term (.ret (dres n r)))

variable (L us l) in
/-- The Mir call stack and the Lir one: a direct call is one activation, an indirect call
two (the caller's and the dispatcher's). -/
inductive StackRel : List MirSem.Act → List (Lir.Activation Nat) → Prop
  | nil : StackRel [] []
  | direct {a : MirSem.Act} {as : List MirSem.Act} {ts : List (Lir.Activation Nat)} {j : Nat} :
      CallerOK L us l a j → StackRel as ts →
      StackRel (a :: as) (⟨⟨j, a.label, a.index⟩, a.frame⟩ :: ts)
  | indirect {a : MirSem.Act} {as : List MirSem.Act} {ts : List (Lir.Activation Nat)}
      {j k lab : Nat} {dfr : Lir.Frame Nat} :
      CallerOK L us l a j → DispAt l k lab a.results.length → StackRel as ts →
      StackRel (a :: as) (⟨⟨k, lab, 0⟩, dfr⟩ :: ⟨⟨j, a.label, a.index⟩, a.frame⟩ :: ts)

variable (L us l) in
/-- A Mir state and the Lir state at the same point of the implementing function. -/
def Rel (s : MirSem.State) (t : Lir.State Nat) : Prop :=
  ∃ j, Impl L us l s.func j ∧ t.point = ⟨j, s.label, s.index⟩ ∧ t.frame = s.frame ∧
    t.mem = s.mem ∧ StackRel L us l s.stack t.stack

variable (L us l) in
/-- What a Mir step result asks of the related Lir state. -/
def ResRel : MirSem.Result → Lir.State Nat → Prop
  | .running s', t => ∃ t', Relation.TransGen (Lir.Step l.prog) t t' ∧ Rel L us l s' t'
  | .returned vs m, t => Lir.step l.prog t = .returned vs m
  | .trapped m, t => Lir.step l.prog t = .trapped m
  | .stuck, _ => True

theorem enter_eq {f : Func} {j : Nat} (h : Impl L us l f j) {vals : List Lir.Word}
    {fr : Lir.Frame Nat} (he : MirSem.enter f vals = some fr) :
    l.prog.enter j vals = some (⟨j, 0, 0⟩, fr) := by
  obtain ⟨lf, hlf, hok⟩ := h
  obtain ⟨hp, he0, -⟩ := funcOK_spec hok
  simp only [MirSem.enter] at he
  simp [Lir.Prog.enter, Lir.Prog.func?, hlf, hp, he0, he]

theorem dispatcher_enter {n : Nat} {v : Lir.Word} {vals : List Lir.Word}
    (hlen : vals.length = n) :
    ∃ dfr, Lir.Frame.empty.writeAll ((List.range (n + 1)).map .reg) (v :: vals) = some dfr ∧
      dfr.regs 0 = some v ∧ dfr.readAll (dargs n) = some vals := by
  have hs := writeAll_isSome (fr := Lir.Frame.empty)
    (locs := (List.range (n + 1)).map .reg) (vals := v :: vals) (by simp [hlen])
  obtain ⟨dfr, hdfr⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨dfr, hdfr, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons] at hdfr
    simp only [Lir.Frame.writeAll] at hdfr
    rw [writeAll_regs_other hdfr (by simp)]
    simp [Lir.Frame.write]
  · rw [List.range_succ_eq_map, List.map_cons] at hdfr
    simp only [Lir.Frame.writeAll] at hdfr
    rw [dargs_eq]
    exact readAll_writeAll (List.nodup_range.map Nat.succ_injective) hdfr


/-- **One Mir step is matched.** -/
theorem Facts.sim (F : Facts L base us l) {s : MirSem.State} {t : Lir.State Nat}
    (hr : Rel L us l s t) : ResRel L us l (MirSem.step us (place L l) s) t := by
  obtain ⟨j, himpl, hpt, hfr, hmem, hstk⟩ := hr
  obtain ⟨tp, tfr, tst, tmem⟩ := t
  simp only at hpt hfr hmem
  subst hpt hfr hmem
  unfold MirSem.step
  cases hb : s.func.blocks[s.label]? with
  | none => trivial
  | some b =>
    obtain ⟨hinstr, hterm⟩ := himpl.fetch hb
    try simp only []
    cases hi : b.instrs[s.index]? with
    | some mi =>
      obtain ⟨li, hfetch, hok⟩ := hinstr _ _ hi
      cases mi with
      | op o =>
        try simp only []
        simp only [iok, instrOK, decide_eq_true_eq] at hok
        subst hok
        cases he : o.exec s.frame s.mem with
        | none => trivial
        | some p =>
          try simp only []
          obtain ⟨fr, m⟩ := p
          exact ⟨_, .single (Lir.Transition.op hfetch he).step_eq, j, himpl, rfl, rfl, rfl, hstk⟩
      | fop op d x y =>
        try simp only []
        simp only [iok, instrOK, decide_eq_true_eq] at hok
        subst hok
        cases he : Lir.FOp.exec op d x y s.frame with
        | none => trivial
        | some fr =>
          try simp only []
          exact ⟨_, .single (Lir.Transition.fop hfetch he).step_eq, j, himpl, rfl, rfl, rfl, hstk⟩
      | addr d sym off =>
        try simp only []
        simp only [iok, instrOK, symValue_eq] at hok
        cases hv : MirSem.symValue us (place L l) sym with
        | none => trivial
        | some v =>
          try simp only []
          rw [hv] at hok
          simp only [decide_eq_true_eq] at hok
          subst hok
          exact ⟨_, .single (Lir.Transition.op hfetch rfl).step_eq, j, himpl, rfl, rfl, rfl, hstk⟩
      | call c args res =>
        try simp only []
        simp only [iok, instrOK] at hok
        split at hok
        · rename_i j' hj'
          simp only [decide_eq_true_eq] at hok
          subst hok
          obtain ⟨-, -, -, -, f', hf', -, himpl'⟩ := F.funcEntry hj'
          rw [hf']
          cases hvals : s.frame.readAll (args.map .reg) with
          | none => trivial
          | some vals =>
            try simp only []
            try simp only [MirSem.call]
            cases henter : MirSem.enter f' vals with
            | none => trivial
            | some fr =>
              try simp only []
              exact ⟨_, .single (Lir.Transition.call hfetch hvals (enter_eq himpl' henter)).step_eq,
                j', himpl', rfl, rfl, rfl, .direct ⟨himpl, _, _, hfetch⟩ hstk⟩
        · cases hok
      | callIndirect tr args res =>
        try simp only []
        simp only [iok, instrOK] at hok
        split at hok
        · rename_i k a' r'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨rfl, rfl⟩, hd⟩ := hok
          cases hv : s.frame.get tr with
          | none => trivial
          | some v =>
            cases hvals : s.frame.readAll (args.map .reg) with
            | none => trivial
            | some vals =>
              try simp only []
              cases htg : MirSem.target us (place L l) v args.length res.length with
              | none => trivial
              | some g =>
                try simp only []
                try simp only [MirSem.call]
                cases henter : MirSem.enter g vals with
                | none => trivial
                | some fr =>
                  try simp only []
                  obtain ⟨cands, ig, hk, himplg, hfirst, hex⟩ := F.dispatch hd htg
                  have hlen := (readAll_length hvals).symm
                  simp only [List.length_map] at hlen
                  obtain ⟨dfr, hdfr, hd0, hdargs⟩ := dispatcher_enter (v := v) hlen
                  -- call the dispatcher
                  have s1 : Lir.Step l.prog ⟨⟨j, s.label, s.index⟩, s.frame, tst, s.mem⟩
                      ⟨⟨k, 0, 0⟩, dfr, ⟨⟨j, s.label, s.index⟩, s.frame⟩ :: tst, s.mem⟩ := by
                    refine (Lir.Transition.call hfetch (readAll_cons_reg hv hvals) ?_).step_eq
                    simp [Lir.Prog.enter, Lir.Prog.func?, hk, dispatcher, hdfr]
                  -- compare until the target's candidate
                  obtain ⟨m, fr', hm, hig, hvals', hloop⟩ := dispatch_loop hk hfirst
                    (⟨⟨j, s.label, s.index⟩, s.frame⟩ :: tst) s.mem _ 0 dfr rfl hex hd0 hdargs
                  simp only [Nat.mul_zero] at hloop
                  -- call the target
                  obtain ⟨-, h2⟩ := dispatcher_blocks args.length res.length cands m hm
                  have hblk : l.prog.block? k (2 * m + 1) = some ⟨[.call cands[m].1
                      (dargs args.length) (dres args.length res.length)],
                      .ret (dres args.length res.length)⟩ := by
                    simp only [Lir.Prog.block?, Lir.Prog.func?, hk, Option.bind_some, h2]
                  have hf0 : l.prog.fetch ⟨k, 2 * m + 1, 0⟩ = some (.instr (.call cands[m].1
                      (dargs args.length) (dres args.length res.length))) :=
                    Lir.Prog.fetch_eq_instr hblk rfl
                  have hf1 : l.prog.fetch ⟨k, 2 * m + 1, 1⟩ =
                      some (.term (.ret (dres args.length res.length))) :=
                    Lir.Prog.fetch_eq_term (pt := ⟨k, 2 * m + 1, 1⟩) hblk rfl
                  have s3 : Lir.Step l.prog
                      ⟨⟨k, 2 * m + 1, 0⟩, fr', ⟨⟨j, s.label, s.index⟩, s.frame⟩ :: tst, s.mem⟩
                      ⟨⟨ig, 0, 0⟩, fr, ⟨⟨k, 2 * m + 1, 0⟩, fr'⟩ ::
                        ⟨⟨j, s.label, s.index⟩, s.frame⟩ :: tst, s.mem⟩ := by
                    refine (Lir.Transition.call hf0 hvals' ?_).step_eq
                    rw [hig]
                    exact enter_eq himplg henter
                  exact ⟨_, .head s1 (hloop.tail s3), ig, himplg, rfl, rfl, rfl,
                    .indirect ⟨himpl, _, _, hfetch⟩ ⟨args.length, cands[m].1, hf0, hf1⟩ hstk⟩
        · cases hok
    | none =>
      try simp only []
      by_cases hix : s.index = b.instrs.size
      · rw [ite_eq_right (not_not.mpr hix)]
        rw [← hix] at hterm
        cases hbt : b.term with
        | jump l' =>
          rw [hbt] at hterm
          simp only []
          exact ⟨_, .single (Lir.Transition.jump hterm).step_eq, j, himpl, rfl, rfl, rfl, hstk⟩
        | branch c l₁ l₂ =>
          rw [hbt] at hterm
          simp only []
          cases hc : s.frame.get c with
          | none => trivial
          | some x =>
            try simp only []
            exact ⟨_, .single (Lir.Transition.branch hterm hc).step_eq, j, himpl, rfl, rfl, rfl,
              hstk⟩
        | ret locs =>
          rw [hbt] at hterm
          simp only []
          cases hvals : s.frame.readAll locs with
          | none => trivial
          | some vals =>
            try simp only []
            cases hst : s.stack with
            | nil =>
              try simp only []
              rw [hst] at hstk
              cases hstk
              exact (Lir.Transition.halt hterm hvals rfl).step_eq
            | cons a rest =>
              try simp only []
              cases hw : a.frame.writeAll (a.results.map .reg) vals with
              | none => trivial
              | some fr =>
                try simp only []
                rw [hst] at hstk
                cases hstk with
                | direct hc hrest =>
                  obtain ⟨himpla, f, args, hcall⟩ := hc
                  exact ⟨_, .single (Lir.Transition.ret hterm hvals rfl hcall hw).step_eq,
                    _, himpla, rfl, rfl, rfl, hrest⟩
                | @indirect _ _ ts ja k lab dfr hc hdisp hrest =>
                  obtain ⟨himpla, f, args, hcall⟩ := hc
                  obtain ⟨n, fid, hf0, hf1⟩ := hdisp
                  have hlen := writeAll_length hw
                  have hs := writeAll_isSome (fr := dfr) (locs := dres n a.results.length)
                    (vals := vals) (by simpa [dres] using hlen)
                  obtain ⟨dfr', hdfr'⟩ := Option.isSome_iff_exists.mp hs
                  have s1 := (Lir.Transition.ret (s := ⟨⟨j, s.label, s.index⟩, s.frame,
                    ⟨⟨k, lab, 0⟩, dfr⟩ :: ⟨⟨ja, a.label, a.index⟩, a.frame⟩ :: ts, s.mem⟩)
                    hterm hvals rfl hf0 hdfr').step_eq
                  have hback : dfr'.readAll (dres n a.results.length) = some vals := by
                    rw [dres_eq] at hdfr' ⊢
                    exact readAll_writeAll (List.nodup_range.map fun x y h => by omega) hdfr'
                  have s2 := (Lir.Transition.ret (s := ⟨⟨k, lab, 0 + 1⟩, dfr',
                    ⟨⟨ja, a.label, a.index⟩, a.frame⟩ :: ts, s.mem⟩) hf1 hback rfl hcall hw).step_eq
                  exact ⟨_, .tail (.single s1) s2, _, himpla, rfl, rfl, rfl, hrest⟩
        | trap =>
          rw [hbt] at hterm
          simp only []
          exact (Lir.Transition.trap hterm).step_eq
      · rw [ite_eq_left hix]
        trivial


/-- The simulation is lock-step: every Mir step is at least one Lir step. -/
theorem Facts.lockstep (F : Facts L base us l) :
    Silmaril.LockstepSim (MirSem.Step us (place L l)) (Lir.Step l.prog) (Rel L us l) where
  step {_ _ _} hs hr := by
    have := F.sim hr
    unfold MirSem.Step at hs
    rw [hs] at this
    exact this

/-- **A link that passes the check refines `MirSem`**: the conclusion of
`Contract.link`, for the placement of the link. -/
theorem check_sound (L : Layout) (base : Nat) (us : Array Mir.Unit) (l : Linked)
    (h : check L base us l = true) (memSize : Nat) (hm : MirSem.need us base ≤ memSize) :
    ∃ P : MirSem.Placement, P.Valid us memSize ∧
      ∀ s, MirSem.start us P memSize = some s → ∀ b, MirSem.Behaves us P s b → b ≠ .stuck →
        ∃ t, l.prog.start 0 [] (linkedMem l memSize) = some t ∧ Lir.Behaves l.prog t b := by
  have F := Facts.of_check L base us l h
  refine ⟨place L l, F.valid hm, ?_⟩
  intro s hs b hb hns
  simp only [MirSem.start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
  obtain ⟨f0, hf0, fr, hfr, rfl⟩ := hs
  have h0 := F.entry f0 hf0
  obtain ⟨-, -, -, -, f', -, huniq, himpl⟩ := F.funcEntry h0
  have hf' : f0 = f' := huniq f0 (List.mem_of_mem_head? hf0) rfl
  subst hf'
  have hstart : l.prog.start 0 [] (linkedMem l memSize) =
      some ⟨⟨0, 0, 0⟩, fr, [], linkedMem l memSize⟩ := by
    simp [Lir.Prog.start, enter_eq himpl hfr]
  refine ⟨_, hstart, ?_⟩
  have hrel : Rel L us l ⟨f0, 0, 0, fr, [], MirSem.initMem us (place L l) memSize⟩
      ⟨⟨0, 0, 0⟩, fr, [], linkedMem l memSize⟩ :=
    ⟨0, himpl, rfl, rfl, (F.initMem_eq memSize).symm, .nil⟩
  have sim := F.lockstep
  cases b with
  | returned vs m =>
    obtain ⟨t, hst, ht⟩ := hb
    obtain ⟨t', hst', hrel'⟩ := sim.steps hst hrel
    have := F.sim hrel'
    rw [ht] at this
    exact ⟨t', hst', this⟩
  | trapped m =>
    obtain ⟨t, hst, ht⟩ := hb
    obtain ⟨t', hst', hrel'⟩ := sim.steps hst hrel
    have := F.sim hrel'
    rw [ht] at this
    exact ⟨t', hst', this⟩
  | stuck => exact absurd rfl hns
  | diverges => exact sim.toForwardSim.diverges hb hrel

end Silmaril.Compile.Mir.LinkCorrect
