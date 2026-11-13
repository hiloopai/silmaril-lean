module

public import Silmaril.Wasm.Models.FunRefCompile.Defs
public import Silmaril.Wasm.Models.FunCompile.Thms

/-!
# Compiling FunRef: representation of values and heaps

* `Rep μ s v w`: as `FunCompile`'s representation, with the cell addresses `μ` (`μ[ℓ]` is the
  address of the cell of location `ℓ`); `Rep.mono`: it survives growth of `μ` and every store
  change that keeps the `$box` structures (`BoxExt`);
* `HeapRep μ s σ`: the cells represent the heap; their addresses are distinct. It is kept by
  allocation (`HeapRep.prefix`, `HeapRep.alloc`) and re-established by a write (`HeapRep.set`);
* `FrameR f`: the frame has the module's three types;
* `Cont`, `Spec`: the continuation-passing statement, now also threading the heap;
* the cell instructions (`twp_newCell`, `twp_castCell`, `twp_getCell`, `twp_setCell`).

The instruction groups shared with FunLang come from `Silmaril.Wasm.Models.FunCompile.Thms`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRef (Tm eval Heap)
open Silmaril.Wasm.Models.FunCompile (dBox dMain boxIdx boxRef lx fx)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree getElem?_of_prefix)
open Silmaril.Wasm.Logic.Core (Post)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Stores that keep the boxes -/

/-- `s'` keeps every `$box` structure of `s`. -/
def BoxExt (s s' : Store H) : Prop :=
  ∀ (a : Nat) (fv : List FieldVal), s.structs[a]? = some ⟨dBox, fv⟩ →
    s'.structs[a]? = some ⟨dBox, fv⟩

theorem BoxExt.refl (s : Store H) : BoxExt s s := fun _ _ h => h

theorem BoxExt.trans {s₁ s₂ s₃ : Store H} (h₁ : BoxExt s₁ s₂) (h₂ : BoxExt s₂ s₃) : BoxExt s₁ s₃ :=
  fun a fv h => h₂ a fv (h₁ a fv h)

theorem BoxExt.of_prefix {s s' : Store H} (h : s.structs <+: s'.structs) : BoxExt s s' :=
  fun _ _ ha => getElem?_of_prefix h ha

theorem dCell_ne_dBox : dCell ≠ dBox := by decide

/-- The structures after a field write at `a`. -/
theorem setStructField_get (s : Store H) (a i : Nat) (fv : FieldVal) (b : Nat) :
    (s.setStructField a i fv).structs[b]? =
      if a = b then (s.structs[b]?).map fun si => { si with fields := si.fields.set i fv }
      else s.structs[b]? := by
  simp only [Store.setStructField, List.getElem?_modify]
  split <;> simp

/-- A write into a cell keeps the boxes. -/
theorem BoxExt.setCell {s : Store H} {a : Nat} {fv₀ : List FieldVal}
    (ha : s.structs[a]? = some ⟨dCell, fv₀⟩) (i : Nat) (fv : FieldVal) :
    BoxExt s (s.setStructField a i fv) := by
  intro b fvb hb
  rw [setStructField_get]
  by_cases hab : a = b
  · subst hab
    have hc : (⟨dCell, fv₀⟩ : StructInst) = ⟨dBox, fvb⟩ := Option.some.inj (ha.symm.trans hb)
    exact absurd (congrArg StructInst.type hc) dCell_ne_dBox
  · simp only [hab, ↓reduceIte]
    exact hb

/-! ## Representation -/

/-- `w` represents `v` in `s`, with cell addresses `μ`. -/
def Rep (μ : List Nat) (s : Store H) : FunRef.Val → Val → Prop
  | .int n, w => w = .ref (.i31 n)
  | .bool b, w => w = .ref (.i31 (if b then 1 else 0))
  | .pair a b, w => ∃ addr wa wb, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wa, .val wb]⟩ ∧ Rep μ s a wa ∧ Rep μ s b wb
  | .inl v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 0)), .val wv]⟩ ∧ Rep μ s v wv
  | .inr v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 1)), .val wv]⟩ ∧ Rep μ s v wv
  | .loc l, w => ∃ a, μ[l]? = some a ∧ w = .ref (.struct a)

/-- **Representation survives growth of the cells and stores that keep the boxes.** -/
theorem Rep.mono {μ μ' : List Nat} {s s' : Store H} (hμ : μ <+: μ') (hs : BoxExt s s') :
    ∀ {v : FunRef.Val} {w : Val}, Rep μ s v w → Rep μ' s' v w
  | .int _, _, hr => hr
  | .bool _, _, hr => hr
  | .pair _ _, _, ⟨addr, wa, wb, hw, hst, ha, hb⟩ =>
      ⟨addr, wa, wb, hw, hs _ _ hst, Rep.mono hμ hs ha, Rep.mono hμ hs hb⟩
  | .inl _, _, ⟨addr, wv, hw, hst, hv⟩ => ⟨addr, wv, hw, hs _ _ hst, Rep.mono hμ hs hv⟩
  | .inr _, _, ⟨addr, wv, hw, hst, hv⟩ => ⟨addr, wv, hw, hs _ _ hst, Rep.mono hμ hs hv⟩
  | .loc _, _, ⟨a, ha, hw⟩ => ⟨a, getElem?_of_prefix hμ ha, hw⟩

/-- **The cells represent the heap**, at distinct addresses. -/
def HeapRep (μ : List Nat) (s : Store H) (σ : Heap) : Prop :=
  μ.length = σ.length ∧ μ.Nodup ∧ ∀ (l : Nat) (v : FunRef.Val), σ[l]? = some v →
    ∃ (a : Nat) (w : Val), μ[l]? = some a ∧ s.structs[a]? = some ⟨dCell, [.val w]⟩ ∧ Rep μ s v w

/-- The cell of a represented location. -/
theorem HeapRep.cell {μ : List Nat} {s : Store H} {σ : Heap} (h : HeapRep μ s σ) {l a : Nat}
    (ha : μ[l]? = some a) : ∃ v w, σ[l]? = some v ∧ s.structs[a]? = some ⟨dCell, [.val w]⟩ ∧
      Rep μ s v w := by
  have hl : l < σ.length := h.1 ▸ (List.getElem?_eq_some_iff.1 ha).1
  obtain ⟨a', w, ha', hst, hv⟩ := h.2.2 l σ[l] (List.getElem?_eq_getElem hl)
  have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact ⟨σ[l], w, List.getElem?_eq_getElem hl, haa ▸ hst, hv⟩

/-- Every cell address is below the number of structures. -/
theorem HeapRep.lt {μ : List Nat} {s : Store H} {σ : Heap} (h : HeapRep μ s σ) {a : Nat}
    (ha : a ∈ μ) : a < s.structs.length := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨_, _, _, hst, _⟩ := h.cell (List.getElem?_eq_getElem hl)
  exact (List.getElem?_eq_some_iff.1 hst).1

/-- The heap survives allocation of structures. -/
theorem HeapRep.prefix {μ : List Nat} {s s' : Store H} {σ : Heap} (h : HeapRep μ s σ)
    (hs : s.structs <+: s'.structs) : HeapRep μ s' σ := by
  refine ⟨h.1, h.2.1, fun l v hl => ?_⟩
  obtain ⟨a, w, ha, hst, hv⟩ := h.2.2 l v hl
  exact ⟨a, w, ha, getElem?_of_prefix hs hst, hv.mono (List.prefix_refl _) (BoxExt.of_prefix hs)⟩

/-- A new cell for a new location. -/
theorem HeapRep.alloc {μ : List Nat} {s : Store H} {σ : Heap} (h : HeapRep μ s σ)
    {v : FunRef.Val} {w : Val} (hv : Rep μ s v w) :
    HeapRep (μ ++ [s.structs.length]) (s.addStruct ⟨dCell, [.val w]⟩) (σ ++ [v]) := by
  have hp := addStruct_prefix' s ⟨dCell, [.val w]⟩
  have hμ : μ <+: μ ++ [s.structs.length] := List.prefix_append _ _
  have hnd : (μ ++ [s.structs.length]).Nodup :=
    List.nodup_append.2 ⟨h.2.1, List.nodup_singleton _,
      fun a ha b hb => by rw [List.mem_singleton.1 hb]; exact Nat.ne_of_lt (h.lt ha)⟩
  refine ⟨by simp [h.1], hnd, fun l u hl => ?_⟩
  rcases Nat.lt_or_ge l σ.length with hlt | hge
  · obtain ⟨a, w', ha, hst, hu⟩ :=
      (h.prefix hp).2.2 l u (by rwa [List.getElem?_append_left hlt] at hl)
    exact ⟨a, w', getElem?_of_prefix hμ ha, hst, hu.mono hμ (BoxExt.refl _)⟩
  · have hle : l = σ.length := by
      have := (List.getElem?_eq_some_iff.1 hl).1
      simp at this; omega
    subst hle
    have hu : u = v := by simpa using hl.symm
    refine ⟨s.structs.length, w, by simp [← h.1], by simp [Store.addStruct], hu ▸ ?_⟩
    exact hv.mono hμ (BoxExt.of_prefix hp)
where
  addStruct_prefix' (s : Store H) (si : StructInst) : s.structs <+: (s.addStruct si).structs :=
    List.prefix_append _ _

theorem nodup_getElem?_inj {l : List Nat} (hl : l.Nodup) {i j a : Nat} (hi : l[i]? = some a)
    (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', hie⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', hje⟩ := List.getElem?_eq_some_iff.1 hj
  exact (List.Nodup.getElem_inj_iff hl).1 (hie.trans hje.symm)

/-- A write of a location's cell. -/
theorem HeapRep.set {μ : List Nat} {s : Store H} {σ : Heap} (h : HeapRep μ s σ) {l a : Nat}
    (ha : μ[l]? = some a) {v : FunRef.Val} {w : Val} (hv : Rep μ s v w) :
    HeapRep μ (s.setStructField a 0 (.val w)) (σ.set l v) := by
  obtain ⟨_, w₀, -, hst, -⟩ := h.cell ha
  have hext : BoxExt s (s.setStructField a 0 (.val w)) := BoxExt.setCell hst 0 _
  refine ⟨by simp [h.1], h.2.1, fun l' u hl' => ?_⟩
  by_cases hll : l = l'
  · subst hll
    have hu : u = v := by
      rw [List.getElem?_set_self (h.1 ▸ (List.getElem?_eq_some_iff.1 ha).1)] at hl'
      exact (Option.some.inj hl').symm
    refine ⟨a, w, ha, ?_, hu ▸ hv.mono (List.prefix_refl _) hext⟩
    simp [setStructField_get, hst]
  · have hl'' : σ[l']? = some u := by rwa [List.getElem?_set_ne hll] at hl'
    obtain ⟨a', w', ha', hst', hu⟩ := h.2.2 l' u hl''
    have haa : a ≠ a' := fun e => hll (nodup_getElem?_inj h.2.1 ha (e ▸ ha'))
    refine ⟨a', w', ha', ?_, hu.mono (List.prefix_refl _) hext⟩
    rw [setStructField_get]
    simp only [haa, ↓reduceIte]
    exact hst'

/-! ## Frames and environments -/

/-- The frame has the module's types and at most `2^32` locals. -/
def FrameR (f : Frame) : Prop := f.module.types = modTypes ∧ f.locals.length ≤ 2 ^ 32

theorem FrameR.ok {f : Frame} (hf : FrameR f) : FrameOK f := ⟨⟨[dMain, dCell], hf.1⟩, hf.2⟩

theorem FrameR.of_agree {d : Nat} {f f' : Frame} (hf : FrameR f) (h : Agree d f f') : FrameR f' :=
  ⟨h.1 ▸ hf.1, h.2.1 ▸ hf.2⟩

theorem FrameR.setLocal {f : Frame} (hf : FrameR f) (x : LocalIdx) (w : Val) :
    FrameR (f.setLocal x w) :=
  ⟨hf.1, (Silmaril.Proofs.Wasm.Models.FunCompile.len_setLocal f x w).symm ▸ hf.2⟩

/-- Locals `1 … d` represent the environment `ρ`. -/
def EnvRep (μ : List Nat) (s : Store H) (f : Frame) (d : Nat) (ρ : List FunRef.Val) : Prop :=
  ρ.length = d ∧ ∀ i v, ρ[i]? = some v → ∃ w, f.locals[d - i]? = some (some w) ∧ Rep μ s v w

theorem EnvRep.of_agree {μ μ' : List Nat} {s s' : Store H} {f f' : Frame} {d : Nat}
    {ρ : List FunRef.Val} (hr : EnvRep μ s f d ρ) (hμ : μ <+: μ') (hs : BoxExt s s')
    (h : Agree d f f') : EnvRep μ' s' f' d ρ := by
  refine ⟨hr.1, fun i v hi => ?_⟩
  obtain ⟨w, hw, hv⟩ := hr.2 i v hi
  exact ⟨w, (h.2.2 _ (Nat.sub_le d i)).trans hw, hv.mono hμ hs⟩

theorem EnvRep.cons {μ : List Nat} {s : Store H} {f : Frame} {d : Nat} {ρ : List FunRef.Val}
    (hr : EnvRep μ s f d ρ) {v : FunRef.Val} {w : Val} (hv : Rep μ s v w)
    (hlt : d + 1 < f.locals.length) (hlim : d + 1 < 2 ^ 32) :
    EnvRep μ s (f.setLocal (lx (d + 1)) w) (d + 1) (v :: ρ) := by
  have hx : (lx (d + 1)).toNat = d + 1 := by simp [lx, Idx.toNat]; exact hlim
  refine ⟨by simp [hr.1], fun i u hi => ?_⟩
  cases i with
  | zero =>
    have hu : u = v := by simpa using hi.symm
    exact ⟨w, by simp [Frame.setLocal, hx, hlt], hu ▸ hv⟩
  | succ i =>
    obtain ⟨w', hw', hu⟩ := hr.2 i u (by simpa using hi)
    have hag := (Agree.setLocal (f := f) w hlim).2.2 (d - i) (Nat.sub_le d i)
    exact ⟨w', by rw [show d + 1 - (i + 1) = d - i by omega, hag]; exact hw', hu⟩

/-! ## The statement proved of every term -/

/-- The continuation of a term with value `v` and final heap `σ'`. -/
def Cont (P : Numerics.Profile) (host : HostSemantics H) (d : Nat) (μ : List Nat) (s : Store H)
    (f : Frame) (v : FunRef.Val) (σ' : Heap) (us : List Val) (rest : List Admin) (Q : Post H) :
    Prop :=
  ∀ μ' s' f' w, μ <+: μ' → BoxExt s s' → Agree d f f' → HeapRep μ' s' σ' → Rep μ' s' v w →
    TWP P host s' f' (vals (us ++ [w]) ++ rest) Q

/-- **The correctness of the code of `e` at depth `d`.** -/
def Spec (P : Numerics.Profile) (host : HostSemantics H) (d : Nat) (e : Tm) : Prop :=
  ∀ σ ρ v σ', eval σ ρ e = some (v, σ') → ∀ μ (s : Store H) (f : Frame), FrameR f →
    d + e.depth < f.locals.length → EnvRep μ s f d ρ → HeapRep μ s σ →
    ∀ us rest Q, Cont P host d μ s f v σ' us rest Q →
      TWP P host s f (vals us ++ (expression (compile d e) ++ rest)) Q

theorem Cont.later {d : Nat} {μ μ₁ : List Nat} {s s₁ : Store H} {f f₁ : Frame} {v : FunRef.Val}
    {σ' : Heap} {us : List Val} {rest : List Admin} {Q : Post H}
    (hk : Cont P host d μ s f v σ' us rest Q) (hμ : μ <+: μ₁) (hs : BoxExt s s₁)
    (hf : Agree d f f₁) : Cont P host d μ₁ s₁ f₁ v σ' us rest Q :=
  fun μ' s' f' w hμ' hs' hf' hh hw =>
    hk μ' s' f' w (hμ.trans hμ') (hs.trans hs') (hf.trans hf') hh hw

/-! ## Cells -/

/-- The field types of `$cell`. -/
def cellFields : Ty (.list .field) :=
  .cons (.field .var (.val (.refv (.ref true (.abs .any))))) .nil

theorem expand_cell : Expand dCell (.struct cellFields) := ⟨rfl⟩

theorem type_cell {f : Frame} (hf : FrameR f) : f.type? cellIdx = some dCell := by
  simp [Frame.type?, hf.1, modTypes, cellIdx, Idx.toNat]

theorem fx0 : (fx 0).toNat = 0 := rfl

/-- `struct.new $cell`. -/
theorem twp_newCell {s : Store H} {f : Frame} (hf : FrameR f) {us : List Val} {rest : List Admin}
    {Q : Post H} {w : Val}
    (h : TWP P host (s.addStruct ⟨dCell, [.val w]⟩) f
      (vals (us ++ [.ref (.struct s.structs.length)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [w]) ++ .plain (.structNew cellIdx) :: rest) Q := by
  have hnf : newFields cellFields [w] = [.val w] := rfl
  have hp : ∀ p ∈ cellFields.toList.zip [w], packable (fieldStorage p.1) p.2 = true := by
    intro p hp
    rw [List.mem_singleton.1 hp]
    rfl
  exact Wp.structNew (m := .total) (type_cell hf) expand_cell rfl hp (hnf ▸ h)

/-- `ref.cast (ref $cell)` on a cell. -/
theorem twp_castCell {s : Store H} {f : Frame} (hf : FrameR f) {us : List Val} {rest : List Admin}
    {Q : Post H} {addr : Nat} {fv : List FieldVal} (hs : s.structs[addr]? = some ⟨dCell, fv⟩)
    (h : TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ .plain (.refCast cellRef) :: rest) Q := by
  have hok : RefOk s (.struct addr) (f.module.instRef cellRef) := by
    have h' : RefOk s (.struct addr) (.ref false (Ty.defHeap dCell)) := RefOk.struct hs
    rw [ModuleInst.instRef, hf.1]
    exact h'
  exact Wp.refCast (m := .total) hok h

/-- `struct.get $cell 0`. -/
theorem twp_getCell {s : Store H} {f : Frame} (hf : FrameR f) {us : List Val} {rest : List Admin}
    {Q : Post H} {addr : Nat} {w : Val} (hs : s.structs[addr]? = some ⟨dCell, [.val w]⟩)
    (h : TWP P host s f (vals (us ++ [w]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++
      .plain (.structGet none cellIdx (fx 0)) :: rest) Q :=
  Wp.structGet (m := .total) (ft := .field .var (.val (.refv (.ref true (.abs .any))))) hs rfl
    (type_cell hf) expand_cell rfl rfl h

/-- `struct.set $cell 0`. -/
theorem twp_setCell {s : Store H} {f : Frame} (hf : FrameR f) {us : List Val} {rest : List Admin}
    {Q : Post H} {addr : Nat} {w₀ w : Val} (hs : s.structs[addr]? = some ⟨dCell, [.val w₀]⟩)
    (h : TWP P host (s.setStructField addr 0 (.val w)) f (vals us ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr), w]) ++
      .plain (.structSet cellIdx (fx 0)) :: rest) Q :=
  Wp.structSet (m := .total) (ft := .field .var (.val (.refv (.ref true (.abs .any)))))
    (type_cell hf) expand_cell rfl hs (by simp [fx0]) rfl h

end Silmaril.Proofs.Wasm.Models.FunRefCompile
