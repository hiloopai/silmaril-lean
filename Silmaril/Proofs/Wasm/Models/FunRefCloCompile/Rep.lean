module

public import Silmaril.Wasm.Models.FunRefCloCompile.Defs
public import Silmaril.Wasm.Models.FunRefClo.Thms
public import Silmaril.Wasm.Models.FunCloCompile.Thms
public import Silmaril.Wasm.Models.FunRefCompile.Thms

/-!
# Compiling FunRefClo: representation, heaps and the statement proved of every term

The representation of FunCloCompile (closures as `$box`es `(tag, env)`, environments as `$box`
lists) and the heap correspondence of FunRefCompile (locations as `$cell`s, `μ[ℓ]` the address of
the cell of `ℓ`), combined:

* `Rep L μ s v w`, `EnvL L μ s ρ w` (mutual); `Rep.mono`: representation survives growth of `μ`
  and every store change that keeps the `$box` structures (`BoxExt`, from FunRefCompile);
* `HeapRep L μ s σ`: the cells represent the heap at distinct addresses; `HeapRep.prefix`,
  `HeapRep.alloc`, `HeapRep.set`;
* `Ext s s'`: `s'` keeps the boxes of `s` and its functions (so `apply` stays at address `1`);
* `FOK f`: the frame has the module's types and `apply` at function index `1`; the cell
  instructions `twp_newCell`, `twp_castCell`, `twp_getCell`, `twp_setCell` for these types;
* `Cont`, `Spec p k d e`: the continuation-passing correctness of the code of `e` for evaluations
  with fuel `k`, threading the heap; `applySpec`, `ApplyOK p k`;
* the closure table: `table_closed`, `mem_table_locals`, `tagOf_get`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCloCompile Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Models.FunRefClo (Tm eval Prog Heap tableLocals)
open Silmaril.Wasm.Models.FunCompile (dBox dMain lx fx boxIdx boxRef)
open Silmaril.Wasm.Models.FunRefCompile (cellIdx cellRef dCell)
open Silmaril.Wasm.Models.FunCloCompile (dApply)
open Silmaril.Proofs.Wasm.Models.FunCompile (FrameOK Agree getElem?_of_prefix)
open Silmaril.Proofs.Wasm.Models.FunRefCompile (BoxExt BoxExt.refl BoxExt.of_prefix BoxExt.setCell
  setStructField_get nodup_getElem?_inj cellFields expand_cell fx0)
open Silmaril.Wasm.Logic.Core (Post Outcome)

/-! ## Representation -/

mutual
/-- `w` represents `v` in `s`, for the closure table `L` and the cell addresses `μ`. -/
def Rep (L : List (Nat × Tm)) (μ : List Nat) (s : Store Nat) : FunRefClo.Val → Val → Prop
  | .int n, w => w = .ref (.i31 n)
  | .bool b, w => w = .ref (.i31 (if b then 1 else 0))
  | .pair a b, w => ∃ addr wa wb, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wa, .val wb]⟩ ∧ Rep L μ s a wa ∧ Rep L μ s b wb
  | .inl v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 0)), .val wv]⟩ ∧ Rep L μ s v wv
  | .inr v, w => ∃ addr wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val (.ref (.i31 1)), .val wv]⟩ ∧ Rep L μ s v wv
  | .clo b ρ, w => ∃ addr we, w = .ref (.struct addr) ∧
      s.structs[addr]? =
        some ⟨dBox, [.val (.ref (.i31 (BitVec.ofNat 31 (tagOf L ρ.length b)))), .val we]⟩ ∧
      L[tagOf L ρ.length b]? = some (ρ.length, b) ∧ EnvL L μ s ρ we
  | .loc l, w => ∃ a, μ[l]? = some a ∧ w = .ref (.struct a)

/-- `w` is the `$box` list of the environment `ρ` in `s`. -/
def EnvL (L : List (Nat × Tm)) (μ : List Nat) (s : Store Nat) :
    List FunRefClo.Val → Val → Prop
  | [], w => w = .ref (.i31 0)
  | v :: ρ, w => ∃ addr wt wv, w = .ref (.struct addr) ∧
      s.structs[addr]? = some ⟨dBox, [.val wt, .val wv]⟩ ∧ EnvL L μ s ρ wt ∧ Rep L μ s v wv
end

mutual
/-- **Representation survives growth of the cells and stores that keep the boxes.** -/
theorem Rep.mono {L : List (Nat × Tm)} {μ μ' : List Nat} {s s' : Store Nat} (hμ : μ <+: μ')
    (hs : BoxExt s s') : ∀ {v : FunRefClo.Val} {w : Val}, Rep L μ s v w → Rep L μ' s' v w
  | .int _, _, hr => hr
  | .bool _, _, hr => hr
  | .pair _ _, _, ⟨addr, wa, wb, hw, hst, ha, hb⟩ =>
      ⟨addr, wa, wb, hw, hs _ _ hst, Rep.mono hμ hs ha, Rep.mono hμ hs hb⟩
  | .inl _, _, ⟨addr, wv, hw, hst, hv⟩ => ⟨addr, wv, hw, hs _ _ hst, Rep.mono hμ hs hv⟩
  | .inr _, _, ⟨addr, wv, hw, hst, hv⟩ => ⟨addr, wv, hw, hs _ _ hst, Rep.mono hμ hs hv⟩
  | .clo _ _, _, ⟨addr, we, hw, hst, hL, he⟩ =>
      ⟨addr, we, hw, hs _ _ hst, hL, EnvL.mono hμ hs he⟩
  | .loc _, _, ⟨a, ha, hw⟩ => ⟨a, getElem?_of_prefix hμ ha, hw⟩

/-- Environment lists survive the same changes. -/
theorem EnvL.mono {L : List (Nat × Tm)} {μ μ' : List Nat} {s s' : Store Nat} (hμ : μ <+: μ')
    (hs : BoxExt s s') : ∀ {ρ : List FunRefClo.Val} {w : Val}, EnvL L μ s ρ w → EnvL L μ' s' ρ w
  | [], _, hr => hr
  | _ :: _, _, ⟨addr, wt, wv, hw, hst, ht, hv⟩ =>
      ⟨addr, wt, wv, hw, hs _ _ hst, EnvL.mono hμ hs ht, Rep.mono hμ hs hv⟩
end

/-! ## Heaps -/

/-- **The cells represent the heap**, at distinct addresses. -/
def HeapRep (L : List (Nat × Tm)) (μ : List Nat) (s : Store Nat) (σ : Heap) : Prop :=
  μ.length = σ.length ∧ μ.Nodup ∧ ∀ (l : Nat) (v : FunRefClo.Val), σ[l]? = some v →
    ∃ (a : Nat) (w : Val), μ[l]? = some a ∧ s.structs[a]? = some ⟨dCell, [.val w]⟩ ∧
      Rep L μ s v w

theorem HeapRep.empty (L : List (Nat × Tm)) (s : Store Nat) : HeapRep L [] s [] :=
  ⟨rfl, List.nodup_nil, fun _ _ h => by simp at h⟩

/-- The cell of a represented location. -/
theorem HeapRep.cell {L : List (Nat × Tm)} {μ : List Nat} {s : Store Nat} {σ : Heap}
    (h : HeapRep L μ s σ) {l a : Nat} (ha : μ[l]? = some a) :
    ∃ v w, σ[l]? = some v ∧ s.structs[a]? = some ⟨dCell, [.val w]⟩ ∧ Rep L μ s v w := by
  have hl : l < σ.length := h.1 ▸ (List.getElem?_eq_some_iff.1 ha).1
  obtain ⟨a', w, ha', hst, hv⟩ := h.2.2 l σ[l] (List.getElem?_eq_getElem hl)
  have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact ⟨σ[l], w, List.getElem?_eq_getElem hl, haa ▸ hst, hv⟩

/-- Every cell address is below the number of structures. -/
theorem HeapRep.lt {L : List (Nat × Tm)} {μ : List Nat} {s : Store Nat} {σ : Heap}
    (h : HeapRep L μ s σ) {a : Nat} (ha : a ∈ μ) : a < s.structs.length := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨_, _, _, hst, _⟩ := h.cell (List.getElem?_eq_getElem hl)
  exact (List.getElem?_eq_some_iff.1 hst).1

/-- The heap survives allocation of structures. -/
theorem HeapRep.prefix {L : List (Nat × Tm)} {μ : List Nat} {s s' : Store Nat} {σ : Heap}
    (h : HeapRep L μ s σ) (hs : s.structs <+: s'.structs) : HeapRep L μ s' σ := by
  refine ⟨h.1, h.2.1, fun l v hl => ?_⟩
  obtain ⟨a, w, ha, hst, hv⟩ := h.2.2 l v hl
  exact ⟨a, w, ha, getElem?_of_prefix hs hst, hv.mono (List.prefix_refl _) (BoxExt.of_prefix hs)⟩

/-- A new cell for a new location. -/
theorem HeapRep.alloc {L : List (Nat × Tm)} {μ : List Nat} {s : Store Nat} {σ : Heap}
    (h : HeapRep L μ s σ) {v : FunRefClo.Val} {w : Val} (hv : Rep L μ s v w) :
    HeapRep L (μ ++ [s.structs.length]) (s.addStruct ⟨dCell, [.val w]⟩) (σ ++ [v]) := by
  have hp : s.structs <+: (s.addStruct ⟨dCell, [.val w]⟩).structs := List.prefix_append _ _
  have hμ : μ <+: μ ++ [s.structs.length] := List.prefix_append _ _
  have hnd : (μ ++ [s.structs.length]).Nodup :=
    List.nodup_append.2 ⟨h.2.1, List.nodup_singleton _,
      fun a ha b hb => by rw [List.mem_singleton.1 hb]; exact Nat.ne_of_lt (h.lt ha)⟩
  refine ⟨by simp [h.1], hnd, fun l u hl => ?_⟩
  rcases Nat.lt_or_ge l σ.length with hlt | hge
  · have hl' : σ[l]? = some u := by rwa [List.getElem?_append_left hlt] at hl
    obtain ⟨a, w', ha, hst, hu⟩ := (h.prefix hp).2.2 l u hl'
    exact ⟨a, w', getElem?_of_prefix hμ ha, hst, hu.mono hμ (BoxExt.refl _)⟩
  · have hle : l = σ.length := by
      have := (List.getElem?_eq_some_iff.1 hl).1
      simp at this; omega
    subst hle
    have hu : u = v := by simpa using hl.symm
    refine ⟨s.structs.length, w, by simp [← h.1], by simp [Store.addStruct], hu ▸ ?_⟩
    exact hv.mono hμ (BoxExt.of_prefix hp)

/-- A write of a location's cell. -/
theorem HeapRep.set {L : List (Nat × Tm)} {μ : List Nat} {s : Store Nat} {σ : Heap}
    (h : HeapRep L μ s σ) {l a : Nat} (ha : μ[l]? = some a) {v : FunRefClo.Val} {w : Val}
    (hv : Rep L μ s v w) : HeapRep L μ (s.setStructField a 0 (.val w)) (σ.set l v) := by
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

/-! ## Stores and frames -/

/-- `s'` keeps the boxes of `s` and has its functions. -/
def Ext (s s' : Store Nat) : Prop := BoxExt s s' ∧ s'.funcs = s.funcs

theorem Ext.refl (s : Store Nat) : Ext s s := ⟨BoxExt.refl s, rfl⟩

theorem Ext.trans {s₁ s₂ s₃ : Store Nat} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem Ext.addStruct (s : Store Nat) (si : StructInst) : Ext s (s.addStruct si) :=
  ⟨BoxExt.of_prefix (List.prefix_append _ _), rfl⟩

theorem Ext.setCell {s : Store Nat} {a : Nat} {fv₀ : List FieldVal}
    (ha : s.structs[a]? = some ⟨dCell, fv₀⟩) (i : Nat) (fv : FieldVal) :
    Ext s (s.setStructField a i fv) :=
  ⟨BoxExt.setCell ha i fv, by simp [Store.setStructField]⟩

theorem Ext.funcs {s s' : Store Nat} {a : Nat} {fi : FuncInst Nat} (h : Ext s s')
    (hf : s.funcs[a]? = some fi) : s'.funcs[a]? = some fi := by
  rw [h.2]; exact hf

/-- The frame invariant: FunCompile's, the module's types, and `apply` at function index `1`. -/
def FOK (f : Frame) : Prop :=
  FrameOK f ∧ f.module.funcs[1]? = some 1 ∧ f.module.types = modTypes

theorem FOK.of_agree {d : Nat} {f f' : Frame} (hf : FOK f) (h : Agree d f f') : FOK f' :=
  ⟨hf.1.of_agree h, h.1 ▸ hf.2.1, h.1 ▸ hf.2.2⟩

theorem FOK.setLocal {f : Frame} (hf : FOK f) (x : LocalIdx) (w : Val) : FOK (f.setLocal x w) :=
  ⟨Silmaril.Proofs.Wasm.Models.FunCompile.FrameOK.setLocal hf.1 x w, hf.2⟩

theorem FOK.of_eq {F F' : Frame} (hF : FOK F) (hm : F'.module = F.module)
    (hl : F'.locals.length = F.locals.length) : FOK F' :=
  ⟨⟨hm ▸ hF.1.1, hl ▸ hF.1.2⟩, hm ▸ hF.2.1, hm ▸ hF.2.2⟩

/-- A local other than `x` is kept by setting `x`. -/
theorem setLocal_ne {f : Frame} {x y : Nat} (w : Val) (hlim : x < 2 ^ 32) (hne : x ≠ y) :
    (f.setLocal (lx x) w).locals[y]? = f.locals[y]? := by
  have hx : (lx x).toNat = x := by simp [lx, Idx.toNat]; exact hlim
  simp only [Frame.setLocal, hx]
  exact List.getElem?_set_ne hne

/-- The environment `ρ` (of length `d`) is in locals `1 … d`. -/
def EnvRep (L : List (Nat × Tm)) (μ : List Nat) (s : Store Nat) (f : Frame) (d : Nat)
    (ρ : List FunRefClo.Val) : Prop :=
  ρ.length = d ∧ ∀ i v, ρ[i]? = some v → ∃ w, f.locals[d - i]? = some (some w) ∧ Rep L μ s v w

theorem EnvRep.of_agree {L : List (Nat × Tm)} {μ μ' : List Nat} {s s' : Store Nat}
    {f f' : Frame} {d : Nat} {ρ : List FunRefClo.Val} (hr : EnvRep L μ s f d ρ)
    (hμ : μ <+: μ') (hs : BoxExt s s') (h : Agree d f f') : EnvRep L μ' s' f' d ρ := by
  refine ⟨hr.1, fun i v hi => ?_⟩
  obtain ⟨w, hw, hv⟩ := hr.2 i v hi
  exact ⟨w, (h.2.2 _ (Nat.sub_le d i)).trans hw, hv.mono hμ hs⟩

theorem EnvRep.cons {L : List (Nat × Tm)} {μ : List Nat} {s : Store Nat} {f : Frame} {d : Nat}
    {ρ : List FunRefClo.Val} (hr : EnvRep L μ s f d ρ) {v : FunRefClo.Val} {w : Val}
    (hv : Rep L μ s v w) (hlt : d + 1 < f.locals.length) (hlim : d + 1 < 2 ^ 32) :
    EnvRep L μ s (f.setLocal (lx (d + 1)) w) (d + 1) (v :: ρ) := by
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

/-! ## Cells -/

variable {P : Numerics.Profile} {host : HostSemantics Nat}

theorem type_cell {f : Frame} (hf : FOK f) : f.type? cellIdx = some dCell := by
  simp [Frame.type?, hf.2.2, modTypes, cellIdx, Idx.toNat]

/-- `struct.new $cell`. -/
theorem twp_newCell {s : Store Nat} {f : Frame} (hf : FOK f) {us : List Val} {rest : List Admin}
    {Q : Post Nat} {w : Val}
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
theorem twp_castCell {s : Store Nat} {f : Frame} (hf : FOK f) {us : List Val}
    {rest : List Admin} {Q : Post Nat} {addr : Nat} {fv : List FieldVal}
    (hs : s.structs[addr]? = some ⟨dCell, fv⟩)
    (h : TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++ .plain (.refCast cellRef) :: rest) Q := by
  have hok : RefOk s (.struct addr) (f.module.instRef cellRef) := by
    have h' : RefOk s (.struct addr) (.ref false (Ty.defHeap dCell)) := RefOk.struct hs
    rw [ModuleInst.instRef, hf.2.2]
    exact h'
  exact Wp.refCast (m := .total) hok h

/-- `struct.get $cell 0`. -/
theorem twp_getCell {s : Store Nat} {f : Frame} (hf : FOK f) {us : List Val} {rest : List Admin}
    {Q : Post Nat} {addr : Nat} {w : Val} (hs : s.structs[addr]? = some ⟨dCell, [.val w]⟩)
    (h : TWP P host s f (vals (us ++ [w]) ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr)]) ++
      .plain (.structGet none cellIdx (fx 0)) :: rest) Q :=
  Wp.structGet (m := .total) (ft := .field .var (.val (.refv (.ref true (.abs .any))))) hs rfl
    (type_cell hf) expand_cell rfl rfl h

/-- `struct.set $cell 0`. -/
theorem twp_setCell {s : Store Nat} {f : Frame} (hf : FOK f) {us : List Val} {rest : List Admin}
    {Q : Post Nat} {addr : Nat} {w₀ w : Val} (hs : s.structs[addr]? = some ⟨dCell, [.val w₀]⟩)
    (h : TWP P host (s.setStructField addr 0 (.val w)) f (vals us ++ rest) Q) :
    TWP P host s f (vals (us ++ [.ref (.struct addr), w]) ++
      .plain (.structSet cellIdx (fx 0)) :: rest) Q :=
  Wp.structSet (m := .total) (ft := .field .var (.val (.refv (.ref true (.abs .any)))))
    (type_cell hf) expand_cell rfl hs (by simp [fx0]) rfl h

/-! ## The statement proved of every term -/

/-- The continuation of a term with value `v` and final heap `σ'`. -/
def Cont (P : Numerics.Profile) (host : HostSemantics Nat) (L : List (Nat × Tm)) (d : Nat)
    (μ : List Nat) (s : Store Nat) (f : Frame) (v : FunRefClo.Val) (σ' : Heap) (us : List Val)
    (rest : List Admin) (Q : Post Nat) : Prop :=
  ∀ μ' s' f' w, μ <+: μ' → Ext s s' → Agree d f f' → HeapRep L μ' s' σ' → Rep L μ' s' v w →
    TWP P host s' f' (vals (us ++ [w]) ++ rest) Q

theorem Cont.later {L : List (Nat × Tm)} {d : Nat} {μ μ₁ : List Nat} {s s₁ : Store Nat}
    {f f₁ : Frame} {v : FunRefClo.Val} {σ' : Heap} {us : List Val} {rest : List Admin}
    {Q : Post Nat} (hk : Cont P host L d μ s f v σ' us rest Q) (hμ : μ <+: μ₁) (hs : Ext s s₁)
    (hf : Agree d f f₁) : Cont P host L d μ₁ s₁ f₁ v σ' us rest Q :=
  fun μ' s' f' w hμ' hs' hf' hh hw =>
    hk μ' s' f' w (hμ.trans hμ') (hs.trans hs') (hf.trans hf') hh hw

/-- **The correctness of the code of `e` at depth `d`** for evaluations with fuel `k`. -/
def Spec (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k d : Nat) (e : Tm) :
    Prop :=
  ∀ σ ρ v σ', eval k σ ρ e = some (v, σ') → ∀ μ (s : Store Nat) (f : Frame), FOK f →
    s.funcs[1]? = some (applyInst p) → d + e.depth < f.locals.length →
    EnvRep p.table μ s f d ρ → HeapRep p.table μ s σ → (∀ x ∈ e.fixes d, x ∈ p.table) →
    ∀ us rest Q, Cont P host p.table d μ s f v σ' us rest Q →
      TWP P host s f (vals us ++ (expression (compile p.table d e) ++ rest)) Q

/-- **The specification of `apply`** on the closure `clo b ρ'` and the argument `u` in the heap
`σ` (cells `μ`), whose body returns `v` in the heap `σ'`. -/
def applySpec (p : Prog) (b : Tm) (ρ' : List FunRefClo.Val) (u v : FunRefClo.Val)
    (σ σ' : Heap) (μ : List Nat) : FSpec Nat :=
  ⟨fun s args => s.funcs[1]? = some (applyInst p) ∧ HeapRep p.table μ s σ ∧
      ∃ wc wu, args = [wc, wu] ∧ Rep p.table μ s (.clo b ρ') wc ∧ Rep p.table μ s u wu,
    fun s _ s' o => ∃ w μ', o = .normal [w] ∧ Ext s s' ∧ μ <+: μ' ∧ HeapRep p.table μ' s' σ' ∧
      Rep p.table μ' s' v w⟩

/-- `apply` is totally correct on every closure whose body evaluates with fuel `k`. -/
def ApplyOK (P : Numerics.Profile) (host : HostSemantics Nat) (p : Prog) (k : Nat) : Prop :=
  ∀ b ρ' u v σ σ' μ, eval k σ (u :: .clo b ρ' :: ρ') b = some (v, σ') →
    TFSpecAt P host 1 (applySpec p b ρ' u v σ σ' μ)

/-! ## The closure table -/

/-- The table of the body of every `fix` subterm is part of the table of the term. -/
theorem fixes_closed : ∀ (e : Tm) (d : Nat) {d' : Nat} {b : Tm}, (d', b) ∈ e.fixes d →
    ∀ x ∈ b.fixes (d' + 2), x ∈ e.fixes d
  | .var _, _, _, _, h => by simp [Tm.fixes] at h
  | .int _, _, _, _, h => by simp [Tm.fixes] at h
  | .bool _, _, _, _, h => by simp [Tm.fixes] at h
  | .arith _ a c, d, _, _, h => fixes_closed_two a c d h (fixes_closed a d) (fixes_closed c d)
  | .cmp _ a c, d, _, _, h => fixes_closed_two a c d h (fixes_closed a d) (fixes_closed c d)
  | .pair a c, d, _, _, h => fixes_closed_two a c d h (fixes_closed a d) (fixes_closed c d)
  | .app a c, d, _, _, h => fixes_closed_two a c d h (fixes_closed a d) (fixes_closed c d)
  | .set a c, d, _, _, h => fixes_closed_two a c d h (fixes_closed a d) (fixes_closed c d)
  | .let_ a c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun x hx => .inl (fixes_closed a d h x hx)
    · exact fun x hx => .inr (fixes_closed c (d + 1) h x hx)
  | .ite c t e, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact fun x hx => .inl (.inl (fixes_closed c d h x hx))
    · exact fun x hx => .inl (.inr (fixes_closed t d h x hx))
    · exact fun x hx => .inr (fixes_closed e d h x hx)
  | .case e l r, d, _, _, h => by
    simp only [Tm.fixes, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact fun x hx => .inl (.inl (fixes_closed e d h x hx))
    · exact fun x hx => .inl (.inr (fixes_closed l (d + 1) h x hx))
    · exact fun x hx => .inr (fixes_closed r (d + 1) h x hx)
  | .fst e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .snd e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .inl e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .inr e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .ref e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .get e, d, _, _, h => by simp only [Tm.fixes] at h ⊢; exact fixes_closed e d h
  | .fix c, d, _, _, h => by
    simp only [Tm.fixes, List.mem_cons] at h ⊢
    rcases h with h | h
    · cases h
      exact fun x hx => .inr hx
    · exact fun x hx => .inr (fixes_closed c (d + 2) h x hx)
where
  fixes_closed_two (a c : Tm) (d : Nat) {d' : Nat} {b : Tm}
      (h : (d', b) ∈ a.fixes d ++ c.fixes d)
      (ha : ∀ {d' : Nat} {b : Tm}, (d', b) ∈ a.fixes d → ∀ x ∈ b.fixes (d' + 2), x ∈ a.fixes d)
      (hc : ∀ {d' : Nat} {b : Tm}, (d', b) ∈ c.fixes d → ∀ x ∈ b.fixes (d' + 2), x ∈ c.fixes d) :
      ∀ x ∈ b.fixes (d' + 2), x ∈ a.fixes d ++ c.fixes d := by
    rcases List.mem_append.1 h with h | h
    · exact fun x hx => List.mem_append_left _ (ha h x hx)
    · exact fun x hx => List.mem_append_right _ (hc h x hx)

theorem table_closed {p : Prog} {d : Nat} {b : Tm} (h : (d, b) ∈ p.table) :
    ∀ x ∈ b.fixes (d + 2), x ∈ p.table :=
  fixes_closed p.body 1 h

/-- `apply` has enough locals for every entry of the table. -/
theorem mem_table_locals {L : List (Nat × Tm)} {d : Nat} {b : Tm} (h : (d, b) ∈ L) :
    d + b.depth + 1 ≤ tableLocals L :=
  Silmaril.Proofs.Wasm.Models.FunCloCompile.le_foldr_max (List.mem_map.2 ⟨(d, b), h, rfl⟩)

/-- The tag of a table entry. -/
theorem tagOf_get {L : List (Nat × Tm)} {d : Nat} {b : Tm} (h : (d, b) ∈ L) :
    L[tagOf L d b]? = some (d, b) := by
  unfold tagOf
  rw [List.getElem?_eq_some_iff]
  exact ⟨List.idxOf_lt_length_iff.2 h, List.getElem_idxOf (List.idxOf_lt_length_iff.2 h)⟩

end Silmaril.Proofs.Wasm.Models.FunRefCloCompile
