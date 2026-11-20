module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Realloc

/-!
# Accepting runs of `store_list_into_range`, generic in the element

The canonical ABI's `store_list_into_range` (`Canon.storeListIntoRangeWith`) in a lift context
`cx` of the caller whose memory is address `ma` and whose `realloc` is the typed allocator `ra`
(`LowerCx`), on an accepting path, for any element layout `el` and element store `storeElem`
that has a `Spec` relating the renamed core stores by some relation `Elem`:

* `spec_storeListIntoRange`: the allocator run (`spec_realloc`) answers `q` (`ReallocRun`),
  the alignment and bounds checks pass (`q % el.alignment.bytes = 0`, the bytes lie in memory
  `ma` of the store the allocator left), and the elements are stored at `q`, `q + el.size`, …
  (`ElemsRel`);
* `spec_writeMem`: a memory write is `SingleThreaded.memWrite?` on the core store.

Along the way the configuration keeps `LInv` (memory `ma` is 32-bit, the instance is well
formed at the renamed core store) and grows (`Grows`: the caller records and the task view
only get longer).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {prof : ProfileKind}

/-- Memory address `ma` (an engine memory address). -/
abbrev memAt (P : Profile) (ma : Nat) : (E3 P).MemAddr := show Nat from ma

/-- The configuration invariant of a lowering: memory `ma` is 32-bit and the instance is well
formed at the renamed core store. -/
structure LInv (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) (ma : Nat)
    (m : Config (E3 P) Unit) : Prop where
  mem : (E3 P).memAddrType? m.core (memAt P ma) = some .i32
  wf : I.WellFormed (cmap m.core)

/-- The caller records and the task view only get longer. -/
def Grows (m m' : Config (E3 P) Unit) : Prop :=
  m.store.callers <+: m'.store.callers ∧ tview m.store <+: tview m'.store

theorem Grows.refl (m : Config (E3 P) Unit) : Grows m m := ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem Grows.trans {m₁ m₂ m₃ : Config (E3 P) Unit} (h₁ : Grows m₁ m₂) (h₂ : Grows m₂ m₃) :
    Grows m₁ m₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- A lift context of the caller: memory `ma` and the typed allocator `ra`. -/
structure LowerCx (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) (ra ma : Nat)
    (cx : LiftLowerContext (E3 P)) : Prop where
  mem : cx.opts.memory = some (memAt P ma)
  realloc : cx.opts.realloc = some ra
  alloc : AllocAt I ra

/-- The elements `us`, stored at `p`, `p + size`, … by `Elem`, take the store `s` to `s'`. -/
inductive ElemsRel {α : Type} (size : Nat)
    (Elem : α → Nat → Silmaril.Wasm.Execution.Core.Store Nat →
      Silmaril.Wasm.Execution.Core.Store Nat → Prop) :
    List α → Nat → Silmaril.Wasm.Execution.Core.Store Nat →
      Silmaril.Wasm.Execution.Core.Store Nat → Prop where
  | nil {p s} : ElemsRel size Elem [] p s s
  | cons {u us p s s₁ s'} : Elem u p s s₁ → ElemsRel size Elem us (p + size) s₁ s' →
      ElemsRel size Elem (u :: us) p s s'

/-! ## Memory writes -/

/-- The memory address types after a byte write. -/
theorem memWrite?_memAddrType {s s' : (E3 P).Store (CanonHost (E3 P))} {a st : Nat}
    {bs : ByteArray} (h : Silmaril.Wasm.SingleThreaded.memWrite? s a st bs = some s') (b : Nat) :
    Silmaril.Wasm.SingleThreaded.memAddrType? s' b =
      Silmaril.Wasm.SingleThreaded.memAddrType? s b :=
  Silmaril.Wasm.Component.Engine.Core3.memWrite?_memAddrType h b

/-- **A memory write** of `cx` (memory `ma`): the core store's `memWrite?`. -/
theorem spec_writeMem {th : Option ThreadId} {m : Config (E3 P) Unit} {ma : Nat}
    {cx : LiftLowerContext (E3 P)} (hcx : cx.opts.memory = some (memAt P ma)) (ptr : Nat)
    (bytes : ByteArray) :
    SpecR prof P th (writeMem cx ptr bytes) m
      (fun _ m' => ∃ c', Silmaril.Wasm.SingleThreaded.memWrite? m.core ma ptr bytes = some c' ∧
        m' = { m with core := c' }) := by
  unfold writeMem memAddr
  rw [hcx]
  refine Spec.bind (Spec.orTrap _ _) fun a m₁ ⟨ha, hm⟩ _ _ => ?_
  subst m₁
  cases ha
  refine Spec.bind Spec.readCore fun v m₂ ⟨hv, hm⟩ _ _ => ?_
  subst m₂ v
  cases hw : (E3 P).memWrite? m.core (memAt P ma) ptr bytes with
  | none =>
    have hok : ((E3 P).view m.core).memWriteOk (memAt P ma) ptr bytes = false := by
      simp [CoreEngine.view, hw]
    rw [hok]
    exact Spec.trap _ _
  | some c' =>
    have hok : ((E3 P).view m.core).memWriteOk (memAt P ma) ptr bytes = true := by
      simp [CoreEngine.view, hw]
    rw [hok]
    refine Spec.mono (Spec.memWriteOp _ _ _) fun _ m' hm _ _ => ⟨c', hw, ?_⟩
    subst m'
    rw [hw]
    rfl

/-- A write keeps `LInv`, and is a `memWrite?` of the renamed stores. -/
theorem LInv.write {I : Silmaril.Wasm.Game.ScalarInstance} {ma : Nat} {m : Config (E3 P) Unit}
    (hi : LInv P I ma m) {ptr : Nat} {bytes : ByteArray} {c' : (E3 P).Store (CanonHost (E3 P))}
    (hw : Silmaril.Wasm.SingleThreaded.memWrite? m.core ma ptr bytes = some c') :
    LInv P I ma { m with core := c' } ∧
      Silmaril.Wasm.SingleThreaded.memWrite? (cmap m.core) ma ptr bytes =
        some (Store.mapH (fun _ => 0) c') := by
  have hm : Silmaril.Wasm.SingleThreaded.memWrite? (cmap m.core) ma ptr bytes =
      some (Store.mapH (fun _ => 0) c') := by
    have h := memWrite?_mapH (H := CanonHost (E3 P)) (fun _ => (0 : Nat)) m.core ma ptr bytes
    rw [hw] at h
    exact h
  refine ⟨⟨?_, wellFormed_memWrite? hi.wf hm⟩, hm⟩
  show Silmaril.Wasm.SingleThreaded.memAddrType? c' ma = some .i32
  rw [memWrite?_memAddrType hw]
  exact hi.mem

/-! ## The element loop -/

/-- An element store with a `Spec`: from every configuration with `LInv`, it keeps `LInv`,
grows, and relates the renamed core stores by `Elem`. -/
def ElemSpec (prof : ProfileKind) (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance)
    (ma : Nat) (th : Option ThreadId) {α : Type} (toV : α → Value.Val)
    (storeElem : Value.Val → Nat → Canon.P (E3 P) Unit Unit)
    (Elem : α → Nat → Silmaril.Wasm.Execution.Core.Store Nat →
      Silmaril.Wasm.Execution.Core.Store Nat → Prop) (u : α) : Prop :=
  ∀ a (m : Config (E3 P) Unit), LInv P I ma m → SpecR prof P th (storeElem (toV u) a) m
    (fun _ m' => LInv P I ma m' ∧ Grows m m' ∧ Elem u a (cmap m.core) (cmap m'.core))

/-- **The element loop** of `store_list_into_valid_range`, from index `k`. -/
theorem spec_storeElems {I : Silmaril.Wasm.Game.ScalarInstance} {ma : Nat} {th : Option ThreadId}
    {α : Type} (toV : α → Value.Val) (storeElem : Value.Val → Nat → Canon.P (E3 P) Unit Unit)
    (Elem : α → Nat → Silmaril.Wasm.Execution.Core.Store Nat →
      Silmaril.Wasm.Execution.Core.Store Nat → Prop) (size ptr : Nat) :
    ∀ (us : List α), (∀ u ∈ us, ElemSpec prof P I ma th toV storeElem Elem u) →
    ∀ (k : Nat) (m : Config (E3 P) Unit), LInv P I ma m →
      SpecR prof P th (Prog.forM ((us.map toV).zipIdx k)
        (fun (e, i) => storeElem e (ptr + i * size))) m
        (fun _ m' => LInv P I ma m' ∧ Grows m m' ∧
          ElemsRel size Elem us (ptr + k * size) (cmap m.core) (cmap m'.core))
  | [], _, k, m, hi =>
    Spec.mono (Spec.pure _) fun _ m' ⟨_, hm⟩ _ _ => by
      subst m'
      exact ⟨hi, Grows.refl _, .nil⟩
  | u :: us, hel, k, m, hi => by
    rw [List.map_cons, List.zipIdx_cons]
    refine Spec.bind (hel u List.mem_cons_self (ptr + k * size) m hi)
      fun _ m₁ ⟨hi₁, hg₁, he₁⟩ _ _ => ?_
    refine Spec.mono (spec_storeElems toV storeElem Elem size ptr us
      (fun u' hu' => hel u' (List.mem_cons_of_mem _ hu')) (k + 1) m₁ hi₁)
      fun _ m' ⟨hi', hg', he'⟩ _ _ => ⟨hi', hg₁.trans hg', .cons he₁ ?_⟩
    rw [show ptr + k * size + size = ptr + (k + 1) * size by rw [Nat.succ_mul]; omega]
    exact he'

/-! ## `allocate` and the checks -/

/-- `memLen` of the renamed store is the core store's memory size. -/
theorem memLen_cmap {c : (E3 P).Store (CanonHost (E3 P))} {ma N : Nat}
    (h : (E3 P).memSize? c (memAt P ma) = some N) : ListLift.memLen (cmap c) ma = N := by
  have h' : (c.mems[ma]?).map (·.bytes.size) = some N := h
  unfold ListLift.memLen
  show ((c.mems[ma]?).map (·.bytes.size)).getD 0 = N
  rw [h']
  rfl

/-- **`allocate`** in a lowering context. -/
theorem spec_allocate {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} {th : Option ThreadId}
    {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx) {m : Config (E3 P) Unit}
    (hi : LInv P I ma m) (align n : Nat) :
    SpecR prof P th (allocate cx align n) m
      (fun q m' => LInv P I ma m' ∧ Grows m m' ∧ AllocRun P I ra align n m.core m'.core q) := by
  unfold allocate reallocate callNat
  refine Spec.bind (Spec.call (spec_realloc hcx.alloc hcx.mem hcx.realloc hi.mem hi.wf align n))
    fun r m' ⟨p, hr, hrun, hcl, htv⟩ _ _ => ?_
  subst r
  refine Spec.mono (Spec.pure p) fun q m'' ⟨hq, hm⟩ _ _ => ?_
  subst q m''
  refine ⟨⟨hrun.mem _ _ hi.mem, hrun.wf⟩, ⟨?_, ?_⟩, hrun⟩
  · rw [hcl]
    exact List.prefix_append _ _
  · rw [htv]
    exact List.prefix_append _ _

/-- **`checkInBounds`** in a lowering context: the range lies in memory `ma`. -/
theorem spec_checkInBounds {th : Option ThreadId} {ma : Nat} {cx : LiftLowerContext (E3 P)}
    (hcx : cx.opts.memory = some (memAt P ma)) {m : Config (E3 P) Unit} (ptr size : Nat) :
    SpecR prof P th (checkInBounds cx ptr size) m
      (fun _ m' => ptr + size ≤ ListLift.memLen (cmap m.core) ma ∧ m' = m) := by
  unfold checkInBounds Canon.memLen memAddr
  rw [hcx]
  refine Spec.bind (Spec.bind (Spec.orTrap _ _) fun a m₁ ⟨ha, hm⟩ _ _ => ?_)
    (R := fun N m' => (E3 P).memSize? m.core (memAt P ma) = some N ∧ m' = m)
    fun N m₂ ⟨hN, hm⟩ _ _ => ?_
  · subst m₁
    cases ha
    refine Spec.bind Spec.readCore fun v m₂ ⟨hv, hm⟩ _ _ => ?_
    subst m₂ v
    exact Spec.mono (Spec.orTrap _ _) fun N m' ⟨hN, hm⟩ _ _ => ⟨hN, hm⟩
  · subst m₂
    refine Spec.mono (Spec.trapIf _ _) fun _ m' ⟨hc, hm⟩ _ _ => ⟨?_, hm⟩
    rw [memLen_cmap hN]
    simpa using hc

/-- The alignment check passes only at aligned pointers. -/
theorem mod_of_alignTo {ptr : Nat} {a : ABI.Alignment}
    (h : decide (ptr ≠ ABI.alignTo ptr a) = false) : ptr % a.bytes = 0 := by
  have h' : ptr = ABI.alignTo ptr a := by simpa using h
  rw [h']
  unfold ABI.alignTo
  exact Nat.mul_mod_left _ _

/-! ## `store_list_into_range` -/

/-- **`store_list_into_range`**, generic in the element layout and store, on an accepting
path: the allocator answers an aligned `q` for the list's bytes, which lie in memory, and the
elements are stored from `q` on. -/
theorem spec_storeListIntoRange {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat}
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)} (hcx : LowerCx P I ra ma cx)
    (el : ABI.Layout) {α : Type} (toV : α → Value.Val)
    (storeElem : Value.Val → Nat → Canon.P (E3 P) Unit Unit)
    (Elem : α → Nat → Silmaril.Wasm.Execution.Core.Store Nat →
      Silmaril.Wasm.Execution.Core.Store Nat → Prop)
    (us : List α) (hel : ∀ u ∈ us, ElemSpec prof P I ma th toV storeElem Elem u)
    {m : Config (E3 P) Unit} (hi : LInv P I ma m) :
    SpecR prof P th (storeListIntoRangeWith cx el storeElem (us.map toV)) m
      (fun r m' => LInv P I ma m' ∧ Grows m m' ∧ ∃ q s₁, r = (q, us.length) ∧
        ReallocRun P ra (cmap m.core) el.alignment.bytes (us.length * el.size) q s₁ ∧
        q % el.alignment.bytes = 0 ∧ q + us.length * el.size ≤ ListLift.memLen s₁ ma ∧
        ElemsRel el.size Elem us q s₁ (cmap m'.core)) := by
  unfold storeListIntoRangeWith
  rw [List.length_map]
  refine Spec.bind (spec_allocate hcx hi _ _) fun q m₁ ⟨hi₁, hg₁, hrun⟩ _ _ => ?_
  refine Spec.bind (Spec.trapIf _ _) fun _ m₂ ⟨ha, hm⟩ _ _ => ?_
  subst m₂
  refine Spec.bind (spec_checkInBounds hcx.mem _ _) fun _ m₃ ⟨hb, hm⟩ _ _ => ?_
  subst m₃
  refine Spec.bind (spec_storeElems toV storeElem Elem el.size q us hel 0 m₁ hi₁)
    fun _ m₄ ⟨hi₄, hg₄, he₄⟩ _ _ => ?_
  refine Spec.mono (Spec.pure _) fun r m' ⟨hr, hm⟩ _ _ => ?_
  subst r m'
  refine ⟨hi₄, hg₁.trans hg₄, q, cmap m₁.core, rfl, hrun.run, mod_of_alignTo ha, hb, ?_⟩
  simpa using he₄

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
