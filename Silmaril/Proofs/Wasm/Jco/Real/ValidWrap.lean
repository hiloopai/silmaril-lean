module

public import Silmaril.Wasm.Jco.Real.ValidAll.Thms
public import Silmaril.Wasm.Validation.Instructions.Properties

/-!
# The adaptor is invalid from `|world| = 2^31` on: proofs

For `2^31 ≤ N < 2^32 - 2`, the world `wrapMeta N` has `N` functions `a^k : (u32, u32, u32) -> ()`
with distinct names. In `adaptorLime (wrapMeta N)` the shim of world function
`i₀ = 2^32 - N - 2` has type index `N + 2 + i₀ = 2^32`, which `mkIdx` reduces to `0`: the
allocator's type `(i32, i32) -> i32`. Its body `local.get 0; local.get 1; local.get 2; call f`
then reads local `2` of a function with two locals, so the Core 3.0 module is invalid.

The proof inverts Core 3.0 validation symbolically, without evaluating the module:

* `getsOk`: in every Core typing of an instruction sequence, each `local.get x` of the sequence
  reads a local that exists. This is an induction over `InstrsOk` (`InstrsOk.ind`); `seq` and
  `cons` move to `C.initLocals xs`, which has the same locals (`initLocals_isSome`), and `sub`
  and `frame` keep the context.
* the types of the module context are `types.map toDefType` (`TypesOk.det` against the Lime1 →
  Core 3.0 typing `typesOk_map`), so type index `0` is the allocator's type.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real.ValidWrap

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Real

/-! ## Inversion of instruction typing -/

/-- A `local.get x` typing reads an existing local. -/
theorem localGet_inv {C : Context} {x : LocalIdx} {it : InstrType}
    (h : InstrOk C (.localGet x) it) : (C.locals[x.toNat]?).isSome := by
  cases h <;> rename_i h <;> cases h
  simp_all

/-- `localGet_inv` with the instruction as an equation. -/
theorem localGet_inv' {C : Context} {i : Instr} {x : LocalIdx} {it : InstrType}
    (h : InstrOk C i it) (hi : i = .localGet x) : (C.locals[x.toNat]?).isSome :=
  localGet_inv (hi ▸ h)

/-- A local that exists after `initLocals` exists before. -/
theorem isSome_of_init {C : Context} {xs : List Nat} {y : Nat}
    (h : ((C.initLocals xs).locals[y]?).isSome) : (C.locals[y]?).isSome :=
  Context.initLocals_isSome.symm.trans h

/-- **In every typing of an instruction sequence, each `local.get x` reads an existing local.** -/
theorem getsOk {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ x : LocalIdx, Instr.localGet x ∈ is → (C.locals[x.toNat]?).isSome := by
  induction h using InstrsOk.ind with
  | nil => exact fun _ hx => absurd hx List.not_mem_nil
  | instr hi => exact fun _ hx => localGet_inv' hi (List.mem_singleton.1 hx).symm
  | seq _ _ _ ih₁ ih₂ =>
    exact fun x hx => (List.mem_append.1 hx).elim (ih₁ x) (fun h => isSome_of_init (ih₂ x h))
  | cons hi _ _ ih =>
    exact fun x hx => (List.mem_cons.1 hx).elim (fun e => localGet_inv' hi e.symm)
      (fun h => isSome_of_init (ih x h))
  | sub _ _ _ ih => exact ih
  | frame _ _ ih => exact ih

/-- A member of the left list of `Forall₂` has a partner. -/
theorem forall₂_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, ha => by cases ha
  | _, _, .cons hab hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, hab⟩
    · exact forall₂_left hs a ha

/-! ## The world -/

/-- The name `a^k`. -/
def nm (k : Nat) : String := String.ofList (List.replicate k 'a')

theorem nm_inj : Function.Injective nm := by
  intro a b h
  have := congrArg String.toList h
  simp only [nm, String.toList_ofList] at this
  simpa using congrArg List.length this

/-- World function `k`: `a^k : (u32, u32, u32) -> ()`. -/
def wsig (k : Nat) : Sig := ⟨nm k, [.val .u32, .val .u32, .val .u32], none⟩

/-- A world of `N` functions with distinct names; the allocator is `b`. -/
def wrapMeta (N : Nat) : Meta := ⟨(List.range N).map wsig, "b"⟩

theorem wrapMeta_length (N : Nat) : (wrapMeta N).world.length = N := by simp [wrapMeta]

theorem not_b_nm (k : Nat) : "b" ≠ nm k := by
  intro h
  have := congrArg String.toList h
  simp only [nm, String.toList_ofList] at this
  cases k with
  | zero => simp at this
  | succ k => simp [List.replicate_succ] at this

theorem not_realloc_nm (k : Nat) : "cabi_realloc" ≠ nm k := by
  intro h
  have := congrArg String.toList h
  simp only [nm, String.toList_ofList] at this
  have hm : 'c' ∈ List.replicate k 'a' := by rw [← this]; decide
  simp at hm

theorem wrapMeta_nodup (N : Nat) : (importNames (wrapMeta N)).Nodup := by
  simp only [importNames, wrapMeta, List.map_map]
  refine List.nodup_cons.2 ⟨?_, (List.nodup_range).map nm_inj⟩
  simp only [List.mem_map, List.mem_range, Function.comp_apply, wsig, not_exists, not_and]
  exact fun k _ h => not_b_nm k h.symm

theorem wrapMeta_realloc (N : Nat) :
    "cabi_realloc" ∉ (wrapMeta N).world.map (·.name) := by
  simp only [wrapMeta, List.map_map, List.mem_map, List.mem_range, Function.comp_apply, wsig,
    not_exists, not_and]
  exact fun k _ h => not_realloc_nm k h.symm

theorem wrapMeta_params (N : Nat) :
    ∀ s ∈ (wrapMeta N).world, (flatParams s.params).length + 2 < 2 ^ 32 := by
  intro s hs
  simp only [wrapMeta, List.mem_map, List.mem_range] at hs
  obtain ⟨k, -, rfl⟩ := hs
  simp only [wsig]
  decide

/-! ## The wrapped shim -/

/-- The Core image of the shim of world function `i` at type index `ty`. -/
abbrev shimC (N i ty : Nat) : Func :=
  Lime1.Func.toCore ((exportShim (wrapMeta N) (wsig i)).toX.toLime (funcIdxOf (wrapMeta N)) ty)

theorem shimC_mem {N i : Nat} (hi : i < N) :
    shimC N i (N + 2 + i) ∈ (adaptorLime (wrapMeta N)).toCore.funcs := by
  have hz : (wsig i, i) ∈ (wrapMeta N).world.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp [wrapMeta, hi]
  simp only [adaptorLime, Lime1.Module.toCore, List.map_cons, List.mem_cons, List.mem_map]
  exact Or.inr ⟨_, ⟨_, hz, rfl⟩, by rw [wrapMeta_length]⟩

theorem shimC_locals (N i ty : Nat) : (shimC N i ty).locals = [] := by
  simp [shimC, Lime1.Func.toCore, XFn.toLime, exportShim, wsig, inMem, AFn.toX]

theorem shimC_type (N i ty : Nat) : (shimC N i ty).type = mkIdx ty := by
  simp [shimC, Lime1.Func.toCore, XFn.toLime]

theorem shimC_body (N i ty : Nat) : (shimC N i ty).body =
    [.localGet (mkIdx 0), .localGet (mkIdx 1), .localGet (mkIdx 2),
      .call (mkIdx (funcIdxOf (wrapMeta N) (nm i)))] := rfl

theorem shimC_get2 (N i ty : Nat) : Instr.localGet (mkIdx 2) ∈ (shimC N i ty).body := by
  rw [shimC_body]
  simp

/-- **A shim at a type index that wraps to `0` is ill typed**: at the allocator's type
`(i32, i32) -> i32` it has two locals, and its body reads local `2`. -/
theorem shimC_not_ok {C : Context} (hT : C.types[0]? = some allocType.toDefType)
    (N i ty : Nat) (hty : ty % 2 ^ 32 = 0) (d : DefType) : ¬ FuncOk C (shimC N i ty) d := by
  intro h
  cases h with
  | @mk ps rs lts hd he hl hb =>
    have hd0 : some d = some allocType.toDefType := by
      rw [← hd, ← hT, Context.type?, shimC_type, Silmaril.Proofs.Wasm.Jco.Real.ValidAll.mkIdx_toNat, hty]
    have hx : (Silmaril.Wasm.Validation.Ty.func ps rs : CCompType) = Silmaril.Wasm.Validation.Ty.func (Silmaril.Wasm.Validation.Ty.ofList (allocType.params.map Silmaril.Wasm.Validation.Ty.num))
        (Silmaril.Wasm.Validation.Ty.ofList (allocType.results.map Silmaril.Wasm.Validation.Ty.num)) :=
      Option.some.inj ((Expand.iff.mp he).symm.trans
        (Expand.iff.mp (Option.some.inj hd0 ▸ Lime1.Validation.expand_toDefType allocType)))
    have hps : ps = Silmaril.Wasm.Validation.Ty.ofList (allocType.params.map Silmaril.Wasm.Validation.Ty.num) := by injection hx
    have hlts : lts = [] := List.forall₂_nil_left_iff.1 (shimC_locals N i ty ▸ hl)
    have hg : ((C.funcBody ps.toList rs.toList lts).locals[(mkIdx 2 : LocalIdx).toNat]?).isSome :=
      getsOk hb _ (shimC_get2 N i ty)
    have hnone : (C.funcBody ps.toList rs.toList lts).locals[(mkIdx 2 : LocalIdx).toNat]? = none := by
      rw [hps, hlts]
      rfl
    exact absurd hg (by rw [hnone]; decide)

/-- **For `2^31 ≤ N < 2^32 - 2`, the adaptor of `wrapMeta N` is not a valid Core 3.0 module.** -/
theorem adaptorLime_wrapMeta_invalid {N : Nat} (h₁ : 2 ^ 31 ≤ N) (h₂ : N + 2 < 2 ^ 32) :
    ¬ ModuleValid (adaptorLime (wrapMeta N)).toCore := by
  rintro ⟨_, hm⟩
  cases hm with
  | @mk dts _ _ _ _ _ _ _ C' C htypes _ hC' hC _ _ _ _ hfuncs =>
    have hdts := TypesOk.det htypes (Lime1.Validation.typesOk_map _ {})
    have hT0 : C.types[0]? = some allocType.toDefType := by
      rw [hC, hC', hdts]
      rfl
    obtain ⟨d, hf⟩ := forall₂_left hfuncs _ (shimC_mem (i := 2 ^ 32 - N - 2) (by omega))
    exact shimC_not_ok hT0 N _ _ (by omega) d hf

/-- **`AdaptorLimeValid` is false**: `wrapMeta (2^31)` satisfies its hypotheses. -/
theorem not_adaptorLime_valid : ¬ AdaptorLimeValid := by
  intro h
  exact adaptorLime_wrapMeta_invalid (N := 2 ^ 31) (le_refl _) (by decide)
    (h _ (wrapMeta_nodup _) (wrapMeta_realloc _) (wrapMeta_params _)
      (by rw [wrapMeta_length]; decide))

end Silmaril.Proofs.Wasm.Jco.Real.ValidWrap
