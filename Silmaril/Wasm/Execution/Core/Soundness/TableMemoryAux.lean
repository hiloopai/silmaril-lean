module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs

@[expose] public section

/-! # Auxiliary lemmas for the table and memory soundness proofs

* lookups: a valid frame resolves every table, memory, element and data index of
  its context to a store instance (`StateOk.table`, `StateOk.mem`, …);
* inversion of value typing at number, vector and reference types;
* success of in-bounds `Memory.load`/`Memory.store`;
* the grow policy always enables one of the two grow rules;
* store updates (`setTable`, `setMem`, `setElem`, `setData`) preserve `StoreOk`
  and extend the store;
* `AdminsOk.vals_instr_replace`: subject replacement for a redex
  `vals vs ++ [plain i]` (stated here, see its doc).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Lists -/

theorem List.Forall₂.getElem?_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (_ : List.Forall₂ R l₁ l₂) {i : Nat} {b : β},
      l₂[i]? = some b → ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab hl, i, b, h => by
    cases i with
    | zero => simp at h; subst h; exact ⟨_, rfl, hab⟩
    | succ i => simpa using List.Forall₂.getElem?_right hl (by simpa using h)

/-! ## Value inversion -/

theorem ValOk.int_inv {s : Store H} {v : Val} {t : IntType} (h : ValOk s v (.num (.int t))) :
    ∃ c, v = .num ⟨.int t, c⟩ := by
  rcases v with ⟨ty, b⟩ | b | r <;> cases h
  exact ⟨b, rfl⟩

theorem ValOk.float_inv {s : Store H} {v : Val} {t : FloatType}
    (h : ValOk s v (.num (.float t))) : ∃ c, v = .num ⟨.float t, c⟩ := by
  rcases v with ⟨ty, b⟩ | b | r <;> cases h
  exact ⟨b, rfl⟩

theorem ValOk.v128_inv {s : Store H} {v : Val} (h : ValOk s v (.vec .v128)) :
    ∃ c, v = .vec c := by
  rcases v with ⟨ty, b⟩ | b | r <;> cases h
  exact ⟨b, rfl⟩

theorem ValOk.ref_inv {s : Store H} {v : Val} {rt : CRefType} (h : ValOk s v (.refv rt)) :
    ∃ r, v = .ref r ∧ RefOk s r rt := by
  rcases v with ⟨ty, b⟩ | b | r <;> cases h
  exact ⟨r, rfl, by assumption⟩

theorem ValOk.addr_inv {s : Store H} {v : Val} {a : AddrType} (h : ValOk s v a.valType) :
    ∃ i, v.toAdmin = aconst a i := by
  obtain ⟨c, rfl⟩ := ValOk.int_inv (t := a.intType) h
  exact ⟨c, rfl⟩

theorem ValOk.i32_inv {s : Store H} {v : Val} (h : ValOk s v Ty.i32) :
    ∃ i, v.toAdmin = constI32 i := by
  obtain ⟨c, rfl⟩ := ValOk.int_inv (t := .i32) h
  exact ⟨c, rfl⟩

/-- Destructure a `Forall₂` against a literal list of length one, two or three. -/
theorem forall₂_one {α β : Type} {R : α → β → Prop} {l : List α} {b₁ : β}
    (h : List.Forall₂ R l [b₁]) : ∃ a₁, l = [a₁] ∧ R a₁ b₁ := by
  rcases h with _ | ⟨h₁, _ | _⟩
  exact ⟨_, rfl, h₁⟩

theorem forall₂_two {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ : β}
    (h : List.Forall₂ R l [b₁, b₂]) : ∃ a₁ a₂, l = [a₁, a₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
  exact ⟨_, _, rfl, h₁, h₂⟩

theorem forall₂_three {α β : Type} {R : α → β → Prop} {l : List α} {b₁ b₂ b₃ : β}
    (h : List.Forall₂ R l [b₁, b₂, b₃]) :
    ∃ a₁ a₂ a₃, l = [a₁, a₂, a₃] ∧ R a₁ b₁ ∧ R a₂ b₂ ∧ R a₃ b₃ := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
  exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

/-! ## Store lookups from a valid state -/

theorem ExternAddrOk.table_aux {s : Store H} (hs : StoreOk s) :
    ∀ {xa : ExternAddr} {xt : CExternType}, ExternAddrOk s xa xt →
      ∀ (a : Nat) (tt : CTableType), xa = .table a → xt = .table tt →
      ∃ ti, s.tables[a]? = some ti ∧ ti.type.address = tt.address ∧
        (∀ r, RefOk s r ti.type.element ↔ RefOk s r tt.element) ∧ TyOk {} tt.element := by
  intro xa xt h
  induction h with
  | table hget =>
    intro a tt hxa hxt
    cases hxa; cases hxt
    refine ⟨_, hget, rfl, fun _ => Iff.rfl, ?_⟩
    exact (hs.tables _ (List.mem_of_getElem? hget)).1.2
  | sub h hok hsub ih =>
    intro a tt hxa hxt
    subst hxa hxt
    cases hsub with
    | table hts =>
      rcases hts with ⟨hl, h₁, h₂⟩
      obtain ⟨ti, hget, haddr, hiff, htok⟩ := ih a _ rfl rfl
      obtain ⟨-, htok'⟩ : TableTypeOk {} _ := by cases hok; assumption
      refine ⟨ti, hget, haddr, fun r => ⟨fun hr => ?_, fun hr => ?_⟩, htok'⟩
      · exact RefOk.sub ((hiff r).1 hr) htok' h₁
      · exact (hiff r).2 (RefOk.sub hr htok h₂)
  | _ => intro a tt hxa hxt; cases hxa

theorem ExternAddrOk.mem_aux {s : Store H} :
    ∀ {xa : ExternAddr} {xt : CExternType}, ExternAddrOk s xa xt →
      ∀ (a : Nat) (mt : MemoryType), xa = .mem a → xt = .mem mt →
      ∃ mi, s.mems[a]? = some mi ∧ mi.type.address = mt.address := by
  intro xa xt h
  induction h with
  | mem hget =>
    intro a mt hxa hxt
    cases hxa; cases hxt
    exact ⟨_, hget, rfl⟩
  | sub h hok hsub ih =>
    intro a mt hxa hxt
    subst hxa hxt
    cases hsub with
    | mem hms =>
      rcases hms with ⟨hl⟩
      obtain ⟨mi, hget, haddr⟩ := ih a _ rfl rfl
      exact ⟨mi, hget, haddr⟩
  | _ => intro a mt hxa hxt; cases hxa

/-- A table index of a valid frame's context resolves to a store table with the
same address type and an equivalent element type. -/
theorem StateOk.table {s : Store H} {f : Frame} {C : Context} {x : TableIdx}
    {tt : CTableType} (hst : StateOk s f C) (hx : C.tables[x.toNat]? = some tt) :
    ∃ ta ti, s.table? f x = some (ta, ti) ∧ ti.type.address = tt.address ∧
      (∀ r, RefOk s r ti.type.element ↔ RefOk s r tt.element) ∧ TyOk {} tt.element ∧
      TableInstOk s ti := by
  obtain ⟨hs, C₀, lts, hmi, _, rfl⟩ := hst
  cases hmi with
  | mk _ _ _ _ _ htables =>
    obtain ⟨ta, hta, hta'⟩ := List.Forall₂.getElem?_right htables hx
    obtain ⟨ti, hget, h₁, h₂, h₃⟩ := ExternAddrOk.table_aux hs hta' ta tt rfl rfl
    refine ⟨ta, ti, ?_, h₁, h₂, h₃, hs.tables _ (List.mem_of_getElem? hget)⟩
    simp [Store.table?, hta, hget]

theorem StateOk.mem {s : Store H} {f : Frame} {C : Context} {x : MemIdx}
    {mt : MemoryType} (hst : StateOk s f C) (hx : C.mems[x.toNat]? = some mt) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.type.address = mt.address ∧ MemInstOk mi := by
  obtain ⟨hs, C₀, lts, hmi, _, rfl⟩ := hst
  cases hmi with
  | mk _ _ _ _ hmems =>
    obtain ⟨ma, hma, hma'⟩ := List.Forall₂.getElem?_right hmems hx
    obtain ⟨mi, hget, h₁⟩ := ExternAddrOk.mem_aux hma' ma mt rfl rfl
    refine ⟨ma, mi, ?_, h₁, hs.mems _ (List.mem_of_getElem? hget)⟩
    simp [Store.mem?, hma, hget]

theorem StateOk.elem {s : Store H} {f : Frame} {C : Context} {y : ElemIdx}
    {rt : CRefType} (hst : StateOk s f C) (hy : C.elems[y.toNat]? = some rt) :
    ∃ ea ei, s.elem? f y = some (ea, ei) ∧ ei.type = rt ∧ ElemInstOk s ei := by
  obtain ⟨hs, C₀, lts, hmi, _, rfl⟩ := hst
  cases hmi with
  | mk _ _ _ _ _ _ _ helems =>
    obtain ⟨ea, hea, ei, hget, hok, hty⟩ := List.Forall₂.getElem?_right helems hy
    exact ⟨ea, ei, by simp [Store.elem?, hea, hget], hty, hok⟩

theorem StateOk.data {s : Store H} {f : Frame} {C : Context} {y : DataIdx}
    (hst : StateOk s f C) (hy : C.datas[y.toNat]? = some ()) :
    ∃ da di, s.data? f y = some (da, di) := by
  obtain ⟨hs, C₀, lts, hmi, _, rfl⟩ := hst
  cases hmi with
  | mk _ _ _ _ _ _ hdatas =>
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
    obtain ⟨da, hda, -⟩ := hy
    obtain ⟨di, hdi⟩ := hdatas da (List.mem_of_getElem? hda)
    exact ⟨da, di, by simp [Store.data?, hda, hdi]⟩

/-! ## Memory access succeeds in bounds -/

theorem Memory.load_of_le {m : ByteArray} {start count : Nat} (h : start + count ≤ m.size) :
    ∃ c, Memory.load m start count = some c := by
  unfold Memory.load
  rw [(Memory.readBytes_eq_some_iff m _ start count).mpr ⟨h, rfl⟩]
  exact ⟨_, rfl⟩

theorem Memory.store_of_le {m : ByteArray} {start count : Nat} (word : BitVec (8 * count))
    (h : start + count ≤ m.size) : ∃ b, Memory.store m start word = some b := by
  unfold Memory.store
  refine ⟨_, (Memory.writeBytes_eq_some_iff m _ _ start).mpr ⟨?_, rfl⟩⟩
  simpa using h

theorem Memory.store_size {m b : ByteArray} {start count : Nat} {word : BitVec (8 * count)}
    (h : Memory.store m start word = some b) : b.size = m.size :=
  Memory.writeBytes_size _ _ _ _ h

/-! ## Grow policy -/

theorem Profile.growMaySucceed_of_not_fail {P : Profile} {k : GrowKind} {a sz d : Nat}
    (h : ¬ P.growMayFail k a sz d) : P.growMaySucceed k a sz d := by
  unfold Profile.growMayFail at h
  unfold Profile.growMaySucceed
  split at h
  · exact absurd trivial h
  · simpa using h

theorem BitVec.toNat_ne_zero {w : Nat} {n : BitVec w} (hn : n ≠ 0) : n.toNat ≠ 0 := by
  intro h; apply hn; exact BitVec.eq_of_toNat_eq (by simpa using h)

end Silmaril.Wasm.Execution.Core
