module

public import Silmaril.Wasm.Tools.Component.Dummy.Defs

/-!
# Theorems of the dummy module

* `mem_typeTable`, `typeTable_nodup`: the type section of the encoding holds every type the
  imports and functions use, once each (as `wat` interns implicit types), so `typeIdx` names
  each one's entry (`typeIdx_lt`, `getElem_typeIdx`).
* `memory_mem_exportsOf`: the memory is exported under the mangling's memory name.
* `dummy_tail`: the last two functions are `realloc` and `initialize` of the mangling.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Dummy

open Silmaril.Wasm.Component (CoreFuncTy)

/-- One step of the table fold. -/
def addTy (acc : List CoreFuncTy) (t : CoreFuncTy) : List CoreFuncTy :=
  if acc.contains t then acc else acc ++ [t]

theorem typeTable_eq (ts : List CoreFuncTy) : typeTable ts = ts.foldl addTy [] := rfl

theorem mem_addTy_left {acc : List CoreFuncTy} {t u : CoreFuncTy} (h : u ∈ acc) :
    u ∈ addTy acc t := by
  unfold addTy
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_addTy_self (acc : List CoreFuncTy) (t : CoreFuncTy) : t ∈ addTy acc t := by
  unfold addTy
  split
  · rename_i h
    exact List.contains_iff_mem.mp h
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem mem_foldl_addTy : ∀ (ts acc : List CoreFuncTy) (t : CoreFuncTy),
    t ∈ acc ∨ t ∈ ts → t ∈ ts.foldl addTy acc
  | [], _, _, h => by
    rcases h with h | h
    · exact h
    · cases h
  | x :: xs, acc, t, h => by
    rw [List.foldl_cons]
    apply mem_foldl_addTy xs
    rcases h with h | h
    · exact Or.inl (mem_addTy_left h)
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Or.inl (mem_addTy_self acc t)
      · exact Or.inr h

/-- Every used type is in the table. -/
theorem mem_typeTable {ts : List CoreFuncTy} {t : CoreFuncTy} (h : t ∈ ts) :
    t ∈ typeTable ts :=
  mem_foldl_addTy ts [] t (Or.inr h)

theorem nodup_addTy {acc : List CoreFuncTy} (h : acc.Nodup) (t : CoreFuncTy) :
    (addTy acc t).Nodup := by
  unfold addTy
  split
  · exact h
  · rename_i hc
    have hn : t ∉ acc := fun hm => hc (List.contains_iff_mem.mpr hm)
    exact List.nodup_append.mpr ⟨h, List.nodup_singleton t, by
      intro a ha b hb hab
      rw [List.mem_singleton.mp hb] at hab
      exact hn (hab ▸ ha)⟩

theorem nodup_foldl_addTy : ∀ (ts acc : List CoreFuncTy), acc.Nodup →
    (ts.foldl addTy acc).Nodup
  | [], _, h => h
  | x :: xs, acc, h => by
    rw [List.foldl_cons]
    exact nodup_foldl_addTy xs _ (nodup_addTy h x)

/-- Every type is in the table once. -/
theorem typeTable_nodup (ts : List CoreFuncTy) : (typeTable ts).Nodup :=
  nodup_foldl_addTy ts [] List.nodup_nil

theorem typeIdx_lt {tab : List CoreFuncTy} {t : CoreFuncTy} (h : t ∈ tab) :
    typeIdx tab t < tab.length :=
  List.idxOf_lt_length_of_mem h

/-- `typeIdx` names the type's entry. -/
theorem getElem_typeIdx {tab : List CoreFuncTy} {t : CoreFuncTy} (h : t ∈ tab) :
    tab[typeIdx tab t]'(typeIdx_lt h) = t :=
  List.getElem_idxOf (typeIdx_lt h)

/-- The memory is exported under the mangling's name. -/
theorem memory_mem_exportsOf (d : Module) :
    (memoryName d.mangling, (0x02 : UInt8), 0) ∈ exportsOf d := by
  unfold exportsOf
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

theorem bind_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The dummy module's last two functions are `realloc` and `initialize`. -/
theorem dummy_tail {wf : Wit.Binary.WorldFull} {m : Mangling} {d : Module}
    (h : dummy wf m = .ok d) :
    ∃ fs, d.funcs = fs ++ [⟨reallocName m, ⟨[t32, t32, t32, t32], [t32]⟩, true⟩,
      ⟨initializeName m, ⟨[], []⟩, false⟩] ∧ d.mangling = m := by
  unfold dummy at h
  obtain ⟨is, _, h⟩ := bind_ok' h
  obtain ⟨fs, _, h⟩ := bind_ok' h
  cases h
  exact ⟨fs, rfl, rfl⟩

end Silmaril.Wasm.Tools.Component.Dummy
