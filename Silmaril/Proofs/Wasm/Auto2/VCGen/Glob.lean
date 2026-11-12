module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Basic

/-!
# The VC generator: stores with globals set (`setGs`)

`setGs s m G` sets the globals `0, …, k - 1` of `m` to the values `G`. With distinct addresses
(`Distinct`): reading global `g` gives `G[g]` (`globals_setGs`), `global.set` of global `g` is
`setGs` with `G.set g v` (`setGlobal_setGs`), and setting the values the globals already hold
changes nothing (`setGs_self`). `setGs` commutes with the memory updates (`upd_setGs`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The first `k` globals of `m` have distinct addresses. -/
def Distinct (m : ModuleInst) (k : Nat) : Prop :=
  ∀ g g' a, g < k → g' < k → m.globals[g]? = some a → m.globals[g']? = some a → g = g'

theorem setGs_mems (s : Store H) (m : ModuleInst) (G : List Val) : (setGs s m G).mems = s.mems :=
  rfl

theorem setGs_funcs (s : Store H) (m : ModuleInst) (G : List Val) :
    (setGs s m G).funcs = s.funcs := rfl

theorem setGs_setMem (s : Store H) (m : ModuleInst) (G : List Val) (a : Nat) (mi : MemInst) :
    (setGs s m G).setMem a mi = setGs (s.setMem a mi) m G := rfl

theorem setM_setGs (s : Store H) (m mi : ModuleInst) (G : List Val) (B : ByteArray) :
    setM (setGs s m G) mi B = setGs (setM s mi B) m G := by
  unfold setM
  split
  · rw [setGs_mems]
    split
    · exact setGs_setMem _ _ _ _ _
    · rfl
  · rfl

theorem upd_setGs (S : FnSpec) (s : Store H) (m mi : ModuleInst) (G : List Val) (B : ByteArray) :
    upd S (setGs s m G) mi B = setGs (upd S s mi B) m G := by
  unfold upd
  split
  · exact setM_setGs s m mi G B
  · rfl

theorem gval_nil (m : ModuleInst) (a : Nat) : gval m [] a = none := by
  simp [gval]

theorem setGs_nil (s : Store H) (m : ModuleInst) : setGs s m [] = s := by
  cases s
  simp only [setGs, gval_nil]
  congr
  exact List.ext_getElem (by simp) fun i _ _ => by simp

theorem length_setGs (s : Store H) (m : ModuleInst) (G : List Val) :
    (setGs s m G).globals.length = s.globals.length := by
  simp [setGs]

/-- The value of an address: the global `g` it belongs to. -/
theorem gval_eq {m : ModuleInst} {G : List Val} {a g : Nat} (hD : Distinct m G.length)
    (hg : g < G.length) (ha : m.globals[g]? = some a) : gval m G a = some G[g] := by
  unfold gval
  rcases hf : (List.range G.length).find? (fun g => m.globals[g]? == some a) with _ | g''
  · have := List.find?_eq_none.mp hf g (List.mem_range.mpr hg)
    simp [ha] at this
  · have hp0 := List.find?_some hf
    have hp : (m.globals[g'']? == some a) = true := hp0
    have hm : g'' < G.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have he : g'' = g := hD g'' g a hm hg (by simpa using hp) ha
    subst he
    simp [List.getElem?_eq_getElem hg]

/-- An address of no global `g < k`. -/
theorem gval_none {m : ModuleInst} {G : List Val} {a : Nat}
    (h : ∀ g < G.length, m.globals[g]? ≠ some a) : gval m G a = none := by
  unfold gval
  rcases hf : (List.range G.length).find? (fun g => m.globals[g]? == some a) with _ | g''
  · rfl
  · have hp0 := List.find?_some hf
    have hp : (m.globals[g'']? == some a) = true := hp0
    have hm : g'' < G.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    exact absurd (by simpa using hp) (h g'' hm)

/-- **Reading a global after `setGs`.** -/
theorem globals_setGs {s : Store H} {m : ModuleInst} {G : List Val} {a g : Nat}
    {gi : GlobalInst} (hD : Distinct m G.length) (hg : g < G.length)
    (ha : m.globals[g]? = some a) (hs : s.globals[a]? = some gi) :
    (setGs s m G).globals[a]? = some { gi with value := G[g] } := by
  simp [setGs, hs, gval_eq hD hg ha]

theorem gval_set {m : ModuleInst} {G : List Val} {a g i : Nat} {v : Val}
    (ha : m.globals[g]? = some a) (hi : i ≠ a) :
    gval m (G.set g v) i = gval m G i := by
  unfold gval
  simp only [List.length_set]
  rcases hf : (List.range G.length).find? (fun g => m.globals[g]? == some i) with _ | g''
  · rfl
  · have hp0 := List.find?_some hf
    have hp : (m.globals[g'']? == some i) = true := hp0
    have hne : g'' ≠ g := by
      rintro rfl
      exact hi (Option.some.inj ((by simpa using hp : m.globals[g'']? = some i).symm.trans ha))
    simp [List.getElem?_set, Ne.symm hne]

/-- **`global.set` after `setGs`** is `setGs` with the new value. -/
theorem setGlobal_setGs {s : Store H} {m : ModuleInst} {G : List Val} {a g : Nat} {v : Val}
    (hD : Distinct m G.length) (hg : g < G.length) (ha : m.globals[g]? = some a) :
    (setGs s m G).setGlobal a v = setGs s m (G.set g v) := by
  have hD' : Distinct m (G.set g v).length := by simpa using hD
  have hg' : g < (G.set g v).length := by simpa using hg
  cases s
  simp only [Store.setGlobal, setGs, Store.mk.injEq, and_true, true_and]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_modify, List.getElem_mapIdx]
  by_cases hi : a = i
  · subst hi
    simp [gval_eq hD hg ha, gval_eq hD' hg' ha]
  · simp only [hi, ↓reduceIte, gval_set ha (Ne.symm hi)]

/-- An address `gval` gives a value for holds that value, if every global holds its value. -/
theorem value_of_gval {s : Store H} {m : ModuleInst} {G : List Val} {i : Nat} {v : Val}
    (hv : ∀ g (hg : g < G.length), ∃ a gi, m.globals[g]? = some a ∧ s.globals[a]? = some gi ∧
      gi.value = G[g]) (hgv : gval m G i = some v) {gi : GlobalInst}
    (hs : s.globals[i]? = some gi) : gi.value = v := by
  unfold gval at hgv
  rcases hf : (List.range G.length).find? (fun g => m.globals[g]? == some i) with _ | g''
  · simp [hf] at hgv
  · have hp0 := List.find?_some hf
    have hp : m.globals[g'']? = some i := by simpa using hp0
    have hm : g'' < G.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    rw [hf] at hgv
    simp only [Option.bind_some, List.getElem?_eq_getElem hm, Option.some.injEq] at hgv
    obtain ⟨a, gi', ha, hs', hval⟩ := hv g'' hm
    have hai : a = i := Option.some.inj (ha.symm.trans hp)
    subst hai
    have hgi : gi' = gi := Option.some.inj (hs'.symm.trans hs)
    rw [← hgi, hval, hgv]

/-- **Setting the values the globals hold** changes nothing. -/
theorem setGs_self {s : Store H} {m : ModuleInst} {G : List Val}
    (hv : ∀ g (hg : g < G.length), ∃ a gi, m.globals[g]? = some a ∧ s.globals[a]? = some gi ∧
      gi.value = G[g]) :
    setGs s m G = s := by
  cases s
  simp only [setGs, Store.mk.injEq, and_true, true_and]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_mapIdx]
  split
  · rename_i v hgv
    have hval := value_of_gval hv hgv (List.getElem?_eq_getElem h₂)
    rw [← hval]
  · rfl

/-! ## Setting a prefix of the globals again (calls) -/

/-- The value of an address after setting the globals `G₁`, then a prefix `G₂` of them: `G₂`'s
if it has one, else `G₁`'s. -/
theorem gval_prefix {m : ModuleInst} {G₁ G₂ : List Val} {a : Nat} (hk : G₂.length ≤ G₁.length) :
    gval m (G₂ ++ G₁.drop G₂.length) a = (gval m G₂ a).or (gval m G₁ a) := by
  obtain ⟨d, hd⟩ : ∃ d, G₁.length = G₂.length + d := ⟨G₁.length - G₂.length, by omega⟩
  have hlen : (G₂ ++ G₁.drop G₂.length).length = G₂.length + d := by simp; omega
  unfold gval
  rw [hlen, hd, List.range_add, List.find?_append]
  cases hf : (List.range G₂.length).find? (fun g => m.globals[g]? == some a) with
  | some g =>
    have hg : g < G₂.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp [List.getElem?_append_left hg, List.getElem?_eq_getElem hg]
  | none =>
    cases hf' : (List.map (G₂.length + ·) (List.range d)).find?
        (fun g => m.globals[g]? == some a) with
    | none => simp
    | some g =>
      have hg : G₂.length ≤ g := by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf')
        omega
      simp [List.getElem?_append_right hg, show G₂.length + (g - G₂.length) = g by omega]

/-- **Setting the globals `G₁`, then a prefix `G₂`** is setting `G₂` followed by the rest of
`G₁`. -/
theorem setGs_setGs {s : Store H} {m : ModuleInst} {G₁ G₂ : List Val}
    (hk : G₂.length ≤ G₁.length) :
    setGs (setGs s m G₁) m G₂ = setGs s m (G₂ ++ G₁.drop G₂.length) := by
  cases s
  simp only [setGs, Store.mk.injEq, and_true, true_and]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_mapIdx, gval_prefix hk]
  cases gval m G₂ i <;> cases gval m G₁ i <;> rfl

end Silmaril.Wasm.Auto2.VCGen
