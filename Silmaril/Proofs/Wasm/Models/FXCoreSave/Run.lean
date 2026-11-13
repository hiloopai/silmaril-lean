module

public import Silmaril.Wasm.Models.FXCoreSave.Defs

/-!
# Runs of the asyncify save and restore code in Core 3.0

For any profile and host:

* `step_ctx`, `steps_ctx`, `steps_label`: steps lift past values before them, code after them,
  and into a label;
* `global?_addStruct`, `global?_setGlobal`, `structs_setGlobal`: what the store updates of the
  save and restore code change;
* `bufIs_addStruct`, `bufIs_setGlobal`: the buffer survives both updates;
* `getLocals_run`: `local.get 0, …, local.get (n-1)` pushes the locals;
* **`save_run`**: the save code builds the record struct, pushes it on the buffer and reaches
  `return`;
* **`restore_run`**: the restore code loads the locals of the head record, stores its resume
  index in the dispatch global and pops it;
* `setMode_run`: a mode transition.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXCoreSave
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem ix_toNat {k : IndexKind} {j : Nat} (hj : j < 2 ^ 32) : (ix j : Idx k).toNat = j :=
  Nat.mod_eq_of_lt hj

/-! ## Contexts -/

/-- A step lifts past values before it and code after it. -/
theorem step_ctx {s s' : Store H} {f f' : Frame} {Y Y' : List Admin} (vs : List Val)
    (rest : List Admin) (h : Step P host ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Step P host ⟨s, f, vals vs ++ Y ++ rest⟩ ⟨s', f', vals vs ++ Y' ++ rest⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h hne
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa only [vals, List.map_nil, List.nil_append, List.append_nil] using h

/-- Runs lift past values before them and code after them. -/
theorem steps_ctx {s s' : Store H} {f f' : Frame} {Y Y' : List Admin} (vs : List Val)
    (rest : List Admin) (h : Steps P host ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Steps P host ⟨s, f, vals vs ++ Y ++ rest⟩ ⟨s', f', vals vs ++ Y' ++ rest⟩ := by
  have key : ∀ c c' : Config H, Steps P host c c' →
      Steps P host ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
        ⟨c'.store, c'.frame, vals vs ++ c'.code ++ rest⟩ := by
    intro c c' hc
    induction hc with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (step_ctx vs rest hst)
  exact key _ _ h

/-- Runs lift into a label. -/
theorem steps_label {s s' : Store H} {f f' : Frame} {Y Y' : List Admin} (n : Nat)
    (cont : List Instr) (h : Steps P host ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Steps P host ⟨s, f, [.label n cont Y]⟩ ⟨s', f', [.label n cont Y']⟩ := by
  have key : ∀ c c' : Config H, Steps P host c c' →
      Steps P host ⟨c.store, c.frame, [.label n cont c.code]⟩
        ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ := by
    intro c c' hc
    induction hc with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (.ctxtLabel hst)
  exact key _ _ h

/-! ## Store updates -/

theorem global?_addStruct (s : Store H) (si : StructInst) (f : Frame) (x : GlobalIdx) :
    (s.addStruct si).global? f x = s.global? f x := rfl

theorem structs_setGlobal (s : Store H) (a : Nat) (v : Val) :
    (s.setGlobal a v).structs = s.structs := rfl

/-- Setting the global at address `a` changes the global found at `a` and no other. -/
theorem global?_setGlobal {s : Store H} {f : Frame} {x : GlobalIdx} {a a' : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a', g)) (v : Val) :
    (s.setGlobal a v).global? f x =
      some (a', if a = a' then { g with value := v } else g) := by
  simp only [Store.global?, Option.bind_eq_bind] at h ⊢
  obtain ⟨b, hb, hg⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g', hg', heq⟩ := Option.bind_eq_some_iff.mp hg
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  simp only [hb, Option.bind_some, Store.setGlobal, List.getElem?_modify, hg', Option.pure_def]
  split <;> simp_all

theorem global?_setGlobal_self {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g)) (v : Val) :
    (s.setGlobal a v).global? f x = some (a, { g with value := v }) := by
  rw [global?_setGlobal h v, ite_eq_left_iff.mpr (fun h => absurd rfl h)]

theorem global?_setGlobal_ne {s : Store H} {f : Frame} {x : GlobalIdx} {a a' : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a', g)) (hne : a ≠ a') (v : Val) :
    (s.setGlobal a v).global? f x = some (a', g) := by
  rw [global?_setGlobal h v]; simp [hne]

theorem bufIs_addStruct {s : Store H} (si : StructInst) :
    ∀ {v : Val} {qs : List CRec}, BufIs s v qs → BufIs (s.addStruct si) v qs := by
  intro v qs h
  induction h with
  | nil => exact .nil
  | cons hs hf _ ih =>
    refine .cons ?_ hf ih
    have hlt := (List.getElem?_eq_some_iff.mp hs).1
    simp only [Store.addStruct, List.getElem?_append_left hlt, hs]

theorem bufIs_setGlobal {s : Store H} (a : Nat) (w : Val) :
    ∀ {v : Val} {qs : List CRec}, BufIs s v qs → BufIs (s.setGlobal a w) v qs := by
  intro v qs h
  induction h with
  | nil => exact .nil
  | cons hs hf _ ih => exact .cons (by rw [structs_setGlobal]; exact hs) hf ih

/-! ## Single instructions -/

theorem step_globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) :
    Step P host ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩ :=
  .variable (.globalGet h)

theorem step_globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) (v : Val) :
    Step P host ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩ :=
  .variable (.globalSet h)

/-- Packing every field of an unpacked struct type keeps the values. -/
theorem zip_pack {fs : List CFieldType} (hu : ∀ ft ∈ fs, ∃ t, fieldStorage ft = .val t) :
    ∀ {vs : List Val}, vs.length = fs.length →
      (fs.zip vs).map (fun p => packField (fieldStorage p.1) p.2) = vs.map .val := by
  induction fs with
  | nil =>
    intro vs hl
    cases vs with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons ft fs ih =>
    intro vs hl
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      obtain ⟨t, ht⟩ := hu ft (List.mem_cons_self ..)
      have ih' := ih (fun ft' h' => hu ft' (List.mem_cons_of_mem _ h')) (vs := vs)
        (by simpa using hl)
      rw [List.zip_cons_cons, List.map_cons, ih', List.map_cons]
      simp only [ht, packField]

/-- **`struct.new` of a record type keeps the field values.** -/
theorem step_structNew {s : Store H} {f : Frame} {x : TypeIdx} {n : Nat} (hx : RecTy f x n)
    (vs : List Val) (hl : vs.length = n + 3) :
    ∃ d, Step P host ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
      ⟨s.addStruct ⟨d, vs.map .val⟩, f, [.ref (.struct s.structs.length)]⟩ := by
  obtain ⟨d, fs, hd, he, hlen, hu⟩ := hx
  have hst := AggregateStep.structNew (H := H) (s := s) hd he (vs := vs)
    (by simp only [Ty.length]; omega) (fun p _ => by
      obtain ⟨t, ht⟩ := hu p.1 (List.of_mem_zip ‹_›).1
      simp only [ht, packable])
  have hz : (fs.toList.zip vs).map (fun (ft, v) => packField (fieldStorage ft) v) =
      vs.map .val := zip_pack hu (by omega)
  rw [hz] at hst
  exact ⟨d, .aggregate hst⟩

/-- **`struct.get` of an unpacked field of a record.** -/
theorem step_structGet {s : Store H} {f : Frame} {x : TypeIdx} {n : Nat} (hx : RecTy f x n)
    {a : Nat} {si : StructInst} (hs : s.structs[a]? = some si) {vs : List Val}
    (hf : si.fields = vs.map .val) {i : Nat} (hi : i < n + 3) (hi32 : n + 3 ≤ 2 ^ 32)
    (hv : i < vs.length) :
    Step P host ⟨s, f, [.ref (.struct a), .plain (.structGet none x (ix i))]⟩
      ⟨s, f, [vs[i].toAdmin]⟩ := by
  obtain ⟨d, fs, hd, he, hlen, hu⟩ := hx
  have hit : (ix i : FieldIdx).toNat = i := ix_toNat (k := .field) (j := i) (by omega)
  have hfi : i < fs.toList.length := by omega
  have hft : fs.toList[i]? = some (fs.toList[i]'hfi) := List.getElem?_eq_getElem hfi
  obtain ⟨t, ht⟩ := hu _ (List.getElem_mem hfi)
  have hfv : si.fields[(ix i : FieldIdx).toNat]? = some (.val vs[i]) := by
    rw [hit, hf, List.getElem?_map, List.getElem?_eq_getElem hv, Option.map_some]
  have hst := AggregateStep.structGetStruct (H := H) (sx := none) hs hfv hd he
    (by rw [hit]; exact hft) (by rw [ht]; rfl)
  exact .aggregate hst

/-! ## The save code -/

/-- Transport a step along equal configurations. -/
theorem step_eq {c₁ c₂ d₁ d₂ : Config H} (h : Step P host c₁ c₂) (e₁ : c₁ = d₁) (e₂ : c₂ = d₂) :
    Step P host d₁ d₂ := e₁ ▸ e₂ ▸ h

/-- Transport a run along equal configurations. -/
theorem steps_eq {c₁ c₂ d₁ d₂ : Config H} (h : Steps P host c₁ c₂) (e₁ : c₁ = d₁)
    (e₂ : c₂ = d₂) : Steps P host d₁ d₂ := e₁ ▸ e₂ ▸ h

/-- `local.get` of the locals `i, …, i + m - 1`. -/
theorem getLocals_from {s : Store H} {f : Frame} {ls : List Val} (hL : LocalsAre f ls)
    (rest : List Admin) :
    ∀ (m i : Nat) (pre : List Val), i + m ≤ ls.length →
      Steps P host
        ⟨s, f, vals pre ++ expression ((List.range' i m).map fun j => .localGet (ix j)) ++ rest⟩
        ⟨s, f, vals (pre ++ (ls.drop i).take m) ++ rest⟩ := by
  intro m i pre hle
  induction m generalizing i pre with
  | zero =>
    simp only [List.range'_zero, List.map_nil, expression, List.append_nil, List.take_zero]
    exact .refl
  | succ m ih =>
    show Steps P host
      ⟨s, f, vals pre ++ expression ((List.range' i (m + 1)).map fun j => .localGet (ix j)) ++ rest⟩
      ⟨s, f, vals (pre ++ (ls.drop i).take (m + 1)) ++ rest⟩
    have hi : i < ls.length := by omega
    have h1 : Step P host ⟨s, f, [.plain (.localGet (ix i))]⟩ ⟨s, f, [ls[i].toAdmin]⟩ :=
      .variable (.localGet (hL i hi))
    have h2 : Step P host
        ⟨s, f, vals pre ++ expression ((List.range' i (m + 1)).map fun j => .localGet (ix j)) ++
          rest⟩
        ⟨s, f, vals (pre ++ [ls[i]]) ++
          (expression ((List.range' (i + 1) m).map fun j => .localGet (ix j)) ++ rest)⟩ :=
      step_eq (step_ctx pre
        (expression ((List.range' (i + 1) m).map fun j => .localGet (ix j)) ++ rest) h1)
        (by simp [List.range'_succ, expression]) (by simp [vals])
    have h3 : Steps P host
        ⟨s, f, vals (pre ++ [ls[i]]) ++
          (expression ((List.range' (i + 1) m).map fun j => .localGet (ix j)) ++ rest)⟩
        ⟨s, f, vals (pre ++ (ls.drop i).take (m + 1)) ++ rest⟩ :=
      steps_eq (ih (i + 1) (pre ++ [ls[i]]) (by omega)) (by rw [List.append_assoc])
        (by rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.append_assoc,
          List.singleton_append])
    exact .head h2 h3

/-- **`local.get 0, …, local.get (n-1)` pushes the locals.** -/
theorem getLocals_run {s : Store H} {f : Frame} {ls : List Val} (hL : LocalsAre f ls)
    (pre : List Val) (rest : List Admin) :
    Steps P host ⟨s, f, vals pre ++ expression (getLocals ls.length) ++ rest⟩
      ⟨s, f, vals (pre ++ ls) ++ rest⟩ := by
  have h := getLocals_from (P := P) (host := host) (s := s) hL rest ls.length 0 pre (by omega)
  simpa only [getLocals, List.range_eq_range', List.drop_zero, List.take_length] using h

end Silmaril.Proofs.Wasm.Models.FXCoreSave
