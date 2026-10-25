module

public import Silmaril.Wasm.Binaryen.TableFrozen
public import Silmaril.Wasm.Binaryen.Pass.Directize
public import Silmaril.Wasm.Binaryen.Profile

@[expose] public section

/-! # Directize: the tables are frozen at the start of the simulation

After the element segments, no code that can run writes a table of the instance
(`TableFrozen.Frozen`): the functions of the store from earlier instantiations name only
older tables (`storeK_of`, from `StoreOk`), the module's own functions contain no
table-writing instruction (`Directize.frozen`, `lowerList_K`), and the rest of the
instantiation code (data segments, start call) writes no table (`admsK_data`).
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeFrozen

open Execution.Core Validation TableFrozen Directize

variable {H : Type}

mutual
theorem instrK_of_forall {W : Nat → Prop} (hW : ∀ x, W x) (i : Instr) : InstrK W i := by
  cases i
  all_goals first
    | exact hW _
    | trivial
    | exact instrsK_of_forall hW _
    | exact ⟨instrsK_of_forall hW _, instrsK_of_forall hW _⟩
termination_by sizeOf i
decreasing_by all_goals simp_wf <;> omega
theorem instrsK_of_forall {W : Nat → Prop} (hW : ∀ x, W x) (is : List Instr) : InstrsK W is := by
  cases is with
  | nil => trivial
  | cons i is => exact ⟨instrK_of_forall hW i, instrsK_of_forall hW is⟩
termination_by sizeOf is
decreasing_by all_goals simp_wf <;> omega
end

/-- An instruction that writes no table keeps every table. -/
theorem instrK_of_mutates {W : Nat → Prop} {i : Instr} (h : mutates i = false) : InstrK W i := by
  cases i <;> trivial

theorem instrsK_append' {W : Nat → Prop} {l₁ l₂ : List Instr} (h₁ : InstrsK W l₁)
    (h₂ : InstrsK W l₂) : InstrsK W (l₁ ++ l₂) := (InstrsK_append W l₁ l₂).mpr ⟨h₁, h₂⟩

theorem mutatesList_cons {e : BExpr} {es : List BExpr} (h : mutatesList (e :: es) = false) :
    mutatesExpr e = false ∧ mutatesList es = false := by
  simpa [mutatesList] using h

theorem lowerList_K' {W : Nat → Prop} :
    ∀ l : List BExpr, (∀ e ∈ l, mutatesExpr e = false → InstrsK W e.lower) →
      mutatesList l = false → InstrsK W (BExpr.lowerList l)
  | [], _, _ => trivial
  | e :: l, h, hm => by
    obtain ⟨h₁, h₂⟩ := mutatesList_cons hm
    simp only [BExpr.lowerList_cons]
    exact instrsK_append' (h e (by simp) h₁) (lowerList_K' l (fun e' he' => h e' (by simp [he'])) h₂)

/-- **A body without table-writing instructions keeps every table.** -/
theorem lower_K {W : Nat → Prop} : ∀ e : BExpr, mutatesExpr e = false → InstrsK W e.lower
  | .op i args, h => by
    simp only [mutatesExpr, Bool.or_eq_false_iff] at h
    simp only [BExpr.lower_op]
    exact instrsK_append' (lowerList_K' args (fun e _ => lower_K e) h.2)
      ((InstrsK_cons W i []).mpr ⟨instrK_of_mutates h.1, trivial⟩)
  | .block bt b, h => by
    simp only [mutatesExpr] at h
    simp only [BExpr.lower]
    exact ⟨lowerList_K' b (fun e _ => lower_K e) h, trivial⟩
  | .loop bt b, h => by
    simp only [mutatesExpr] at h
    simp only [BExpr.lower]
    exact ⟨lowerList_K' b (fun e _ => lower_K e) h, trivial⟩
  | .if_ bt c t e, h => by
    simp only [mutatesExpr, Bool.or_eq_false_iff] at h
    simp only [BExpr.lower]
    exact instrsK_append' (lowerList_K' c (fun x _ => lower_K x) h.1.1)
      ⟨⟨lowerList_K' t (fun x _ => lower_K x) h.1.2, lowerList_K' e (fun x _ => lower_K x) h.2⟩,
        trivial⟩
  | .tryTable bt cs b, h => by
    simp only [mutatesExpr] at h
    simp only [BExpr.lower]
    exact ⟨lowerList_K' b (fun e _ => lower_K e) h, trivial⟩
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

theorem lowerList_K {W : Nat → Prop} {l : List BExpr} (h : mutatesList l = false) :
    InstrsK W (BExpr.lowerList l) :=
  lowerList_K' l (fun e _ => lower_K e) h

/-! ## Functions of older instances -/

theorem externAddrOk_table {s : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.table a) xt) : ∃ ti, s.tables[a]? = some ti := by
  generalize hx : ExternAddr.table a = xa at h
  induction h with
  | table h => cases hx; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem moduleInstOk_tables {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x ta : Nat} (hx : mi.tables[x]? = some ta) : ta < s.tables.length := by
  cases h with
  | mk _ _ _ _ _ htables =>
    have hlt := (List.getElem?_eq_some_iff.mp hx).1
    have := (List.forall₂_iff_get.mp htables).2 x hlt (by rw [← htables.length_eq]; exact hlt)
    simp only [List.get_eq_getElem] at this
    rw [(List.getElem?_eq_some_iff.mp hx).2] at this
    obtain ⟨ti, hti⟩ := externAddrOk_table this
    exact (List.getElem?_eq_some_iff.mp hti).1

/-- **No function of the store writes a fresh table.** -/
theorem storeK_of {s s' : Store H} (hs : StoreOk s) {ta : Nat} (hta : s.tables.length ≤ ta)
    {new : List (FuncInst H)}
    (hnew : ∀ fi ∈ new, ∀ code : Func, fi.code = .wasm code → ∀ W, InstrsK W code.body)
    (hf : s'.funcs = s.funcs ++ new) : StoreK ta s' := by
  intro fi hfi code hcode
  rw [hf, List.mem_append] at hfi
  rcases hfi with hfi | hfi
  · cases hs.funcs fi hfi with
    | wasm _ hm hc _ _ =>
      refine instrsK_of_forall (fun x hx => ?_) _
      have := moduleInstOk_tables hm hx
      omega
    | host _ _ hc => rw [hcode] at hc; cases hc
  · exact hnew fi hfi code hcode _

/-! ## The rest of the instantiation code -/

theorem admsK_expression {ta : Nat} {mi : ModuleInst} :
    ∀ l : List Instr, InstrsK (W ta mi) l → AdmsK ta mi (expression l)
  | [], _ => by simp [expression]
  | i :: l, h => by
    simp only [expression, List.map_cons, AdmsK_cons]
    exact ⟨h.1, admsK_expression l h.2⟩

theorem runData_K {W : Nat → Prop} {x : Nat} {d : Data} (hd : profileData d = true) :
    InstrsK W (runData x d) := by
  unfold runData
  split
  · trivial
  · rename_i y off hm
    unfold profileData at hd
    rw [hm] at hd
    simp only [Bool.and_eq_true] at hd
    obtain ⟨c, rfl⟩ := profileOffset_sound hd.2
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- **The data segments and the start call write no table.** -/
theorem admsK_data {ta : Nat} {mi : ModuleInst} {L : List (Nat × Data)}
    (hL : ∀ p ∈ L, profileData p.2 = true) (st : List Admin)
    (hst : ∀ a ∈ st, ∃ x, a = .plain (.call x)) :
    AdmsK ta mi (expression (L.flatMap fun (i, d) => runData i d) ++ st) := by
  rw [AdmsK_append]
  refine ⟨admsK_expression _ ?_, ?_⟩
  · induction L with
    | nil => trivial
    | cons p L ih =>
      rw [List.flatMap_cons]
      exact instrsK_append' (runData_K (hL p (by simp)))
        (ih fun q hq => hL q (by simp [hq]))
  · induction st with
    | nil => trivial
    | cons a st ih =>
      obtain ⟨x, rfl⟩ := hst a (by simp)
      exact (AdmsK_cons ta mi _ _).mpr ⟨trivial, ih fun b hb => hst b (by simp [hb])⟩

end DirectizeFrozen

end Silmaril.Wasm.Binaryen
