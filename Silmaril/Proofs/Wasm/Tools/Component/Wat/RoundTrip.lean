module

public import Silmaril.Proofs.Wasm.Tools.Component.Wat.Canon
public import Silmaril.Wasm.Component.BinaryP3.Thms

/-!
# Component WAT with every built-in: the round trip

Every item the printer writes for a section other than `canon` built-ins and nested
components is one of `Wat`'s, and this reader reads it as `Wat`'s reader does (`Bridge`); the
built-ins read back by `item_canon`. Hence `ofSexp (toSexp c) = some (norm c)` and
`read (print c) = some (norm c)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Wat

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Wat (Sexp kw num nm bytesS)
open Silmaril.Wasm.Component.Wat.Sexp (WF WFL)
open Silmaril.Wasm.Component.BinaryP3 (Canon Section Ast)

/-- An item this reader reads as `Wat`'s reader does. -/
def Bridge (x : Sexp) : Prop :=
  R.item x = (_root_.Silmaril.Wasm.Component.Wat.R.item x).map Section.ofV0

theorem bridge_kw (k : String) (ss : List Sexp) (h1 : k ≠ "component") (h2 : k ≠ "core") :
    Bridge (.list (.atom k :: ss)) := by
  unfold Bridge
  rw [item_other k ss h1 h2, _root_.Silmaril.Wasm.Component.Wat.item_kw k ss h1]

theorem bridge_core (k : String) (rest : List Sexp) (hk : k ≠ "func") :
    Bridge (.list (.atom "core" :: .atom k :: rest)) := by
  unfold Bridge
  rw [_root_.Silmaril.Wasm.Component.Wat.item_kw _ _ (by decide),
    _root_.Silmaril.Wasm.Component.Wat.itemKw_core]
  show R.coreItem (.atom k :: rest) = _
  unfold R.coreItem
  split
  · next h => cases h; exact absurd rfl hk
  · rfl

theorem items_cons (s : Sexp) (ss : List Sexp) :
    R.items (s :: ss) = (R.item s).bind fun x => (R.items ss).map (x :: ·) := by
  show (do
    let x ← R.item s
    let xs ← R.items ss
    pure (x :: xs)) = _
  cases R.item s <;> cases R.items ss <;> rfl

theorem items_append : ∀ (a b : List Sexp),
    R.items (a ++ b) = (R.items a).bind fun xs => (R.items b).map (xs ++ ·)
  | [], b => by
    rw [List.nil_append]
    show R.items b = Option.bind (some []) _
    cases R.items b <;> rfl
  | s :: a, b => by
    rw [List.cons_append, items_cons, items_cons, items_append a b]
    cases R.item s <;> cases R.items a <;> cases R.items b <;> rfl

/-- Lists of bridged items read as `Wat`'s reader reads them. -/
theorem items_bridge : ∀ l : List Sexp, (∀ x ∈ l, Bridge x) →
    R.items l = (_root_.Silmaril.Wasm.Component.Wat.R.items l).map (List.map Section.ofV0)
  | [], _ => rfl
  | x :: l, h => by
    rw [items_cons, _root_.Silmaril.Wasm.Component.Wat.items_cons, h x (by simp),
      items_bridge l (fun y hy => h y (by simp [hy]))]
    cases _root_.Silmaril.Wasm.Component.Wat.R.item x <;>
      cases _root_.Silmaril.Wasm.Component.Wat.R.items l <;> rfl

theorem items_map {α : Type} (f : α → Sexp) (g : α → Section) (h : ∀ x, R.item (f x) = some (g x)) :
    ∀ xs : List α, R.items (xs.map f) = some (xs.map g)
  | [] => rfl
  | x :: xs => by rw [List.map_cons, items_cons, h x, items_map f g h xs]; rfl

/-! ## Every item of the other sections is bridged -/

section Bridged
open _root_.Silmaril.Wasm.Component.Wat.P (coreInstance inst alias_ start import_ export_ value)

/-- `Wat`'s printer. -/
abbrev P0.section_ := _root_.Silmaril.Wasm.Component.Wat.P.section_

theorem bridge_coreInstance (x : Binary.CoreInstanceExpr) : Bridge (coreInstance x) := by
  cases x <;> exact bridge_core "instance" _ (by decide)

theorem bridge_inst (x : Binary.InstanceExpr) : Bridge (inst x) := by
  cases x <;> exact bridge_kw "instance" _ (by decide) (by decide)

theorem bridge_alias (a : Binary.Alias) : Bridge (alias_ a) := by
  obtain ⟨ss, h⟩ := _root_.Silmaril.Wasm.Component.Wat.alias_list a
  rw [h]; exact bridge_kw "alias" ss (by decide) (by decide)

theorem bridge_map {α : Type} {f : α → Sexp} (h : ∀ y, Bridge (f y)) (xs : List α) :
    ∀ x ∈ xs.map f, Bridge x := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact h y

theorem bridge_single {y : Sexp} (h : Bridge y) : ∀ x ∈ [y], Bridge x := by
  intro x hx
  rw [List.mem_singleton.mp hx]
  exact h

/-- The sections `Wat`'s printer writes for every section but `canon` and `component`. -/
theorem bridge_section (s : Binary.Section)
    (hs : ∀ xs, s ≠ .canons xs) (hc : ∀ c, s ≠ .component c) :
    ∀ x ∈ P0.section_ s, Bridge x := by
  cases s with
  | canons xs => exact absurd rfl (hs xs)
  | component c => exact absurd rfl (hc c)
  | custom n d => exact bridge_single (bridge_kw "@custom" _ (by decide) (by decide))
  | coreModule b => exact bridge_single (bridge_core "module" _ (by decide))
  | coreInstances xs => exact bridge_map bridge_coreInstance xs
  | coreTypes xs => exact bridge_map (fun _ => bridge_core "type" _ (by decide)) xs
  | instances xs => exact bridge_map bridge_inst xs
  | aliases xs => exact bridge_map bridge_alias xs
  | types xs => exact bridge_map (fun _ => bridge_kw "type" _ (by decide) (by decide)) xs
  | start s => exact bridge_single (bridge_kw "start" _ (by decide) (by decide))
  | imports xs => exact bridge_map (fun _ => bridge_kw "import" _ (by decide) (by decide)) xs
  | exports xs => exact bridge_map (fun _ => bridge_kw "export" _ (by decide) (by decide)) xs
  | values xs => exact bridge_map (fun _ => bridge_kw "value" _ (by decide) (by decide)) xs

end Bridged

/-- A bridged section reads back as `Wat`'s normal form, embedded. -/
theorem section_rt_v0 (s : Binary.Section)
    (hs : ∀ xs, s ≠ .canons xs) (hc : ∀ c, s ≠ .component c) :
    R.items (_root_.Silmaril.Wasm.Component.Wat.P.section_ s) =
      some ((_root_.Silmaril.Wasm.Component.Wat.normSection s).map Section.ofV0) := by
  rw [items_bridge _ (bridge_section s hs hc), _root_.Silmaril.Wasm.Component.Wat.section_rt]
  rfl

theorem item_component (ss : List Sexp) :
    R.item (.list (kw "component" :: ss)) =
      (R.items ss).map fun xs => .component (.mk (R.group xs)) := by
  rw [R.item.eq_def]
  rfl

mutual
theorem section_rt : ∀ s : Section, R.items (P.section_ s) = some (normSection s)
  | .component (.mk ss) => by
    show R.items [_] = _
    rw [items_cons, item_component]
    show (((R.items (P.sections ss)).map _).bind _) = _
    rw [sections_rt ss]; rfl
  | .canons xs => items_map _ _ item_canon xs
  | .custom n d => section_rt_v0 (.custom n d) (by simp) (by simp)
  | .coreModule b => section_rt_v0 (.coreModule b) (by simp) (by simp)
  | .coreInstances xs => section_rt_v0 (.coreInstances xs) (by simp) (by simp)
  | .coreTypes xs => section_rt_v0 (.coreTypes xs) (by simp) (by simp)
  | .instances xs => section_rt_v0 (.instances xs) (by simp) (by simp)
  | .aliases xs => section_rt_v0 (.aliases xs) (by simp) (by simp)
  | .types xs => section_rt_v0 (.types xs) (by simp) (by simp)
  | .start s => section_rt_v0 (.start s) (by simp) (by simp)
  | .imports xs => section_rt_v0 (.imports xs) (by simp) (by simp)
  | .exports xs => section_rt_v0 (.exports xs) (by simp) (by simp)
  | .values xs => section_rt_v0 (.values xs) (by simp) (by simp)

theorem sections_rt : ∀ ss : List Section, R.items (P.sections ss) = some (normSections ss)
  | [] => rfl
  | s :: ss => by
    show R.items (P.section_ s ++ P.sections ss) = _
    rw [items_append, section_rt s, sections_rt ss]; rfl
end

/-- The reader inverts the printer up to the normal form, at the level of S-expressions. -/
theorem ofSexp_toSexp (c : Ast) : ofSexp (toSexp c) = some (norm c) := by
  obtain ⟨ss⟩ := c
  show (R.items (P.sections ss)).map _ = _
  rw [sections_rt]; rfl

/-! ## Well-formedness -/

mutual
theorem wfl_section : ∀ s : Section, WFL (P.section_ s)
  | .component (.mk ss) => by
    have := wfl_sections ss
    simp [P.section_, P.ast, kw, this, Wat.wf_atom, Wat.wf_list, Wat.wfl_cons]
    decide
  | .canons xs => by simp [P.section_, Wat.wfl_map, wf_canon]
  | .custom n d => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.custom n d)
  | .coreModule b => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.coreModule b)
  | .coreInstances xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.coreInstances xs)
  | .coreTypes xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.coreTypes xs)
  | .instances xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.instances xs)
  | .aliases xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.aliases xs)
  | .types xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.types xs)
  | .start s => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.start s)
  | .imports xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.imports xs)
  | .exports xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.exports xs)
  | .values xs => _root_.Silmaril.Wasm.Component.Wat.wfl_section (.values xs)

theorem wfl_sections : ∀ ss : List Section, WFL (P.sections ss)
  | [] => Wat.wfl_nil
  | s :: ss => (Wat.wfl_append _ _).2 ⟨wfl_section s, wfl_sections ss⟩
end

theorem wf_toSexp (c : Ast) : WF (toSexp c) := by
  obtain ⟨ss⟩ := c
  have := wfl_sections ss
  simp [toSexp, P.ast, kw, this, Wat.wf_atom, Wat.wf_list, Wat.wfl_cons]
  decide

/-! ## Text and bytes -/

/-- **Round trip.** Reading the printed text of a component gives its normal form. -/
theorem read_print (c : Ast) : read (print c) = some (norm c) := by
  unfold read print
  rw [Wat.Sexp.read_printAll [toSexp c] ((Wat.wfl_cons _ _).2 ⟨wf_toSexp c, Wat.wfl_nil⟩)]
  exact ofSexp_toSexp c

/-- The tool's reader reads the printer's text with the verified reader. -/
theorem readX_print (c : Ast) : readX (print c) = some (norm c) := by
  simp [readX, read_print]

/-- **`wasm-tools parse` of `wasm-tools print`**: printing a component binary and parsing the
text gives the encoding of the normal form of its decoding. -/
theorem parseText_printBytes {b : ByteArray} {t : String} (h : printBytes b = .ok t) :
    ∃ c, BinaryP3.parse b = .ok c ∧ t = print c ∧
      parseText t = match BinaryP3.encode (norm c) with
        | some b' => .ok b'
        | none => .error "a number or size exceeds 2^32" := by
  unfold printBytes at h
  split at h
  · next c hc =>
    cases h
    refine ⟨c, hc, rfl, ?_⟩
    simp only [parseText, readX_print]
    rfl
  · cases h

/-- On a component in normal form, print then parse returns bytes that decode to the same
component (`BinaryP3.parse_encode`). -/
theorem parse_print_decode {c : Ast} {b' : ByteArray} (hn : norm c = c)
    (h : parseText (print c) = .ok b') : BinaryP3.parse b' = .ok c := by
  simp only [parseText, readX_print, hn] at h
  split at h
  · next b'' he => cases h; exact BinaryP3.parse_encode he
  · cases h

end Silmaril.Wasm.Tools.Component.Wat
