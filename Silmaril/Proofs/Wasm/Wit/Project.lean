module

public import Silmaril.Wasm.Wit.Project.Defs
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# The projection of a component to its world: proofs

* `project_worldPackage`: the projection of the package of a world `w` is the
  package's type, and `worldOf` reads `w` (in normal form) back from it;
* `project_stripCode`: code does not change the projection, so the projection
  is many-to-one (`project_not_injective`);
* `project_norm`: the projection does not see the WAT normal form (section
  grouping, name spelling), so it is well defined on component WAT text.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat

/-! ## The normal form is idempotent on declarations -/

theorem normName_normName (n : ExternName) : normName (normName n) = normName n := by
  obtain ⟨s, f⟩ := n
  cases f with
  | attrs as => cases as <;> rfl
  | _ => rfl

mutual
theorem normDefType_idem : ∀ t : DefType, normDefType (normDefType t) = normDefType t
  | .val _ => rfl
  | .func _ => rfl
  | .component ds => by
    show DefType.component (normComponentDecls (normComponentDecls ds)) = _
    rw [normComponentDecls_idem ds]; rfl
  | .instance ds => by
    show DefType.instance (normInstanceDecls (normInstanceDecls ds)) = _
    rw [normInstanceDecls_idem ds]; rfl
  | .resource _ _ => rfl

theorem normInstanceDecl_idem : ∀ d : InstanceDecl,
    normInstanceDecl (normInstanceDecl d) = normInstanceDecl d
  | .coreType _ => rfl
  | .type t => by
    show InstanceDecl.type (normDefType (normDefType t)) = _
    rw [normDefType_idem t]; rfl
  | .alias _ => rfl
  | .export n d => by
    show InstanceDecl.export (normName (normName n)) d = _
    rw [normName_normName]; rfl

theorem normComponentDecl_idem : ∀ d : ComponentDecl,
    normComponentDecl (normComponentDecl d) = normComponentDecl d
  | .import n d => by
    show ComponentDecl.import (normName (normName n)) d = _
    rw [normName_normName]; rfl
  | .inst d => by
    show ComponentDecl.inst (normInstanceDecl (normInstanceDecl d)) = _
    rw [normInstanceDecl_idem d]; rfl

theorem normInstanceDecls_idem : ∀ ds : List InstanceDecl,
    normInstanceDecls (normInstanceDecls ds) = normInstanceDecls ds
  | [] => rfl
  | d :: ds => by
    show normInstanceDecl (normInstanceDecl d) :: normInstanceDecls (normInstanceDecls ds) = _
    rw [normInstanceDecl_idem d, normInstanceDecls_idem ds]; rfl

theorem normComponentDecls_idem : ∀ ds : List ComponentDecl,
    normComponentDecls (normComponentDecls ds) = normComponentDecls ds
  | [] => rfl
  | d :: ds => by
    show normComponentDecl (normComponentDecl d) :: normComponentDecls (normComponentDecls ds) = _
    rw [normComponentDecl_idem d, normComponentDecls_idem ds]; rfl
end

theorem isResource_normDefType (t : DefType) : isResource (normDefType t) = isResource t := by
  cases t <;> rfl

/-! ## Replay -/

theorem replay_append (s : PState) (a b : List Section) :
    replay s (a ++ b) = (replay s a).bind fun s' => replay s' b := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (step s x).bind (fun s' => replay s' (a ++ b)) = ((step s x).bind _).bind _
    cases step s x with
    | none => rfl
    | some s' => exact ih s'

/-- Two lists of items that replay alike, item by item. -/
inductive SameSteps : List Section → List Section → Prop
  | nil : SameSteps [] []
  | cons {x y : Section} {l m : List Section} : (∀ s, step s x = step s y) → SameSteps l m →
      SameSteps (x :: l) (y :: m)

theorem SameSteps.append {a b c d : List Section} (h1 : SameSteps a b) (h2 : SameSteps c d) :
    SameSteps (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem SameSteps.replay_eq {l m : List Section} (h : SameSteps l m) (s : PState) :
    replay s l = replay s m := by
  induction h generalizing s with
  | nil => rfl
  | cons hx _ ih =>
    show (step s _).bind _ = (step s _).bind _
    rw [hx s]
    cases step s _ with
    | none => rfl
    | some s' => exact ih s'

theorem SameSteps.refl : ∀ l : List Section, SameSteps l l
  | [] => .nil
  | _ :: l => .cons (fun _ => rfl) (SameSteps.refl l)

theorem SameSteps.map {α : Type} (f g : α → Section) (h : ∀ x s, step s (f x) = step s (g x)) :
    ∀ xs : List α, SameSteps (xs.map f) (xs.map g)
  | [] => .nil
  | x :: xs => .cons (h x) (SameSteps.map f g h xs)

/-! ## The normal form -/

theorem split_merge {s t u : Section} (h : R.merge s t = some u) :
    splitSection u = splitSection s ++ splitSection t := by
  cases s <;> cases t <;> simp [R.merge] at h <;> subst h <;> simp [splitSection]

theorem flatMap_split_group : ∀ l : List Section,
    (R.group l).flatMap splitSection = l.flatMap splitSection
  | [] => rfl
  | s :: ss => by
    have ih := flatMap_split_group ss
    show (match R.group ss with
      | [] => [s]
      | t :: ts => match R.merge s t with
        | some u => u :: ts
        | none => s :: t :: ts).flatMap splitSection = splitSection s ++ ss.flatMap splitSection
    rw [← ih]
    cases R.group ss with
    | nil => simp
    | cons t ts =>
      simp only
      cases hm : R.merge s t with
      | none => rfl
      | some u => simp [split_merge hm]

theorem step_normName_import (s : PState) (i : Silmaril.Wasm.Component.Binary.Import) :
    step s (.imports [⟨normName i.name, i.desc⟩]) = step s (.imports [i]) := by
  simp only [step, normName_normName]

theorem step_normName_export (s : PState) (e : Silmaril.Wasm.Component.Binary.Export) :
    step s (.exports [⟨normName e.name, e.item, e.desc⟩]) = step s (.exports [e]) := by
  simp only [step, exportDesc, normName_normName]

theorem step_normDefType (s : PState) (t : DefType) :
    step s (.types [normDefType t]) = step s (.types [t]) := by
  simp only [step, isResource_normDefType, normDefType_idem]

/-- The normal form of a section replays like its split. -/
theorem sameSteps_normSection (x : Section) :
    SameSteps (normSection x) (splitSection x) := by
  cases x with
  | component c => exact .cons (fun _ => rfl) .nil
  | instances xs =>
    exact SameSteps.map (fun x => .instances [normInstance x]) (fun x => .instances [x])
      (fun _ _ => rfl) xs
  | types xs => exact SameSteps.map _ _ (fun t s => step_normDefType s t) xs
  | imports xs => exact SameSteps.map _ _ (fun i s => step_normName_import s i) xs
  | exports xs => exact SameSteps.map _ _ (fun e s => step_normName_export s e) xs
  | _ => exact SameSteps.refl _

theorem sameSteps_normSections : ∀ ss : List Section,
    SameSteps (normSections ss) (ss.flatMap splitSection)
  | [] => .nil
  | x :: ss => (sameSteps_normSection x).append (sameSteps_normSections ss)

theorem flatMap_single {α : Type} (f : α → Section) :
    ∀ xs : List α, xs.flatMap (fun a => [f a]) = xs.map f
  | [] => rfl
  | x :: xs => by simp [flatMap_single f xs]

theorem flatMap_split_normSection (x : Section) :
    (normSection x).flatMap splitSection = normSection x := by
  cases x <;> simp [normSection, splitSection, List.flatMap_map, flatMap_single]

theorem flatMap_split_normSections : ∀ ss : List Section,
    (normSections ss).flatMap splitSection = normSections ss
  | [] => rfl
  | x :: ss => by
    show (normSection x ++ normSections ss).flatMap splitSection = _
    rw [List.flatMap_append, flatMap_split_normSection, flatMap_split_normSections ss]; rfl

/-- **The projection does not see the WAT normal form**: it is well defined on
component text (`Wat.read`). -/
theorem project_norm (c : Ast) : project (norm c) = project c := by
  obtain ⟨ss⟩ := c
  show (replay {} ((R.group (normSections ss)).flatMap splitSection)).map _ =
    (replay {} (ss.flatMap splitSection)).map _
  rw [flatMap_split_group, flatMap_split_normSections,
    (sameSteps_normSections ss).replay_eq]

/-- The projection of the text of a component. -/
theorem project_read_print (c : Ast) : (read (print c)).bind project = project c := by
  rw [read_print]
  exact project_norm c

/-! ## Code does not change the projection -/

theorem step_code {x : Section} (h : isCode x = true) :
    ∀ y ∈ splitSection x, ∀ s, step s y = some s := by
  cases x <;> simp [isCode] at h <;> simp [splitSection, step]

theorem replay_code (s : PState) (x : Section) (h : isCode x = true) :
    replay s (splitSection x) = some s := by
  have := step_code h
  generalize splitSection x = l at this
  induction l with
  | nil => rfl
  | cons y l ih =>
    show (step s y).bind _ = _
    rw [this y (by simp) s]
    exact ih (fun z hz => this z (by simp [hz]))

theorem replay_strip (s : PState) : ∀ ss : List Section,
    replay s ((ss.filter fun x => !isCode x).flatMap splitSection) =
      replay s (ss.flatMap splitSection)
  | [] => rfl
  | x :: ss => by
    rw [List.flatMap_cons, replay_append]
    by_cases h : isCode x = true
    · rw [List.filter_cons_of_neg (by simp [h]), replay_code s x h]
      exact replay_strip s ss
    · rw [List.filter_cons_of_pos (by simpa using h), List.flatMap_cons, replay_append]
      cases replay s (splitSection x) with
      | none => rfl
      | some s' => exact replay_strip s' ss

/-- **Code does not change the projection.** -/
theorem project_stripCode (c : Ast) : project (stripCode c) = project c := by
  obtain ⟨ss⟩ := c
  simp only [project, stripCode, Ast.sections]
  rw [replay_strip]

/-- The projection is many-to-one: a component and its code-free shell differ but
have the same (defined) world. -/
theorem project_not_injective :
    ∃ c d : Ast, c ≠ d ∧ project c = project d ∧ (project c).isSome := by
  refine ⟨.mk [.start ⟨0, [], 0⟩, .imports [⟨↑"f", .func 0⟩]], .mk [.imports [⟨↑"f", .func 0⟩]],
    ?_, rfl, rfl⟩
  intro h
  have := congrArg (fun a : Ast => a.sections.length) h
  simp [Ast.sections] at this

/-! ## Worlds as packages -/

/-- The projection of the package of a world. -/
theorem project_worldPackage (id name : String) (w : WorldType) :
    project (worldPackage id name w) = some
      [.inst (.type (.component [.inst (.type (.component (normComponentDecls w))),
        .inst (.export ↑id (.component 0))])),
       .inst (.export ↑name (.type (.eq 0)))] := rfl

/-- **The package of a world projects back to that world** (in normal form). -/
theorem worldOf_project_worldPackage (id name : String) (w : WorldType) :
    (project (worldPackage id name w)).bind worldOf = some (normComponentDecls w) := by
  rw [project_worldPackage]; rfl

/-- On worlds in normal form, the package projects back to exactly the world. -/
theorem worldOf_project_worldPackage_of_norm (id name : String) {w : WorldType}
    (h : normComponentDecls w = w) :
    (project (worldPackage id name w)).bind worldOf = some w := by
  rw [worldOf_project_worldPackage, h]

/-- Two worlds have the same package exactly when their normal forms agree. -/
theorem project_worldPackage_inj (id name : String) (w w' : WorldType) :
    project (worldPackage id name w) = project (worldPackage id name w') ↔
      normComponentDecls w = normComponentDecls w' := by
  constructor
  · intro h
    have := congrArg (fun o => o.bind worldOf) h
    simp only [worldOf_project_worldPackage] at this
    exact Option.some.inj this
  · intro h
    rw [project_worldPackage, project_worldPackage, h]

/-! ## Packages of several items -/

/-- The declarations the items of a package project to, from the `k`-th on. -/
def itemDecls : Nat → List (String × DefType) → WorldType
  | _, [] => []
  | k, (n, d) :: rest =>
    .inst (.type (normDefType d)) :: .inst (.export ↑n (.type (.eq (2 * k)))) ::
      itemDecls (k + 1) rest

theorem replay_itemSecs : ∀ (k : Nat) (items : List (String × DefType)) (s : PState),
    (∀ p ∈ items, isResource p.2 = false) →
    replay s ((itemSecs k items).flatMap splitSection) =
      some { s with decls := s.decls ++ itemDecls k items }
  | _, [], s, _ => by simp [itemSecs, itemDecls, replay]
  | k, (n, d) :: rest, s, h => by
    have hd : isResource d = false := h (n, d) (by simp)
    have ih := replay_itemSecs (k + 1) rest
      { s with decls := s.decls ++
        [.inst (.type (normDefType d)), .inst (.export ↑n (.type (.eq (2 * k))))] }
      (fun p hp => h p (by simp [hp]))
    simp only [itemSecs, List.flatMap_cons, splitSection, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
    simp only [replay, step, hd, Bool.false_eq_true, ite_false, exportDesc,
      PState.emit, Option.bind_some]
    simpa [itemDecls, List.append_assoc, normName, isValueEq] using ih

theorem packageItems_itemDecls : ∀ (k : Nat) (items : List (String × DefType)),
    packageItems k (itemDecls k items) = some (items.map fun p => (p.1, normDefType p.2))
  | _, [] => rfl
  | k, (n, d) :: rest => by
    simp [itemDecls, packageItems, packageItems_itemDecls (k + 1) rest]

theorem replay_customs (s : PState) : ∀ cs : List Section, (∀ c ∈ cs, isCode c = true) →
    replay s (cs.flatMap splitSection) = some s
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatMap_cons, replay_append, replay_code s c (h c (by simp))]
    exact replay_customs s cs (fun c' hc => h c' (by simp [hc]))

/-- **A package projects back to its items** (in normal form): the binary package
of named items without top-level resource definitions, followed by any custom
sections (`package-docs`, `producers`, …), projects to declarations from which
`packageItems` reads the items back. -/
theorem packageItems_project_itemsPackage (items : List (String × DefType)) (cs : List Section)
    (hr : ∀ p ∈ items, isResource p.2 = false) (hc : ∀ c ∈ cs, isCode c = true) :
    (project (itemsPackage items cs)).bind (packageItems 0) =
      some (items.map fun p => (p.1, normDefType p.2)) := by
  simp only [project, itemsPackage, Ast.sections, List.flatMap_append, replay_append,
    replay_itemSecs 0 items {} hr, Option.bind_some, replay_customs _ cs hc, Option.map_some,
    List.nil_append]
  exact packageItems_itemDecls 0 items

end Silmaril.Wasm.Wit.Project
