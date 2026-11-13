module

public import Silmaril.Compiler.Clang.TotalJson.Defs
public import Silmaril.Formats.Json.Decode.Thms
public section
namespace Silmaril.Compiler.Clang.TotalJson

attribute [local simp] Silmaril.Formats.Json.Tree.array.sizeOf_spec
  Silmaril.Formats.Json.Tree.object.sizeOf_spec List.cons.sizeOf_spec Prod.mk.sizeOf_spec

@[simp] private theorem pure_ok {A : Type} (a : A) :
    (pure a : Except Error A) = .ok a := rfl
@[simp] private theorem bind_ok {A B : Type} (a : A) (f : A → Except Error B) :
    ((.ok a : Except Error A) >>= f) = f a := rfl
@[simp] private theorem bind_error {A B : Type} (error : Error) (f : A → Except Error B) :
    ((.error error : Except Error A) >>= f) = .error error := rfl
@[simp] private theorem map_ok {A B : Type} (a : A) (f : A → B) :
    f <$> (.ok a : Except Error A) = .ok (f a) := rfl
@[simp] private theorem map_error {A B : Type} (error : Error) (f : A → B) :
    f <$> (.error error : Except Error A) = .error error := rfl
@[simp] private theorem throw_error {A : Type} (error : Error) :
    (throw error : Except Error A) = .error error := rfl

private theorem nonObject_ne_ok (tree : Tree) (node : Node) :
    nonObject tree ≠ .ok node := by
  simp [nonObject]

mutual
  theorem decodeTreeCore_sound (tree : Tree) (node : Node)
      (success : decodeTreeCore tree = .ok node) : DecodesTree tree node := by
    cases tree with
    | scalar value => exact False.elim (nonObject_ne_ok _ _ success)
    | array values => exact False.elim (nonObject_ne_ok _ _ success)
    | object members =>
      cases hc : classify members with
      | error error => simp [decodeTreeCore, hc] at success
      | ok head =>
        cases head with
        | absent =>
          simp [decodeTreeCore, hc] at success
          subst node
          exact .absent hc
        | comment json =>
          simp [decodeTreeCore, hc] at success
          subst node
          exact .comment hc
        | association kind selected =>
          cases hi : decodeChildren "generic association" "inner" members with
          | error error => simp [decodeTreeCore, hc, hi] at success
          | ok inner =>
            cases hs : selected with
            | error error => simp [decodeTreeCore, hc, hi, hs] at success
            | ok chosen =>
              simp [decodeTreeCore, hc, hi, hs] at success
              subst node
              exact .association hc (decodeChildren_sound _ _ _ _ hi) hs
        | node header =>
          cases hi : decodeChildren s!"{header.kind} {header.id}" "inner" members with
          | error error => simp [decodeTreeCore, hc, hi] at success
          | ok inner =>
            cases hf : decodeChildren s!"{header.kind} {header.id}" "array_filler" members with
            | error error => simp [decodeTreeCore, hc, hi, hf] at success
            | ok filler =>
              simp [decodeTreeCore, hc, hi, hf] at success
              subst node
              exact .node hc (decodeChildren_sound _ _ _ _ hi)
                (decodeChildren_sound _ _ _ _ hf)
  termination_by sizeOf tree

  theorem decodeNodes_sound (trees : List Tree) (nodes : Nodes)
      (success : decodeNodes trees = .ok nodes) : DecodesNodes trees nodes := by
    cases trees with
    | nil =>
      simp [decodeNodes] at success
      subst nodes
      exact .nil
    | cons tree trees =>
      cases ht : decodeTreeCore tree with
      | error error => simp [decodeNodes, ht] at success
      | ok node =>
        cases hs : decodeNodes trees with
        | error error => simp [decodeNodes, ht, hs] at success
        | ok rest =>
          simp [decodeNodes, ht, hs] at success
          subst nodes
          exact .cons (decodeTreeCore_sound _ _ ht) (decodeNodes_sound _ _ hs)
  termination_by sizeOf trees

  theorem decodeChildren_sound (context key : String) (members : Members)
      (nodes : Option (Array Node)) (success : decodeChildren context key members = .ok nodes) :
      DecodesChildren key members nodes := by
    cases members with
    | nil =>
      simp [decodeChildren] at success
      subst nodes
      exact .nil
    | cons member members =>
      cases member with
      | mk name tree =>
        cases hk : keyMatches name key with
        | false =>
          exact .skip hk (decodeChildren_sound context key members nodes
            (by simpa [decodeChildren, decodeChild, hk] using success))
        | true =>
          cases tree with
          | scalar value => simp [decodeChildren, decodeChild, hk] at success
          | object entries => simp [decodeChildren, decodeChild, hk] at success
          | array values =>
            cases hv : decodeNodes values with
            | error error => simp [decodeChildren, decodeChild, hk, hv] at success
            | ok decoded =>
              simp [decodeChildren, decodeChild, hk, hv] at success
              subst nodes
              exact .found hk (decodeNodes_sound _ _ hv)
  termination_by sizeOf members
  decreasing_by all_goals (simp_all; omega)
end

mutual
  theorem decodeTreeCore_complete {tree : Tree} {node : Node}
      (schema : DecodesTree tree node) : decodeTreeCore tree = .ok node := by
    cases schema with
    | absent hc => simp [decodeTreeCore, hc]
    | comment hc => simp [decodeTreeCore, hc]
    | association hc hi hs =>
      simp [decodeTreeCore, hc, decodeChildren_complete "generic association" hi, hs]
    | node hc hi hf =>
      simp [decodeTreeCore, hc, decodeChildren_complete _ hi, decodeChildren_complete _ hf]
  termination_by sizeOf tree

  theorem decodeNodes_complete {trees : List Tree} {nodes : Nodes}
      (schema : DecodesNodes trees nodes) : decodeNodes trees = .ok nodes := by
    cases schema with
    | nil => simp [decodeNodes]
    | cons ht hs => simp [decodeNodes, decodeTreeCore_complete ht, decodeNodes_complete hs]
  termination_by sizeOf trees

  theorem decodeChildren_complete (context : String) {key : String} {members : Members}
      {nodes : Option (Array Node)} (schema : DecodesChildren key members nodes) :
      decodeChildren context key members = .ok nodes := by
    cases schema with
    | nil => simp [decodeChildren]
    | skip hk hs =>
      rw [decodeChildren]
      simp only [hk, Bool.false_eq_true, ite_false]
      exact decodeChildren_complete context hs
    | found hk hs =>
      rw [decodeChildren]
      simp only [hk, ite_true]
      rw [decodeChild, decodeNodes_complete hs]
      rfl
  termination_by sizeOf members
  decreasing_by all_goals (simp_all; omega)
end

/-- The recursive implementation and the independent recursive schema agree. -/
theorem decodeTreeCore_iff {tree : Tree} {node : Node} :
    decodeTreeCore tree = .ok node ↔ DecodesTree tree node :=
  ⟨decodeTreeCore_sound tree node, decodeTreeCore_complete⟩

theorem decodeNodes_iff {trees : List Tree} {nodes : Nodes} :
    decodeNodes trees = .ok nodes ↔ DecodesNodes trees nodes :=
  ⟨decodeNodes_sound trees nodes, decodeNodes_complete⟩

theorem decodeChildren_iff (context : String) {key : String} {members : Members}
    {nodes : Option (Array Node)} :
    decodeChildren context key members = .ok nodes ↔ DecodesChildren key members nodes :=
  ⟨decodeChildren_sound context key members nodes, decodeChildren_complete context⟩

/-- Validation is an explicit part of the schema, preceding semantic decoding. -/
theorem decodeTree_iff {tree : Tree} {node : Node} :
    decodeTree tree = .ok node ↔ DecodesValue tree node := by
  cases hb : Silmaril.Formats.Json.Decode.treeToLean? tree <;>
    simp [decodeTree, DecodesValue, hb, decodeTreeCore_iff]

/-- Both successful values and staged errors are tied to the total Tree decoder. -/
theorem result_iff {tree : Tree} {result : Except Error Node} :
    decodeTree tree = result ↔ Result tree result := by
  constructor
  · intro h
    cases result with
    | ok node => exact .success (decodeTree_iff.mp h)
    | error error =>
      cases hb : Silmaril.Formats.Json.Decode.treeToLean? tree with
      | none =>
        have same : Error.bridge = error := by simpa [decodeTree, hb] using h
        subst error
        exact .bridge hb
      | some json => exact .semantic hb (by simpa [decodeTree, hb] using h)
  · intro h
    cases h with
    | success schema => exact decodeTree_iff.mpr schema
    | bridge hb => simp [decodeTree, hb]
    | semantic hb hc => simp [decodeTree, hb, hc]

theorem result_functional {tree : Tree} {first second : Except Error Node}
    (a : Result tree first) (b : Result tree second) : first = second :=
  (result_iff.mpr a).symm.trans (result_iff.mpr b)

theorem result_total (tree : Tree) : ∃ result, Result tree result :=
  ⟨decodeTree tree, result_iff.mp rfl⟩

theorem decode_iff {json : Silmaril.Formats.Json.Ast} {node : Node} :
    decode json = .ok node ↔ Decodes json node := decodeTree_iff

theorem decode?_iff {json : Silmaril.Formats.Json.Ast} {node : Node} :
    decode? json = some node ↔ Decodes json node := by
  cases h : decode json <;> simp [decode?, Except.toOption, h, ← decode_iff]

/-- A certified standard-JSON schema decoder, reusable by the generic pattern. -/
def certified : Silmaril.Formats.Json.Decode.Certified Node Decodes where
  decode := decode?
  sound := fun _ _ h => decode?_iff.mp h
  complete := fun _ _ h => decode?_iff.mpr h

theorem parse_iff {bytes : Silmaril.Formats.Bytes} {node : Node} :
    parse bytes = .ok node ↔ Parses bytes node := by
  change parse bytes = .ok node ↔
    ∃ json, Silmaril.Formats.Json.parse? bytes = some json ∧ Decodes json node
  cases hp : Silmaril.Formats.Json.parse? bytes <;> simp [parse, hp, decode_iff]

theorem decodes_functional : Decodes.Functional := by
  intro json a b ha hb
  exact Except.ok.inj ((decode_iff.mpr ha).symm.trans (decode_iff.mpr hb))

theorem parses_functional : Parses.Functional :=
  Silmaril.Formats.Json.Decode.text_functional decodes_functional

theorem translationUnit_iff {bytes : Silmaril.Formats.Bytes} {node : Node} :
    translationUnit bytes = .ok node ↔ ParsesTranslationUnit bytes node := by
  constructor
  · intro h
    cases hp : parse bytes with
    | error error => simp [translationUnit, hp] at h
    | ok result =>
      by_cases ht : IsTranslationUnit result
      · simp [translationUnit, hp, ht] at h
        subst node
        exact ⟨parse_iff.mp hp, ht⟩
      · simp [translationUnit, hp, ht] at h
  · rintro ⟨hp, ht⟩
    simp [translationUnit, parse_iff.mpr hp, ht]

theorem parsesTranslationUnit_functional : ParsesTranslationUnit.Functional := by
  intro bytes a b ha hb
  exact parses_functional ha.1 hb.1

/-- All header fields and both optional child arrays are retained exactly. -/
theorem node_metadata_iff {members : Members} {header : Silmaril.Clang.Header}
    {inner filler : Option (Array Node)} :
    DecodesTree (.object members) (.mk header inner filler) ↔
      classify members = .ok (.node header) ∧
      DecodesChildren "inner" members inner ∧ DecodesChildren "array_filler" members filler := by
  constructor
  · intro h
    cases h with
    | node hc hi hf => exact ⟨hc, hi, hf⟩
  · rintro ⟨hc, hi, hf⟩
    exact .node hc hi hf

theorem syntax_error {bytes : Silmaril.Formats.Bytes}
    (h : Silmaril.Formats.Json.parse? bytes = none) : parse bytes = .error .syntax := by
  simp [parse, h]

theorem bridge_error {tree : Tree}
    (h : Silmaril.Formats.Json.Decode.treeToLean? tree = none) :
    decodeTree tree = .error .bridge := by
  simp [decodeTree, h]

/-- Association children fail before a malformed selected flag is reported. -/
theorem association_inner_error {members : Members} {kind : String}
    {selected : Except Error (Option Bool)} {error : Error}
    (hc : classify members = .ok (.association kind selected))
    (hi : decodeChildren "generic association" "inner" members = .error error) :
    decodeTreeCore (.object members) = .error error := by
  simp [decodeTreeCore, hc, hi]

theorem association_selected_error {members : Members} {kind : String}
    {selected : Except Error (Option Bool)} {inner : Option (Array Node)} {error : Error}
    (hc : classify members = .ok (.association kind selected))
    (hi : decodeChildren "generic association" "inner" members = .ok inner)
    (hs : selected = .error error) :
    decodeTreeCore (.object members) = .error error := by
  simp [decodeTreeCore, hc, hi, hs]

theorem root_error {bytes : Silmaril.Formats.Bytes} {node : Node}
    (hp : parse bytes = .ok node) (ht : ¬ IsTranslationUnit node) :
    translationUnit bytes = .error (.root "the document is not a TranslationUnitDecl") := by
  simp [translationUnit, hp, ht]

end Silmaril.Compiler.Clang.TotalJson
