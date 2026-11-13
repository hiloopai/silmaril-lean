module

public import Silmaril.Project.WasmComponents.Code.Defs
public import Silmaril.Project.Shapes.Component.Thms
public import Silmaril.Wasm.Wit.Tool.Defs

/-!
# The code of a component: custom sections do not matter

* `replayX_filter`, `projectX_stripCustom`, `project_stripCustom`: the WIT projection
  (`wasm-wit project`) of a component is that of its code.
* `wellScopedC_stripCustom`: index scoping ignores custom sections.
* `lower_stripCustom`: so does the IR lowering, hence every `irDen C L`
  (`irDen_stripCustom`).
* `decodeSections_append`, `reencode_eq_of_trailing`: `wasm-wit decode` and `encode` ignore
  the trailing custom sections of a WIT package binary, except the first `package-docs`.
* Transfer to the standard shapes: `CompValid`, `HasWorld` (`hasWorld_iff_of_codeEq`) and
  `DigestBehaviourEq` (`digestBehaviourEq_of_codeEq`, for every denotation that ignores custom
  sections).
* `Task.parse_codeSections` (open, frozen): two binaries that parse and have the same framed
  non-custom sections (`codeSections`, what `same_code` compares) have the same code. The pilot's
  conclusions about `wasi:io@0.2.12` are stated under it.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents

open Silmaril.Wasm.Component.Binary (Ast Section)
open Silmaril.Wasm.Wit.Project (XState replayX stepX resExport splitSection projectX)

/-- The predicate `stripCustom` keeps. -/
abbrev keep (s : Section) : Bool := !isCustom s

theorem stripCustom_sections (c : Ast) : (stripCustom c).sections = c.sections.filter keep := rfl

theorem stripCustom_idem (c : Ast) : stripCustom (stripCustom c) = stripCustom c := by
  simp [stripCustom, Ast.sections, List.filter_filter]

theorem CodeEq.refl (a : Ast) : CodeEq a a := rfl

theorem CodeEq.symm {a b : Ast} (h : CodeEq a b) : CodeEq b a := Eq.symm h

theorem CodeEq.trans {a b c : Ast} (h₁ : CodeEq a b) (h₂ : CodeEq b c) : CodeEq a c := Eq.trans h₁ h₂

theorem codeEq_stripCustom (a : Ast) : CodeEq (stripCustom a) a := stripCustom_idem a

/-! ## Splitting sections -/

theorem splitSection_filter (s : Section) :
    (splitSection s).filter keep = if isCustom s then [] else splitSection s := by
  cases s <;> simp [splitSection, isCustom, keep, List.filter_map, Function.comp_def]

/-- Splitting commutes with dropping custom sections. -/
theorem flatMap_split_filter (l : List Section) :
    (l.filter keep).flatMap splitSection = (l.flatMap splitSection).filter keep := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.flatMap_cons, List.filter_append, splitSection_filter, ← ih]
    cases h : isCustom s <;> simp [keep, h]

/-! ## The projection -/

theorem resExport_filter (t : Nat) (l : List Section) :
    resExport t (l.filter keep) = resExport t l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | exports xs =>
      rcases xs with _ | ⟨e, _ | _⟩ <;> simp [keep, isCustom, resExport, ih]
    | _ => simp [keep, isCustom, resExport, ih]

theorem stepX_filter (s : XState) (l : List Section) (x : Section) :
    stepX s (l.filter keep) x = stepX s l x := by
  unfold stepX
  split <;> simp only [resExport_filter]

theorem stepX_custom (s : XState) (l : List Section) (n : String) (d : ByteArray) :
    stepX s l (.custom n d) = some s := rfl

/-- **The extended replay ignores custom sections.** -/
theorem replayX_filter (s : XState) (l : List Section) :
    replayX s (l.filter keep) = replayX s l := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    cases hx : isCustom x
    · simp only [List.filter_cons, keep, hx, Bool.not_false, ite_true, replayX, stepX_filter]
      congr 1
      funext s'
      exact ih s'
    · cases x <;> simp_all [isCustom, replayX, stepX_custom, keep]

/-- **`wasm-wit project` ignores custom sections.** -/
theorem projectX_stripCustom (c : Ast) : projectX (stripCustom c) = projectX c := by
  simp only [projectX, stripCustom_sections, flatMap_split_filter, replayX_filter]

theorem replay_filter (s : Silmaril.Wasm.Wit.Project.PState) (l : List Section) :
    Silmaril.Wasm.Wit.Project.replay s (l.filter keep) = Silmaril.Wasm.Wit.Project.replay s l := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    cases hx : isCustom x
    · simp only [List.filter_cons, keep, hx, Bool.not_false, ite_true,
        Silmaril.Wasm.Wit.Project.replay]
      congr 1
      funext s'
      exact ih s'
    · cases x <;> simp_all [isCustom, Silmaril.Wasm.Wit.Project.replay,
        Silmaril.Wasm.Wit.Project.step, keep]

/-- The plain projection ignores custom sections. -/
theorem project_stripCustom (c : Ast) :
    Silmaril.Wasm.Wit.Project.project (stripCustom c) = Silmaril.Wasm.Wit.Project.project c := by
  simp only [Silmaril.Wasm.Wit.Project.project, stripCustom_sections, flatMap_split_filter,
    replay_filter]

/-! ## Index scoping -/

theorem cCheck_filter (k : Silmaril.Wasm.Wit.Project.CCount) (l : List Section) :
    Silmaril.Wasm.Wit.Project.cCheck k (l.filter keep) = Silmaril.Wasm.Wit.Project.cCheck k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    cases hx : isCustom x
    · simp only [List.filter_cons, keep, hx, Bool.not_false, ite_true,
        Silmaril.Wasm.Wit.Project.cCheck]
      congr 1
      funext k'
      exact ih k'
    · cases x <;> simp_all [isCustom, Silmaril.Wasm.Wit.Project.cCheck,
        Silmaril.Wasm.Wit.Project.cStep, keep]

theorem wellScopedC_stripCustom (c : Ast) :
    Silmaril.Wasm.Wit.Project.wellScopedC (stripCustom c) = Silmaril.Wasm.Wit.Project.wellScopedC c := by
  simp only [Silmaril.Wasm.Wit.Project.wellScopedC, stripCustom_sections, flatMap_split_filter,
    cCheck_filter]

/-! ## The IR lowering -/

theorem forM_filter {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → Bool)
    (f : α → m PUnit) (hf : ∀ x, p x = false → f x = pure ⟨⟩) (l : List α) :
    (l.filter p).forM f = l.forM f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hx : p x
    · simp [hx, hf x hx, ih]
    · simp only [List.filter_cons, hx, ite_true]
      show (do f x; (l.filter p).forM f) = (do f x; l.forM f)
      rw [ih]

theorem forIn_filter {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (p : α → Bool)
    (f : α → β → m (ForInStep β)) (hf : ∀ x r, p x = false → f x r = pure (.yield r))
    (l : List α) (b : β) : forIn (l.filter p) b f = forIn l b f := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    cases hx : p x
    · simp [hx, hf x b hx, ih]
    · simp only [List.filter_cons, hx, ite_true, List.forIn_cons]
      congr 1
      funext r
      cases r <;> simp [ih]

theorem importsPass_filter (l : List Section) :
    Silmaril.Wasm.Component.Binary.Lower.importsPass (l.filter keep) =
      Silmaril.Wasm.Component.Binary.Lower.importsPass l := by
  unfold Silmaril.Wasm.Component.Binary.Lower.importsPass
  dsimp only
  rw [forIn_filter]
  intro x r hx
  cases x <;> first | rfl | simp [keep, isCustom] at hx

/-- **The IR lowering ignores custom sections.** -/
theorem lower_stripCustom (c : Ast) :
    Silmaril.Wasm.Component.Binary.lower (stripCustom c) = Silmaril.Wasm.Component.Binary.lower c := by
  have hs : (c.sections.filter keep).forM Silmaril.Wasm.Component.Binary.Lower.section_ =
      c.sections.forM Silmaril.Wasm.Component.Binary.Lower.section_ := by
    refine forM_filter _ _ ?_ _
    intro x hx
    cases x <;> first | rfl | simp [keep, isCustom] at hx
  simp only [Silmaril.Wasm.Component.Binary.lower, stripCustom_sections, importsPass_filter, hs]

/-- Every `irDen C L` ignores custom sections. -/
theorem irDen_stripCustom (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) (c : Ast) : irDen C L (stripCustom c) = irDen C L c := by
  simp only [irDen, lower_stripCustom]

/-! ## WIT packages: `wasm-wit decode` and `encode`

A WIT package binary lists its items, then its custom sections; `decodeSections` reads the items
and the first `package-docs` section and ignores the other custom sections. -/

open Silmaril.Wasm.Wit.Binary (splitCustom decodeSections decodeEnv decodePackage)

/-- The name and contents of the custom sections of a list. -/
def customPairs : List Section → List (String × ByteArray)
  | [] => []
  | .custom n d :: ss => (n, d) :: customPairs ss
  | _ :: ss => customPairs ss

theorem splitCustom_customs {cs : List Section} (h : ∀ s ∈ cs, isCustom s = true) :
    splitCustom cs = ([], customPairs cs) := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    have hs := h s (List.mem_cons_self ..)
    have ih := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    cases s <;> simp_all [isCustom, splitCustom, customPairs]

/-- Items whose last section is not custom, then custom sections: `splitCustom` separates them. -/
theorem splitCustom_append {items cs : List Section} {s : Section} (hs : isCustom s = false)
    (h : ∀ t ∈ cs, isCustom t = true) :
    splitCustom (items ++ s :: cs) = (items ++ [s], customPairs cs) := by
  induction items with
  | nil =>
    cases s <;> simp_all [isCustom, splitCustom, splitCustom_customs h]
  | cons x items ih =>
    cases x <;> simp [splitCustom, ih]

/-- **`wasm-wit decode` ignores trailing custom sections other than `package-docs`.** -/
theorem decodeSections_append {items cs₁ cs₂ : List Section} {s : Section}
    (hs : isCustom s = false) (h₁ : ∀ t ∈ cs₁, isCustom t = true)
    (h₂ : ∀ t ∈ cs₂, isCustom t = true)
    (hd : (customPairs cs₁).find? (·.1 = "package-docs") =
      (customPairs cs₂).find? (·.1 = "package-docs")) :
    decodeSections (items ++ s :: cs₁) = decodeSections (items ++ s :: cs₂) := by
  simp only [decodeSections, splitCustom_append hs h₁, splitCustom_append hs h₂, hd]

/-- Two WIT binaries that parse to the same items followed by custom sections with the same
`package-docs`: **`wasm-wit encode` gives the same bytes for both** (`Wit.Tool.reencode`). -/
theorem reencode_eq_of_trailing {x y : ByteArray} {items cs₁ cs₂ : List Section} {s : Section}
    (hx : Silmaril.Wasm.Component.Binary.parse x = .ok (.mk (items ++ s :: cs₁)))
    (hy : Silmaril.Wasm.Component.Binary.parse y = .ok (.mk (items ++ s :: cs₂)))
    (hs : isCustom s = false) (h₁ : ∀ t ∈ cs₁, isCustom t = true)
    (h₂ : ∀ t ∈ cs₂, isCustom t = true)
    (hd : (customPairs cs₁).find? (·.1 = "package-docs") =
      (customPairs cs₂).find? (·.1 = "package-docs")) :
    Silmaril.Wasm.Wit.Tool.reencode x = Silmaril.Wasm.Wit.Tool.reencode y := by
  simp only [Silmaril.Wasm.Wit.Tool.reencode, Silmaril.Wasm.Wit.Tool.decode, decodePackage, decodeEnv,
    hx, hy, decodeSections_append hs h₁ h₂ hd, splitCustom_append hs h₁, splitCustom_append hs h₂]

/-! ## The standard shapes -/

open Silmaril.Project.Shapes.Component

theorem projectX_eq_of_codeEq {a b : Ast} (h : CodeEq a b) : projectX a = projectX b := by
  rw [← projectX_stripCustom a, ← projectX_stripCustom b, h]

theorem compValid_iff_of_codeEq {a b : Ast} (h : CodeEq a b) : CompValid a ↔ CompValid b := by
  unfold CompValid
  rw [← wellScopedC_stripCustom a, ← wellScopedC_stripCustom b, h]

/-- **One code, one world.** -/
theorem hasWorld_iff_of_codeEq {a b : Ast} (h : CodeEq a b) (W : Silmaril.Wasm.Wit.Project.WorldType) :
    Shapes.Component.HasWorld a W ↔ Shapes.Component.HasWorld b W := by
  simp only [Shapes.Component.HasWorld, projectX_eq_of_codeEq h]

/-- **One code, one behaviour**: two releases that decode to components with the same code are
behaviourally equal under every denotation that ignores custom sections. -/
theorem digestBehaviourEq_of_codeEq {W : Silmaril.Wasi.World} {den : Ast → W.Model}
    (hden : ∀ c, den (stripCustom c) = den c) {X Y : Value Ast} {a b : Ast}
    (ha : X.Is a) (hb : Y.Is b) (h : CodeEq a b) : DigestBehaviourEq den X Y :=
  ⟨a, b, ha, hb, by rw [← hden a, ← hden b, h]⟩

/-! ## The byte level (open) -/

/-- Open (frozen): **the framing determines the code**. Two component binaries that parse and
have the same framed non-custom sections (`codeSections`: ids and raw bodies, in order) have
the same code. Expected to follow from the section grammar (`Binary.sectionG`): a parse
explains each frame as one section, and a section is a function of its id and body (up to the
nesting depth, which is only a bound). -/
def Task.parse_codeSections : Prop :=
  ∀ (x y : ByteArray) (a b : Ast), Silmaril.Wasm.Component.Binary.parse x = .ok a →
    Silmaril.Wasm.Component.Binary.parse y = .ok b → codeSections x = codeSections y → CodeEq a b

end Silmaril.Project.WasmComponents

end
