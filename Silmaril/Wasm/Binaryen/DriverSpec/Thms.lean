module

public import Silmaril.Wasm.Binaryen.DriverSpec.Defs
public import Silmaril.Cli.Text.Thms

@[expose] public section

namespace Silmaril.Wasm.Binaryen.DriverSpec

open Silmaril.Wasm.Binaryen.Driver Silmaril.Wasm.Binaryen.Pipeline Silmaril.Cli.Surface
open Silmaril.Wasm.Binaryen.Exe

theorem selectable_names :
    selectableStages.map ExtraStage.name = Silmaril.Cli.Spec.WasmOpt.passNames := by
  decide

theorem parseStage_name (s : ExtraStage) : parseStage s.name = .ok s := by
  rcases s with ((f | _ | _) | m | _) <;> (try cases f) <;> (try cases m) <;> rfl

/-- No stage name contains `,`. -/
theorem comma_not_mem_name (s : ExtraStage) : ',' ∉ s.name.toList := by
  rcases s with ((f | _ | _) | m | _) <;> (try cases f) <;> (try cases m) <;> decide

/-- Every stage name, split at `,`, is itself (no name has a comma). -/
theorem name_splitOn_comma (s : ExtraStage) : s.name.splitOn "," = [s.name] :=
  Silmaril.Cli.Text.splitOn_comma_of_not_mem _ (comma_not_mem_name s)

theorem parsePasses_name (s : ExtraStage) :
    parsePasses s.name = .ok [s] := by
  unfold parsePasses
  rw [name_splitOn_comma s]
  simp [List.mapM_cons, parseStage_name]

theorem parseArgs_verifiedStages (rest : List String) (plan : Plan) :
    parseArgs ("--verified-stages" :: rest) plan =
      parseArgs rest { plan with verifiedStages := true } := by
  simp [parseArgs]

theorem parseArgs_output (o : String) (rest : List String) (plan : Plan) :
    parseArgs ("-o" :: o :: rest) plan = (setOutput plan o >>= parseArgs rest) := by
  simp [parseArgs]

theorem startsWith_dash_of_append {pfx r : String} (hp : pfx.startsWith "-" = true) :
    (pfx ++ r).startsWith "-" = true := by
  simp only [String.startsWith_string_iff, String.toList_append] at hp ⊢
  exact hp.trans (List.prefix_append _ _)

theorem dropPrefix?_none {i pfx : String} (h : i.startsWith "-" = false)
    (hp : pfx.startsWith "-" = true) : i.dropPrefix? pfx = none := by
  cases hd : i.dropPrefix? pfx with
  | none => rfl
  | some r =>
    have := String.eq_append_of_dropPrefix?_string_eq_some hd
    rw [this, startsWith_dash_of_append hp] at h
    cases h

theorem ne_of_startsWith {i L : String} (h : i.startsWith "-" = false)
    (hL : L.startsWith "-" = true) : i ≠ L := by
  rintro rfl
  rw [hL] at h
  cases h

theorem parseOptCompatPreset_plain {i : String} (h : i.startsWith "-" = false) :
    parseOptCompatPreset i = none := by
  unfold parseOptCompatPreset
  split
  all_goals first
    | rfl
    | simp at h

theorem namedFlag?_plain {i : String} (h : i.startsWith "-" = false) : namedFlag? i = none := by
  unfold namedFlag?
  rw [List.find?_eq_none]
  intro x _ heq
  have : i = "--" ++ x.name := by simpa using heq
  rw [this, startsWith_dash_of_append (by simp)] at h
  cases h

/-- On the verified-stages path, a token that does not start with `-` is the input path. -/
theorem parseArgs_plain {i : String} (h : i.startsWith "-" = false) (rest : List String)
    (plan : Plan) : parseArgs (i :: rest) plan = (setInput plan i >>= parseArgs rest) := by
  have hp := parseOptCompatPreset_plain h
  have hn := namedFlag?_plain h
  have h1 : i.dropPrefix? "--output=" = none := dropPrefix?_none h (by simp)
  have h2 : i.dropPrefix? "--passes=" = none := dropPrefix?_none h (by simp)
  have h3 : i.dropPrefix? "--rounds=" = none := dropPrefix?_none h (by simp)
  have hne : ∀ L : String, L.startsWith "-" = true → i ≠ L := fun _ hL => ne_of_startsWith h hL
  rw [parseArgs.eq_def]
  split <;> simp_all

/-! ## The normal form, segment by segment -/

theorem parseArgs_nil (plan : Plan) : parseArgs [] plan = .ok plan := by
  simp [parseArgs]

theorem seg_verifiedStages (b : Bool) (rest : List String) (plan : Plan) :
    parseArgs ((if b then ["--verified-stages"] else []) ++ rest) plan =
      parseArgs rest (if b then { plan with verifiedStages := true } else plan) := by
  cases b <;> simp [parseArgs]

theorem seg_stats (b : Bool) (rest : List String) (plan : Plan) :
    parseArgs ((if b then ["--stats"] else []) ++ rest) plan =
      parseArgs rest (if b then { plan with stats := true } else plan) := by
  cases b <;> simp [parseArgs]

theorem seg_component (k : InputKind) (rest : List String) (plan : Plan) :
    parseArgs ((if k = .component then ["--component"] else []) ++ rest) plan =
      parseArgs rest (if k = .component then { plan with kind := .component } else plan) := by
  cases k <;> simp [parseArgs]

theorem seg_printPipeline (b : Bool) (rest : List String) (plan : Plan) :
    parseArgs ((if b then ["--print-pipeline"] else []) ++ rest) plan =
      parseArgs rest (if b then { plan with printPipeline := true } else plan) := by
  cases b <;> simp [parseArgs]

theorem seg_output (o : Option String) (ho : ∀ x, o = some x → x ≠ "") (rest : List String)
    (plan : Plan) (hp : plan.output = none) :
    parseArgs (outputArgs o ++ rest) plan =
      parseArgs rest { plan with output := o } := by
  cases plan
  cases o with
  | none => simp_all [outputArgs]
  | some x =>
    have hx := ho x rfl
    simp_all [outputArgs, parseArgs, setOutput]
    rfl

theorem seg_rounds (r : Nat) (rest : List String) (plan : Plan)
    (hp : plan.rounds = 1) :
    parseArgs ((if r = 1 then [] else ["--rounds", toString r]) ++ rest) plan =
      parseArgs rest { plan with rounds := r } := by
  by_cases hr : r = 1
  · subst hr
    cases plan
    simp_all
  · have hn : r.repr.toNat? = some r := Silmaril.Cli.Text.toNat?_toString r
    simp [hr, parseArgs, hn]

theorem seg_preset (q : CleanupPreset) (rest : List String) (plan : Plan) :
    parseArgs (q.name :: rest) plan =
      parseArgs rest { plan with itemsRev := .preset q :: plan.itemsRev } := by
  cases q <;> simp [parseArgs, CleanupPreset.name, parseOptCompatPreset]

theorem seg_items (l : List Item) (rest : List String)
    (plan : Plan) :
    parseArgs (l.flatMap Item.render ++ rest) plan =
      parseArgs rest { plan with itemsRev := l.reverse ++ plan.itemsRev } := by
  induction l generalizing plan with
  | nil => simp
  | cons it l ih =>
    cases it with
    | stage s =>
      simp only [List.flatMap_cons, Item.render, List.cons_append, List.nil_append]
      rw [show parseArgs ("--passes" :: s.name :: (l.flatMap Item.render ++ rest)) plan =
          parseArgs (l.flatMap Item.render ++ rest)
            { plan with itemsRev := .stage s :: plan.itemsRev } by
        simp [parseArgs, parsePasses_name s]
        rfl]
      rw [ih]
      simp
    | preset q =>
      simp only [List.flatMap_cons, Item.render, List.cons_append, List.nil_append]
      rw [seg_preset, ih]
      simp

theorem seg_input (i : Option String) (hi : ∀ x, i = some x → PlainPath x) (plan : Plan)
    (hp : plan.input = none) :
    parseArgs (inputArgs i) plan =
      .ok { plan with input := i } := by
  cases plan
  cases i with
  | none => simp_all [inputArgs, parseArgs_nil]
  | some x =>
    obtain ⟨hne, hx⟩ := hi x rfl
    rcases hx with rfl | hx
    · simp_all [inputArgs, parseArgs, setInput]
      rfl
    · simp only [inputArgs]
      rw [parseArgs_plain hx]
      simp_all [setInput]
      rfl

/-- **The driver reads the normal form back.** For every plan whose input is plain and
whose output is nonempty, `parseArgs (render p) {} = .ok p`: the verified-stages path of
`wasm-opt` reads the rendered argument vector as exactly that plan. Unconditional: the
facts about `String.splitOn` and `String.toNat?` it needs are `name_splitOn_comma` and
`Silmaril.Cli.Text.toNat?_toString`. -/
theorem parseArgs_render (p : Plan) (h : NormalForm p) : parseArgs (render p) {} = .ok p := by
  obtain ⟨hin, hout⟩ := h
  rcases p with ⟨input, output, itemsRev, rounds, verified, stats, printPipeline, kind⟩
  dsimp only at hin hout
  simp only [render, List.append_assoc]
  rw [seg_verifiedStages, seg_stats, seg_component, seg_printPipeline]
  rw [seg_output output hout _ _ (by split <;> split <;> split <;> split <;> rfl)]
  rw [seg_rounds _ _ _ (by split <;> split <;> split <;> split <;> rfl)]
  rw [seg_items]
  rw [seg_input input hin _ (by split <;> split <;> split <;> split <;> rfl)]
  congr 1
  cases verified <;> cases stats <;> cases printPipeline <;> cases kind <;> simp

/-- The normal form of a plan with `--verified-stages` takes the verified-stages path. -/
theorem usesVerifiedStages_render (p : Plan) (h : p.verifiedStages = true) :
    usesVerifiedStages (render p) = true := by
  simp [render, h, usesVerifiedStages, extraOnlyFlag]

end Silmaril.Wasm.Binaryen.DriverSpec
