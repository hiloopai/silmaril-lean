module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# Component WAT: printing does not see the normal form

`P.ast (norm c) = P.ast c`: grouping sections and respelling attribute-free
names do not change the printed items.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary Sexp

theorem name_normName (n : ExternName) : P.name (normName n) = P.name n := by
  obtain ⟨s, f⟩ := n
  cases f with
  | attrs as => cases as <;> rfl
  | _ => rfl

theorem inst_normInstance (x : InstanceExpr) : P.inst (normInstance x) = P.inst x := by
  cases x with
  | instantiate c args => rfl
  | exports es => simp [P.inst, normInstance, name_normName]

mutual
theorem defType_norm : ∀ t : DefType, P.defType (normDefType t) = P.defType t
  | .val _ => rfl
  | .func _ => rfl
  | .component ds => by
    show Sexp.list (_ :: P.componentDecls (normComponentDecls ds)) = _
    rw [componentDecls_norm ds]; rfl
  | .instance ds => by
    show Sexp.list (_ :: P.instanceDecls (normInstanceDecls ds)) = _
    rw [instanceDecls_norm ds]; rfl
  | .resource _ _ => rfl

theorem instanceDecl_norm : ∀ d : InstanceDecl,
    P.instanceDecl (normInstanceDecl d) = P.instanceDecl d
  | .coreType _ => rfl
  | .type t => by
    show Sexp.list [_, P.defType (normDefType t)] = _
    rw [defType_norm t]; rfl
  | .alias _ => rfl
  | .export n d => by
    show Sexp.list (_ :: P.name (normName n) ++ _) = _
    rw [name_normName]; rfl

theorem componentDecl_norm : ∀ d : ComponentDecl,
    P.componentDecl (normComponentDecl d) = P.componentDecl d
  | .import n d => by
    show Sexp.list (_ :: P.name (normName n) ++ _) = _
    rw [name_normName]; rfl
  | .inst d => by
    show P.instanceDecl (normInstanceDecl d) = _
    rw [instanceDecl_norm d]; rfl

theorem instanceDecls_norm : ∀ ds : List InstanceDecl,
    P.instanceDecls (normInstanceDecls ds) = P.instanceDecls ds
  | [] => rfl
  | d :: ds => by
    show P.instanceDecl (normInstanceDecl d) :: P.instanceDecls (normInstanceDecls ds) = _
    rw [instanceDecl_norm d, instanceDecls_norm ds]; rfl

theorem componentDecls_norm : ∀ ds : List ComponentDecl,
    P.componentDecls (normComponentDecls ds) = P.componentDecls ds
  | [] => rfl
  | d :: ds => by
    show P.componentDecl (normComponentDecl d) :: P.componentDecls (normComponentDecls ds) = _
    rw [componentDecl_norm d, componentDecls_norm ds]; rfl
end

theorem merge_section {s t u : Section} (h : R.merge s t = some u) :
    P.section_ u = P.section_ s ++ P.section_ t := by
  cases s <;> cases t <;> simp [R.merge] at h <;> subst h <;> simp [P.section_]

theorem sections_append (a b : List Section) :
    P.sections (a ++ b) = P.sections a ++ P.sections b := by
  induction a with
  | nil => rfl
  | cons s a ih =>
    show P.section_ s ++ P.sections (a ++ b) = (P.section_ s ++ P.sections a) ++ _
    rw [ih, List.append_assoc]

theorem sections_group : ∀ l : List Section, P.sections (R.group l) = P.sections l
  | [] => rfl
  | s :: ss => by
    have ih := sections_group ss
    show P.sections (match R.group ss with
      | [] => [s]
      | t :: ts => match R.merge s t with
        | some u => u :: ts
        | none => s :: t :: ts) = P.section_ s ++ P.sections ss
    rw [← ih]
    cases R.group ss with
    | nil => rfl
    | cons t ts =>
      simp only
      cases hm : R.merge s t with
      | none => rfl
      | some u =>
        show P.section_ u ++ P.sections ts = P.section_ s ++ (P.section_ t ++ P.sections ts)
        rw [merge_section hm, List.append_assoc]

theorem sections_map {α : Type} (f : α → Section) (g : α → Sexp)
    (h : ∀ x, P.section_ (f x) = [g x]) :
    ∀ xs : List α, P.sections (xs.map f) = xs.map g
  | [] => rfl
  | x :: xs => by
    show P.section_ (f x) ++ P.sections (xs.map f) = _
    rw [h x, sections_map f g h xs]; rfl

mutual
theorem section_norm : ∀ s : Section, P.sections (normSection s) = P.section_ s
  | .custom _ _ => rfl
  | .coreModule _ => rfl
  | .coreInstances xs => sections_map _ _ (fun _ => rfl) xs
  | .coreTypes xs => sections_map _ _ (fun _ => rfl) xs
  | .component c => by
    show P.section_ (.component (norm c)) ++ [] = _
    rw [List.append_nil]
    show [Sexp.list (_ :: P.ast (norm c))] = [Sexp.list (_ :: P.ast c)]
    rw [ast_norm c]
  | .instances xs => sections_map _ _ (fun x => by
      show [P.inst (normInstance x)] = _
      rw [inst_normInstance]) xs
  | .aliases xs => sections_map _ _ (fun _ => rfl) xs
  | .types xs => sections_map _ _ (fun x => by
      show [Sexp.list [_, P.defType (normDefType x)]] = _
      rw [defType_norm]) xs
  | .canons xs => sections_map _ _ (fun _ => rfl) xs
  | .start _ => rfl
  | .imports xs => sections_map _ _ (fun x => by
      show [Sexp.list (_ :: P.name (normName x.name) ++ _)] = _
      rw [name_normName]; rfl) xs
  | .exports xs => sections_map _ _ (fun x => by
      show [Sexp.list (_ :: P.name (normName x.name) ++ _)] = _
      rw [name_normName]; rfl) xs
  | .values xs => sections_map _ _ (fun _ => rfl) xs

theorem sections_norm : ∀ ss : List Section, P.sections (normSections ss) = P.sections ss
  | [] => rfl
  | s :: ss => by
    show P.sections (normSection s ++ normSections ss) = P.section_ s ++ P.sections ss
    rw [sections_append, section_norm s, sections_norm ss]

theorem ast_norm : ∀ c : Ast, P.ast (norm c) = P.ast c
  | .mk ss => by
    show P.sections (R.group (normSections ss)) = P.sections ss
    rw [sections_group, sections_norm ss]
end

/-- Printing does not see the normal form. -/
theorem toSexp_norm (c : Ast) : toSexp (norm c) = toSexp c := by
  simp only [toSexp, ast_norm]

end Silmaril.Wasm.Component.Wat
