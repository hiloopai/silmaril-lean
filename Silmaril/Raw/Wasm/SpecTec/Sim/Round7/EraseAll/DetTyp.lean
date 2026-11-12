module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms

/-!
# Round 7, the export swap: values typed over `tyA` have no `EXPORTS` record (unrefined)

`nx_of_hasTyp_A`, the `nxB` copy of `Round7.Determ.ef_of_hasTyp_A`: a value typed in `utf8Env B` at
a type over `Round7.TypAgree.tyA` has no record with an `EXPORTS` field (`Round7.Swap.nxB`), so it
is in every swap set. The original already shows that the typed records have no `EXPORTS` field;
this copy records it with `nxB` in place of `ExpFree`. Kept unrefined like its original.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (instsNoExp instsNoExp_A)

theorem nx_tuple {vs : List Value} : nxB (.tuple vs) = true ↔ ∀ w ∈ vs, nxB w = true := by
  simp [nxBs_eq_all]

theorem nx_list {vs : List Value} : nxB (.list vs) = true ↔ ∀ w ∈ vs, nxB w = true := by
  simp [nxBs_eq_all]

theorem nx_case {op : MixopS} {w : Value} : nxB (.case op w) = true ↔ nxB w = true := Iff.rfl

theorem nx_optSome {w : Value} : nxB (.opt (some w)) = true ↔ nxB w = true := Iff.rfl

theorem nxBf_of : ∀ {gs : List (AtomS × Value)}, (∀ g ∈ gs, nxB g.2 = true) →
    (∀ g ∈ gs, g.1 ≠ "EXPORTS") → nxBf gs = true
  | [], _, _ => rfl
  | (a, v) :: gs, h₁, h₂ => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨h₁ _ (List.mem_cons_self ..), h₂ _ (List.mem_cons_self ..)⟩,
      nxBf_of (fun g hg => h₁ g (List.mem_cons_of_mem _ hg))
        (fun g hg => h₂ g (List.mem_cons_of_mem _ hg))⟩

theorem nx_struct_of {gs : List (AtomS × Value)} (h₁ : ∀ g ∈ gs, nxB g.2 = true)
    (h₂ : ∀ g ∈ gs, g.1 ≠ "EXPORTS") : nxB (.struct gs) = true := nxBf_of h₁ h₂

variable (B : Builtins)

/-- **Values typed over `tyA` have no `EXPORTS` record**, at fuel `n`. -/
structure TypNX (n : Nat) : Prop where
  typ : ∀ ρ t v, TypsOk tyA ρ → tyOk tyA tyA t = true →
    hasTyp n (utf8Env B) ρ t v = .ok true → nxB v = true
  tup : ∀ ρ bs vs, TypsOk tyA ρ → bindsOk tyA tyA bs = true →
    hasTypTup n (utf8Env B) ρ bs vs = .ok true → ∀ v ∈ vs, nxB v = true
  list : ∀ ρ t vs, TypsOk tyA ρ → tyOk tyA tyA t = true →
    hasTypList n (utf8Env B) ρ t vs = .ok true → ∀ v ∈ vs, nxB v = true
  defTyp : ∀ ρ dt v, TypsOk tyA ρ → defTypOk tyA tyA false dt = true →
    instsNoExp [.instD [] [] dt] = true → hasTypDef n (utf8Env B) ρ dt v = .ok true → nxB v = true
  fields : ∀ ρ fs gs, TypsOk tyA ρ → fieldsOk tyA tyA false fs = true →
    (fs.all fun f => match f with | .mk a _ _ _ => a != "EXPORTS") = true →
    hasTypFields n (utf8Env B) ρ fs gs = .ok true →
      (∀ g ∈ gs, nxB g.2 = true) ∧ ∀ g ∈ gs, g.1 ≠ "EXPORTS"
  case : ∀ ρ cs op w, TypsOk tyA ρ → casesOk tyA tyA cs = true →
    hasTypCase n (utf8Env B) ρ cs op w = .ok true → nxB w = true
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgTyOk tyA w) → instsOk tyA tyA false insts = true →
    instsNoExp insts = true → hasTypInsts n (utf8Env B) insts ws v = .ok true → nxB v = true

theorem typNX_zero : TypNX B 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase, hasTypInsts]

theorem typNX_succ (m : Nat) (ih : TypNX B m) : TypNX B (m + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v hT ht h
    cases t with
    | boolT =>
        simp only [hasTyp] at h
        cases v <;> first | exact rfl | simp [Value.asBool?] at h
    | numT t =>
        simp only [hasTyp] at h
        cases v <;> first | exact rfl | simp [Value.asNum?] at h
    | textT =>
        simp only [hasTyp] at h
        cases v <;> first | exact rfl | simp [Value.asText?] at h
    | tupT bs =>
        simp only [tyOk] at ht
        simp only [hasTyp] at h
        cases v with
        | tuple vs => exact nx_tuple.2 (ih.tup _ _ _ hT ht h)
        | _ => simp [Value.asTuple?] at h
    | iterT t it =>
        simp only [tyOk, Bool.and_eq_true] at ht
        cases it with
        | opt =>
            simp only [hasTyp] at h
            cases v with
            | opt o =>
              cases o with
              | none => exact rfl
              | some w => exact nx_optSome.2 (ih.typ _ _ _ hT ht.1 h)
            | _ => simp [Value.asOpt?] at h
        | list =>
            simp only [hasTyp] at h
            cases v with
            | list vs => exact nx_list.2 (ih.list _ _ _ hT ht.1 h)
            | _ => simp [Value.asList?] at h
        | list1 =>
            simp only [hasTyp] at h
            cases v with
            | list vs =>
              simp only [Value.asList?] at h
              split at h
              · cases h
              · exact nx_list.2 (ih.list _ _ _ hT ht.1 h)
            | _ => simp [Value.asList?] at h
        | listN e x =>
            simp only [hasTyp] at h
            cases v with
            | list vs =>
              simp only [Value.asList?, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
              obtain ⟨_, _, _, _, h⟩ := h
              split at h
              · exact nx_list.2 (ih.list _ _ _ hT ht.1 h)
              · cases h
            | _ => simp [Value.asList?] at h
    | varT x args =>
        simp only [tyOk, Bool.and_eq_true] at ht
        simp only [hasTyp] at h
        cases hl : localTyp? ρ x args with
        | some t' =>
            rw [hl] at h
            have ht' : tyOk tyA tyA t' = true := by
              cases args with
              | nil =>
                  simp only [localTyp?] at hl
                  exact hT (x, t') (mem_of_find? hl)
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hT ht' h
        | none =>
            rw [hl] at h
            simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, findTyp?_utf8Env] at h
            obtain ⟨td, htd, ws, hws, h⟩ := h
            exact ih.insts _ _ _ (evalArgs_argTyOk hT ht.2 hws) (instsOk_A htd ht.1)
              (instsNoExp_A htd ht.1) h
  -- `hasTypTup`
  · intro ρ bs vs hT hbs h
    cases bs with
    | nil => cases vs <;> simp only [hasTypTup] at h <;> simp_all
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [bindsOk, Bool.and_eq_true] at hbs
            cases vs with
            | nil => simp
            | cons v vs =>
                simp only [hasTypTup, Res.bind_eq_ok] at h
                obtain ⟨b, hb, h⟩ := h
                cases b with
                | false => simp at h
                | true =>
                  simp only [↓reduceIte] at h
                  intro w hw
                  rcases List.mem_cons.1 hw with rfl | hw
                  · exact ih.typ _ _ _ hT hbs.1 hb
                  · exact ih.tup (ρ.bindVal x v) _ _ hT hbs.2 h w hw
  -- `hasTypList`
  · intro ρ t vs hT ht h
    cases vs with
    | nil => simp
    | cons v vs =>
        simp only [hasTypList, Res.bind_eq_ok] at h
        obtain ⟨b, hb, h⟩ := h
        cases b with
        | false => simp at h
        | true =>
          simp only [↓reduceIte] at h
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ih.typ _ _ _ hT ht hb
          · exact ih.list _ _ _ hT ht h w hw
  -- `hasTypDef`
  · intro ρ dt v hT hdt hne h
    cases dt with
    | aliasT t => simp only [defTypOk] at hdt; simp only [hasTypDef] at h; exact ih.typ _ _ _ hT hdt h
    | structT fs =>
        simp only [defTypOk] at hdt
        simp only [instsNoExp, List.all_cons, List.all_nil, Bool.and_true] at hne
        simp only [hasTypDef] at h
        cases v with
        | struct gs =>
          obtain ⟨h₁, h₂⟩ := ih.fields _ _ _ hT hdt hne h
          exact nx_struct_of h₁ h₂
        | _ => simp [Value.asStruct?] at h
    | variantT cs =>
        simp only [defTypOk] at hdt
        simp only [hasTypDef] at h
        cases v with
        | case op w => exact nx_case.2 (ih.case _ _ _ _ hT hdt h)
        | _ => simp [Value.asCase?] at h
  -- `hasTypFields`
  · intro ρ fs gs hT hfs hne h
    cases fs with
    | nil => cases gs <;> simp only [hasTypFields] at h <;> simp_all
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            simp only [fieldsOk, Bool.and_eq_true, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte] at hfs
            simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hne
            cases gs with
            | nil => simp
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields] at h
                split at h
                · rename_i haa
                  subst haa
                  simp only [Res.bind_eq_ok] at h
                  obtain ⟨b, hb, h⟩ := h
                  cases b with
                  | false => simp at h
                  | true =>
                    simp only [↓reduceIte, Res.bind_eq_ok] at h
                    obtain ⟨hp, _, h⟩ := h
                    cases hp with
                    | false => simp at h
                    | true =>
                      simp only [↓reduceIte] at h
                      obtain ⟨h₁, h₂⟩ := ih.fields _ _ _ hT hfs.2 hne.2 h
                      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
                      · rcases List.mem_cons.1 hp with rfl | hp
                        · exact ih.typ _ _ _ hT hfs.1.1 hb
                        · exact h₁ p hp
                      · rcases List.mem_cons.1 hp with rfl | hp
                        · exact hne.1
                        · exact h₂ p hp
                · cases h
  -- `hasTypCase`
  · intro ρ cs op w hT hcs h
    cases cs with
    | nil => simp only [hasTypCase] at h; cases h
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [casesOk, Bool.and_eq_true] at hcs
            obtain ⟨⟨⟨hct, _⟩, _⟩, hcs⟩ := hcs
            simp only [hasTypCase] at h
            split at h
            · simp only [Res.bind_eq_ok] at h
              obtain ⟨b, hb, h⟩ := h
              cases b with
              | false => simp at h
              | true => exact ih.typ _ _ _ hT hct hb
            · exact ih.case _ _ _ _ hT hcs h
  -- `hasTypInsts`
  · intro insts ws v hWT hins hne h
    cases insts with
    | nil => simp only [hasTypInsts] at h; cases h
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            simp only [instsOk, List.all_cons, Bool.and_eq_true] at hins
            obtain ⟨⟨_, hdt⟩, hins⟩ := hins
            have hne' : instsNoExp [.instD [] [] dt] = true ∧ instsNoExp insts = true := by
              simp only [instsNoExp, List.all_cons, Bool.and_eq_true] at hne ⊢
              exact ⟨⟨by cases dt <;> simp_all, rfl⟩, hne.2⟩
            simp only [hasTypInsts] at h
            rcases Script.elimUndef_eq_ok h with ⟨ρ', h', h⟩ | ⟨_, h⟩
            · exact ih.defTyp _ _ _ (matchArgs_typsOk m (typsOk_empty tyA) hWT h') hdt hne'.1 h
            · exact ih.insts _ _ _ hWT hins hne'.2 h

/-- **Values typed over `tyA` have no `EXPORTS` record**, at every fuel. -/
theorem typNX : ∀ n, TypNX B n
  | 0 => typNX_zero B
  | n + 1 => typNX_succ B n (typNX n)

/-- **A value typed in `utf8Env B` at a type over `tyA` has no `EXPORTS` record.** -/
theorem nx_of_hasTyp_A {ρ : VarEnv} {t : Typ} {v : Value} (hT : TypsOk tyA ρ)
    (ht : tyOk tyA tyA t = true) (h : HasTyp (utf8Env B) ρ t v) : nxB v = true := by
  obtain ⟨n, hn⟩ := h
  exact (typNX B n).typ _ _ _ hT ht hn

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
