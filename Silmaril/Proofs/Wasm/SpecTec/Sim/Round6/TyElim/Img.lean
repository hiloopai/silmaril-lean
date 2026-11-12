module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi4.WitnessBnd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Bounds

/-!
# Round 6: typed type values are images of Core types

SpecTec's `Heaptype_sub/bot` relates `BOT` to *every* value its quantifier `heaptype` is typed
at, so reading `Reftype_sub {}` back (`AgreeTy.subElim`) needs that a typed `heaptype` value is
the image `tyV h` of a Core heap type. This file inverts the type grammar of the pinned script's
`rec` group (definition 95) and its satellites (`deftype`, `typeidx`, `n`, `final`, `mut`,
`null`):

* `img_all`: by strong induction on the size of the value, a value typed at `heaptype`,
  `typeuse`, `rectype`, `subtype`, `comptype`, `fieldtype`, `storagetype` or `valtype` is the
  image of a Core type of the corresponding sort;
* `img_heap`, `img_def`: the two instances the elimination uses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV natV idxV)
open Round5.Multi (HasE hasE_of_valsOnly listT_inv)

variable {B : Builtins}

/-- `v` is the image of a Core type of sort `k`. -/
def Img (k : TKind) (v : Value) : Prop := ∃ t : Ty k, v = tyV t

/-- A list of images is the image of a sequence. -/
theorem img_list {k : TKind} : ∀ {l : List Value}, (∀ u ∈ l, Img k u) → Img (.list k) (.list l)
  | [], _ => ⟨.nil, rfl⟩
  | a :: l, h => by
    obtain ⟨t, rfl⟩ := h a (List.mem_cons_self ..)
    obtain ⟨ts, hts⟩ := img_list (l := l) fun u hu => h u (List.mem_cons_of_mem _ hu)
    refine ⟨.cons t ts, ?_⟩
    simp only [tyV, ← hts, Silmaril.SpecTec.Equiv.Validation.consV]

/-! ## Typing, inverted -/

/-- A typed case of a variant: its operator is declared and its payload has the declared type. -/
theorem hasTypCase_find {σ : VarEnv} : ∀ {cs : List TypCase} {op : MixopS} {w : Value},
    HasTypCase (simEnv B) σ cs op w →
      ∃ t prems, IntNumeric.findCase cs op = some (t, prems) ∧ HasTyp (simEnv B) σ t w
  | [], _, _, h => absurd h not_hasTypCase_nil
  | .mk o t qs prems :: cs, op, w, h => by
    by_cases ho : o = op
    · exact ⟨t, prems, by simp [IntNumeric.findCase, ho], ((hasTypCase_cons_hit_iffQ ho).1 h).1⟩
    · obtain ⟨t', p', hf, ht⟩ := hasTypCase_find ((hasTypCase_cons_miss_iff ho).1 h)
      exact ⟨t', p', by simp [IntNumeric.findCase, ho, hf], ht⟩

/-- A value of a closed one-instance variant is a case of it, with a typed payload. -/
theorem case_of_hasE {x : IL.Id} {cs : List TypCase} {v : Value}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)])) (h : HasE B x v) :
    ∃ op w t prems, v = .case op w ∧ IntNumeric.findCase cs op = some (t, prems) ∧
      HasTyp (simEnv B) VarEnv.empty t w := by
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff rfl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, prems, hf, ht⟩ := hasTypCase_find hc
    exact ⟨op, w, t, prems, rfl, hf, ht⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- The empty tuple type has only the empty tuple. -/
theorem tup0_inv {σ : VarEnv} {w : Value} (h : HasTyp (simEnv B) σ (.tupT []) w) :
    w = .tuple [] := by
  obtain ⟨vs, rfl, ht⟩ := hasTyp_tupT_iff.1 h
  rw [hasTypTup_nil_iff.1 ht]

/-- A typed pair. -/
theorem tup2_inv {σ : VarEnv} {a b : IL.Id} {τ₁ τ₂ : Typ} {w : Value}
    (h : HasTyp (simEnv B) σ (.tupT [.mk a τ₁, .mk b τ₂]) w) :
    ∃ x y, w = .tuple [x, y] ∧ HasTyp (simEnv B) σ τ₁ x ∧
      HasTyp (simEnv B) (σ.bindVal a x) τ₂ y := by
  obtain ⟨vs, rfl, ht⟩ := hasTyp_tupT_iff.1 h
  obtain ⟨x, vs₁, rfl, hx, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨y, vs₂, rfl, hy, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  rw [hasTypTup_nil_iff.1 ht₂]
  exact ⟨x, y, rfl, hx, hy⟩

/-- A typed triple. -/
theorem tup3_inv {σ : VarEnv} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {w : Value}
    (h : HasTyp (simEnv B) σ (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) w) :
    ∃ x y z, w = .tuple [x, y, z] ∧ HasTyp (simEnv B) σ τ₁ x ∧
      HasTyp (simEnv B) (σ.bindVal a x) τ₂ y ∧
      HasTyp (simEnv B) ((σ.bindVal a x).bindVal b y) τ₃ z := by
  obtain ⟨vs, rfl, ht⟩ := hasTyp_tupT_iff.1 h
  obtain ⟨x, vs₁, rfl, hx, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨y, vs₂, rfl, hy, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨z, vs₃, rfl, hz, ht₃⟩ := hasTypTup_cons_iff.1 ht₂
  rw [hasTypTup_nil_iff.1 ht₃]
  exact ⟨x, y, z, rfl, hx, hy, hz⟩

/-- A `nat` is a natural numeral. -/
theorem nat_inv {σ : VarEnv} {v : Value} (h : HasTyp (simEnv B) σ (.numT .natT) v) :
    ∃ i, v = natV i := by
  obtain ⟨m, rfl, hm⟩ := hasTyp_numT_iff.1 h
  cases m with
  | natN i => exact ⟨i, rfl⟩
  | _ => simp [Num.toTyp, Num.subTyp] at hm

/-- An `n` is a natural numeral. -/
theorem n_inv {σ : VarEnv} (hσ : ValsOnly σ) {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "n" []) v) : ∃ i, v = natV i :=
  nat_inv (ConfigOk.hasTyp_of_closedAlias hσ Typing.findTyp_n h)

/-- The instance of `uN(32)`, after its argument pattern `N` matched `32`. -/
theorem hasTypDef_uN32 {σ : VarEnv} {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "uN" [.expA (.numE (.natN 32))]) v) :
    HasTypDef (simEnv B) (VarEnv.empty.bindVal "N" (.num (.natN 32)))
      (.variantT (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d22 0)) v := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_uN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨v', hv, rfl⟩ := evalArgs_expA_iff.1 hargs
  obtain rfl := evalExp_numE_iff.1 hv
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA (.varE "N")] [.val (.num (.natN 32))]
      (VarEnv.empty.bindVal "N" (.num (.natN 32))) :=
    matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil
  rcases hasTypInsts_cons_inv hi with ⟨σ', ⟨k, hk⟩, hd⟩ | hrest
  · rwa [IntNumeric.matchArgs_det hm0 hk] at hd
  · exact absurd hrest not_hasTypInsts_nil

/-- A `typeidx` is an index numeral. -/
theorem typeidx_inv {σ : VarEnv} (hσ : ValsOnly σ) {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "typeidx" []) v) : ∃ x, v = idxV x := by
  have hu := ConfigOk.hasTyp_of_closedAlias ⟨rfl, rfl, rfl⟩ Typing.findTyp_u32
    (ConfigOk.hasTyp_of_closedAlias ⟨rfl, rfl, rfl⟩ Typing.findTyp_idx
      (ConfigOk.hasTyp_of_closedAlias hσ Typing.findTyp_typeidx h))
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 (hasTypDef_uN32 hu)
  rw [ConfigOk.uNCases] at hc
  obtain ⟨t, prems, hf, ht⟩ := hasTypCase_find hc
  simp only [IntNumeric.findCase] at hf
  split_ifs at hf with ho
  simp only [Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, -⟩ := hf
  subst ho
  obtain ⟨vs, rfl, ht'⟩ := hasTyp_tupT_iff.1 ht
  obtain ⟨x, vs₁, rfl, hx, ht₁⟩ := hasTypTup_cons_iff.1 ht'
  rw [hasTypTup_nil_iff.1 ht₁]
  obtain ⟨i, rfl⟩ := nat_inv hx
  exact ⟨i, rfl⟩

/-! ## The case lists of the type grammar -/

/-- `tupT []`. -/
abbrev unitT : Typ := .tupT []

/-- `typeuse`'s cases. -/
def useCases : List TypCase :=
  [.mk "_IDX" (.varT "typeidx" []) [] [],
   .mk "_DEF" (.tupT [.mk "rectype" (.varT "rectype" []), .mk "n" (.varT "n" [])]) [] [],
   .mk "REC" (.varT "n" []) [] []]

/-- A nullary case. -/
abbrev nullCase (o : MixopS) : TypCase := .mk o unitT [] []

/-- The twelve abstract heap types' operators. -/
def absOps : List MixopS :=
  ["ANY", "EQ", "I31", "STRUCT", "ARRAY", "NONE", "FUNC", "NOFUNC", "EXN", "NOEXN", "EXTERN",
   "NOEXTERN"]

/-- The number and vector types' operators. -/
def numOps : List MixopS := ["I32", "I64", "F32", "F64", "V128"]

/-- `heaptype`'s cases. -/
def heapCases : List TypCase :=
  (absOps ++ ["BOT"]).map nullCase ++
  [.mk "_IDX" (.varT "typeidx" []) [] [],
   .mk "_DEF" (.tupT [.mk "rectype" (.varT "rectype" []), .mk "n" (.varT "n" [])]) [] [],
   .mk "REC" (.varT "n" []) [] []]

/-- `REF null? heaptype`'s payload type. -/
abbrev refPayT : Typ :=
  .tupT [.mk "null?" (.iterT (.varT "null" []) .opt), .mk "heaptype" (.varT "heaptype" [])]

/-- `valtype`'s cases. -/
def valCases : List TypCase :=
  numOps.map nullCase ++ (.mk "REF" refPayT [] [] :: ["BOT"].map nullCase)

/-- `storagetype`'s cases. -/
def storageCases : List TypCase :=
  numOps.map nullCase ++ (.mk "REF" refPayT [] [] :: ["BOT", "I8", "I16"].map nullCase)

/-- `fieldtype`'s cases. -/
def fieldCases : List TypCase :=
  [.mk "%%" (.tupT [.mk "mut?" (.iterT (.varT "mut" []) .opt),
    .mk "storagetype" (.varT "storagetype" [])]) [] []]

/-- `comptype`'s cases. -/
def compCases : List TypCase :=
  [.mk "STRUCT" (.varT "list" [.typA (.varT "fieldtype" [])]) [] [],
   .mk "ARRAY" (.varT "fieldtype" []) [] [],
   .mk "FUNC%->%" (.tupT [.mk "resulttype" (.varT "resulttype" []),
    .mk "resulttype" (.varT "resulttype" [])]) [] []]

/-- `subtype`'s cases. -/
def subCases : List TypCase :=
  [.mk "SUB" (.tupT [.mk "final?" (.iterT (.varT "final" []) .opt),
    .mk "typeuse*" (.iterT (.varT "typeuse" []) .list), .mk "comptype" (.varT "comptype" [])])
    [] []]

/-- `rectype`'s cases. -/
def recCases : List TypCase := [.mk "REC" (.varT "list" [.typA (.varT "subtype" [])]) [] []]

/-- `deftype`'s cases. -/
def defCases : List TypCase :=
  [.mk "_DEF" (.tupT [.mk "rectype" (.varT "rectype" []), .mk "n" (.varT "n" [])]) [] []]

set_option maxRecDepth 100000 in
theorem findTyp_typeuse' : (simEnv B).findTyp? "typeuse" =
    some ([], [.instD [] [] (.variantT useCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_heaptype' : (simEnv B).findTyp? "heaptype" =
    some ([], [.instD [] [] (.variantT heapCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_valtype' : (simEnv B).findTyp? "valtype" =
    some ([], [.instD [] [] (.variantT valCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_storagetype' : (simEnv B).findTyp? "storagetype" =
    some ([], [.instD [] [] (.variantT storageCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_fieldtype' : (simEnv B).findTyp? "fieldtype" =
    some ([], [.instD [] [] (.variantT fieldCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_comptype' : (simEnv B).findTyp? "comptype" =
    some ([], [.instD [] [] (.variantT compCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_subtype' : (simEnv B).findTyp? "subtype" =
    some ([], [.instD [] [] (.variantT subCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_rectype' : (simEnv B).findTyp? "rectype" =
    some ([], [.instD [] [] (.variantT recCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_deftype' : (simEnv B).findTyp? "deftype" =
    some ([], [.instD [] [] (.variantT defCases)]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_final' : (simEnv B).findTyp? "final" =
    some ([], [.instD [] [] (.variantT [.mk "FINAL" unitT [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_null' : (simEnv B).findTyp? "null" =
    some ([], [.instD [] [] (.variantT [.mk "NULL" unitT [] []])]) := rfl

/-! ## Sizes -/

theorem sz_case (op : MixopS) (w : Value) : sizeOf w < sizeOf (Value.case op w) := by
  simp only [Value.case.sizeOf_spec]; omega

theorem sz_tuple {l : List Value} {a : Value} (h : a ∈ l) : sizeOf a < sizeOf (Value.tuple l) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Value.tuple.sizeOf_spec]; omega

theorem sz_list {l : List Value} {a : Value} (h : a ∈ l) : sizeOf a < sizeOf (Value.list l) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Value.list.sizeOf_spec]; omega

theorem sz_opt (a : Value) : sizeOf a < sizeOf (Value.opt (some a)) := by
  simp only [Value.opt.sizeOf_spec, Option.some.sizeOf_spec]; omega

/-- An element of the payload `%(l)` of a case, inside it. -/
theorem sz_pct {op : MixopS} {l : List Value} {u : Value} (h : u ∈ l) :
    sizeOf u < sizeOf (Value.case op (.case "%" (.tuple [.list l]))) :=
  (sz_list h).trans <| (sz_tuple (List.mem_singleton_self _)).trans <|
    (sz_case _ _).trans (sz_case _ _)

/-! ## The sorts, one at a time -/

/-- The images of the eight sorts the grammar is closed under. -/
def ImgAll (B : Builtins) (v : Value) : Prop :=
  (HasE B "heaptype" v → Img .heap v) ∧ (HasE B "typeuse" v → Img .use v) ∧
  (HasE B "rectype" v → Img .group v) ∧ (HasE B "subtype" v → Img .sub v) ∧
  (HasE B "comptype" v → Img .comp v) ∧ (HasE B "fieldtype" v → Img .field v) ∧
  (HasE B "storagetype" v → Img .storage v) ∧ (HasE B "valtype" v → Img .val v)

/-- The induction hypothesis: every smaller value is an image at its sorts. -/
abbrev IHB (B : Builtins) (v : Value) : Prop := ∀ u, sizeOf u < sizeOf v → ImgAll B u

theorem pair_eq {α β : Type} {a c : α} {b d : β} (h : some (a, b) = some (c, d)) :
    a = c ∧ b = d := by
  simpa using h

/-- `_DEF (rectype, n)`. -/
theorem img_defPay {v w : Value} (hw : sizeOf w < sizeOf v) (ih : IHB B v)
    (h : HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "rectype" (.varT "rectype" []), .mk "n" (.varT "n" [])]) w) :
    ∃ d : DefType, Value.case "_DEF" w = tyV d := by
  obtain ⟨r, x, rfl, hr, hx⟩ := tup2_inv h
  obtain ⟨i, rfl⟩ := n_inv ⟨rfl, rfl, rfl⟩ hx
  obtain ⟨g, rfl⟩ := (ih r ((sz_tuple (List.mem_cons_self ..)).trans hw)).2.2.1 hr
  exact ⟨.defn g i, rfl⟩

/-- `typeuse`. -/
theorem img_use {v : Value} (ih : IHB B v) (h : HasE B "typeuse" v) : Img .use v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_typeuse' h
  simp only [useCases, IntNumeric.findCase] at hf
  split_ifs at hf with h₁ h₂ h₃ <;> obtain ⟨rfl, rfl⟩ := pair_eq hf
  · subst h₁
    obtain ⟨x, rfl⟩ := typeidx_inv ⟨rfl, rfl, rfl⟩ ht
    exact ⟨.idx x, rfl⟩
  · subst h₂
    obtain ⟨d, hd⟩ := img_defPay (sz_case _ _) ih ht
    exact ⟨.dt d, hd⟩
  · subst h₃
    obtain ⟨i, rfl⟩ := n_inv ⟨rfl, rfl, rfl⟩ ht
    exact ⟨.recv i, rfl⟩

/-- One step of `findCase`. -/
theorem findCase_cons_inv {o : MixopS} {t : Typ} {qs : List Param} {p : List Prem}
    {cs : List TypCase} {op : MixopS} {r : Typ × List Prem}
    (h : IntNumeric.findCase (.mk o t qs p :: cs) op = some r) :
    (o = op ∧ r = (t, p)) ∨ IntNumeric.findCase cs op = some r := by
  simp only [IntNumeric.findCase] at h
  split_ifs at h with ho
  · exact .inl ⟨ho, (Option.some.inj h).symm⟩
  · exact .inr h

/-- `findCase` finds nothing in no cases. -/
theorem findCase_nil {op : MixopS} {r : Typ × List Prem} : ¬ IntNumeric.findCase [] op = some r :=
  by simp [IntNumeric.findCase]

/-- `findCase` past a prefix of nullary cases. -/
theorem findCase_nullPrefix : ∀ {ops : List MixopS} {rest : List TypCase} {op : MixopS}
    {r : Typ × List Prem}, IntNumeric.findCase (ops.map nullCase ++ rest) op = some r →
      (op ∈ ops ∧ r = (unitT, [])) ∨ IntNumeric.findCase rest op = some r
  | [], _, _, _, h => .inr h
  | o :: ops, rest, op, r, h => by
    rcases findCase_cons_inv h with ⟨ho, hr⟩ | h'
    · exact .inl ⟨ho ▸ List.mem_cons_self .., hr⟩
    · rcases findCase_nullPrefix h' with ⟨hm, hr⟩ | h''
      · exact .inl ⟨List.mem_cons_of_mem _ hm, hr⟩
      · exact .inr h''

/-- `findCase` in nullary cases only. -/
theorem findCase_nullOnly {ops : List MixopS} {op : MixopS} {r : Typ × List Prem}
    (h : IntNumeric.findCase (ops.map nullCase) op = some r) : op ∈ ops ∧ r = (unitT, []) := by
  rcases findCase_nullPrefix (rest := []) (by rwa [List.append_nil]) with h' | h'
  · exact h'
  · exact absurd h' findCase_nil

/-- A nullary case. -/
theorem img_null {k : TKind} {op : MixopS} {w : Value} {t : Typ} {p : List Prem}
    (hr : (t, p) = (unitT, ([] : List Prem))) (ht : HasTyp (simEnv B) VarEnv.empty t w)
    (hi : Img k (.case op (.tuple []))) : Img k (.case op w) := by
  have hw : w = .tuple [] := tup0_inv ((Prod.mk.inj hr).1 ▸ ht)
  exact hw ▸ hi

/-- The abstract heap types' operators are their images. -/
theorem absOps_img {op : MixopS} (h : op ∈ absOps) :
    ∃ a, Silmaril.SpecTec.Equiv.Validation.absV a = .case op (.tuple []) := by
  simp only [absOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨.any, rfl⟩, ⟨.eq, rfl⟩, ⟨.i31, rfl⟩, ⟨.struct, rfl⟩, ⟨.array, rfl⟩, ⟨.none, rfl⟩,
    ⟨.func, rfl⟩, ⟨.nofunc, rfl⟩, ⟨.exn, rfl⟩, ⟨.noexn, rfl⟩, ⟨.extern, rfl⟩, ⟨.noextern, rfl⟩]

/-- `heaptype`'s nullary cases are images. -/
theorem heapNull_img {op : MixopS} (h : op ∈ absOps ++ ["BOT"]) :
    Img .heap (.case op (.tuple [])) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨a, ha⟩ := absOps_img h
    exact ⟨.abs a, ha.symm⟩
  · rw [List.mem_singleton.1 h]
    exact ⟨.bot, rfl⟩

/-- `_IDX typeidx`. -/
theorem img_idxPay {t : Typ} {p : List Prem} {w : Value}
    (hr : (t, p) = (.varT "typeidx" [], [])) (ht : HasTyp (simEnv B) VarEnv.empty t w) :
    ∃ x : Nat, w = idxV x :=
  typeidx_inv ⟨rfl, rfl, rfl⟩ ((Prod.mk.inj hr).1 ▸ ht)

/-- `REC n`. -/
theorem img_nPay {t : Typ} {p : List Prem} {w : Value}
    (hr : (t, p) = (.varT "n" [], [])) (ht : HasTyp (simEnv B) VarEnv.empty t w) :
    ∃ i : Nat, w = natV i :=
  n_inv ⟨rfl, rfl, rfl⟩ ((Prod.mk.inj hr).1 ▸ ht)

/-- `heaptype`. -/
theorem img_heapS {v : Value} (ih : IHB B v) (h : HasE B "heaptype" v) : Img .heap v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_heaptype' h
  rcases findCase_nullPrefix hf with ⟨hop, hr⟩ | hf₁
  · exact img_null hr ht (heapNull_img hop)
  rcases findCase_cons_inv hf₁ with ⟨rfl, hr⟩ | hf₂
  · obtain ⟨x, hx⟩ := img_idxPay hr ht
    exact ⟨.use (.idx x), by rw [hx]; rfl⟩
  rcases findCase_cons_inv hf₂ with ⟨rfl, hr⟩ | hf₃
  · obtain ⟨d, hd⟩ := img_defPay (sz_case _ _) ih ((Prod.mk.inj hr).1 ▸ ht)
    exact ⟨.use (.dt d), hd⟩
  rcases findCase_cons_inv hf₃ with ⟨rfl, hr⟩ | hf₄
  · obtain ⟨i, hi⟩ := img_nPay hr ht
    exact ⟨.use (.recv i), by rw [hi]; rfl⟩
  · exact absurd hf₄ findCase_nil

/-- `null?`. -/
theorem nullOpt_inv {σ : VarEnv} (hσ : ValsOnly σ) {x : Value}
    (h : HasTyp (simEnv B) σ (.iterT (.varT "null" []) .opt) x) :
    ∃ n, x = Silmaril.SpecTec.Equiv.Validation.nullV n := by
  rcases hasTyp_iterT_opt_iff.1 h with rfl | ⟨y, rfl, hy⟩
  · exact ⟨false, rfl⟩
  · obtain ⟨op, w, t, prems, rfl, hf, ht⟩ :=
      case_of_hasE findTyp_null' (hasE_of_valsOnly hσ hy)
    rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
      obtain rfl := tup0_inv ht
      exact ⟨true, rfl⟩
    · simp [IntNumeric.findCase] at hf

/-- `REF null? heaptype`. -/
theorem img_refPay {v w : Value} (hw : sizeOf w < sizeOf v) (ih : IHB B v)
    (h : HasTyp (simEnv B) VarEnv.empty refPayT w) :
    ∃ r : CRefType, Value.case "REF" w = tyV r := by
  obtain ⟨x, y, rfl, hx, hy⟩ := tup2_inv h
  obtain ⟨n, rfl⟩ := nullOpt_inv ⟨rfl, rfl, rfl⟩ hx
  obtain ⟨hp, rfl⟩ := (ih y ((sz_tuple (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans
    hw)).1 (hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ hy)
  exact ⟨.ref n hp, rfl⟩

/-- The number and vector types' operators are images of value types. -/
theorem numOps_img {op : MixopS} (h : op ∈ numOps) : Img .val (.case op (.tuple [])) := by
  simp only [numOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  exacts [⟨.num (.int .i32), rfl⟩, ⟨.num (.int .i64), rfl⟩, ⟨.num (.float .f32), rfl⟩,
    ⟨.num (.float .f64), rfl⟩, ⟨.vec .v128, rfl⟩]

/-- `storagetype`'s nullary cases after `REF` are images. -/
theorem storageTail_img {op : MixopS} (h : op ∈ ["BOT", "I8", "I16"]) :
    Img .storage (.case op (.tuple [])) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  exacts [⟨.val .botv, rfl⟩, ⟨.pack .i8, rfl⟩, ⟨.pack .i16, rfl⟩]

/-- `valtype`. -/
theorem img_valS {v : Value} (ih : IHB B v) (h : HasE B "valtype" v) : Img .val v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_valtype' h
  rcases findCase_nullPrefix hf with ⟨hop, hr⟩ | hf₁
  · exact img_null hr ht (numOps_img hop)
  rcases findCase_cons_inv hf₁ with ⟨rfl, hr⟩ | hf₂
  · obtain ⟨r, hr'⟩ := img_refPay (sz_case _ _) ih ((Prod.mk.inj hr).1 ▸ ht)
    exact ⟨.refv r, hr'⟩
  obtain ⟨hop, hr⟩ := findCase_nullOnly hf₂
  exact img_null hr ht (by rw [List.mem_singleton.1 hop]; exact ⟨.botv, rfl⟩)

/-- `storagetype`. -/
theorem img_storageS {v : Value} (ih : IHB B v) (h : HasE B "storagetype" v) :
    Img .storage v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_storagetype' h
  rcases findCase_nullPrefix hf with ⟨hop, hr⟩ | hf₁
  · obtain ⟨vt, hvt⟩ := numOps_img hop
    exact img_null hr ht ⟨.val vt, hvt⟩
  rcases findCase_cons_inv hf₁ with ⟨rfl, hr⟩ | hf₂
  · obtain ⟨r, hr'⟩ := img_refPay (sz_case _ _) ih ((Prod.mk.inj hr).1 ▸ ht)
    exact ⟨.val (.refv r), hr'⟩
  obtain ⟨hop, hr⟩ := findCase_nullOnly hf₂
  exact img_null hr ht (storageTail_img hop)

/-- `mut?`. -/
theorem mutOpt_inv {σ : VarEnv} (hσ : ValsOnly σ) {x : Value}
    (h : HasTyp (simEnv B) σ (.iterT (.varT "mut" []) .opt) x) :
    ∃ m, x = Silmaril.SpecTec.Equiv.Validation.mutV m := by
  rcases hasTyp_iterT_opt_iff.1 h with rfl | ⟨y, rfl, hy⟩
  · exact ⟨.const, rfl⟩
  · obtain ⟨op, w, t, prems, rfl, hf, ht⟩ :=
      case_of_hasE ConfigOk.findTyp_mut (hasE_of_valsOnly hσ hy)
    rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
      obtain rfl := tup0_inv ht
      exact ⟨.var, rfl⟩
    · simp [IntNumeric.findCase] at hf

/-- `final?`. -/
theorem finalOpt_inv {σ : VarEnv} (hσ : ValsOnly σ) {x : Value}
    (h : HasTyp (simEnv B) σ (.iterT (.varT "final" []) .opt) x) :
    ∃ b, x = Silmaril.SpecTec.Equiv.Validation.finalV b := by
  rcases hasTyp_iterT_opt_iff.1 h with rfl | ⟨y, rfl, hy⟩
  · exact ⟨false, rfl⟩
  · obtain ⟨op, w, t, prems, rfl, hf, ht⟩ :=
      case_of_hasE findTyp_final' (hasE_of_valsOnly hσ hy)
    rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
      obtain rfl := tup0_inv ht
      exact ⟨true, rfl⟩
    · simp [IntNumeric.findCase] at hf

/-- `fieldtype`. -/
theorem img_fieldS {v : Value} (ih : IHB B v) (h : HasE B "fieldtype" v) : Img .field v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_fieldtype' h
  unfold fieldCases at hf
  rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
  · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
    obtain ⟨x, y, rfl, hx, hy⟩ := tup2_inv ht
    obtain ⟨m, rfl⟩ := mutOpt_inv ⟨rfl, rfl, rfl⟩ hx
    obtain ⟨st, rfl⟩ := (ih y ((sz_tuple (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans
      (sz_case _ _))).2.2.2.2.2.2.1 (hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ hy)
    exact ⟨.field m st, rfl⟩
  · simp [IntNumeric.findCase] at hf

/-- A `list(y)` payload of images. -/
theorem img_listPay {k : TKind} {y : IL.Id} (hy : y ≠ "X") {σ : VarEnv} (hσ : ValsOnly σ)
    {op : MixopS} {w : Value}
    (hP : ∀ u, sizeOf u < sizeOf (Value.case op w) → HasE B y u → Img k u)
    (h : HasTyp (simEnv B) σ (.varT "list" [.typA (.varT y [])]) w) :
    ∃ ts : Ty (.list k), w = .case "%" (.tuple [tyV ts]) := by
  obtain ⟨l, rfl, -, hall⟩ := listT_inv hσ hy h
  obtain ⟨ts, hts⟩ := img_list (k := k) fun u hu => hP u (sz_pct hu) (hall u hu)
  exact ⟨ts, by rw [← hts]⟩

/-- `resulttype`, at a typed payload component. -/
theorem img_results {σ : VarEnv} (hσ : ValsOnly σ) {v x : Value} (hx : sizeOf x < sizeOf v)
    (ih : IHB B v) (h : HasTyp (simEnv B) σ (.varT "resulttype" []) x) :
    ∃ ts : Ty (.list .val), x = .case "%" (.tuple [tyV ts]) := by
  have h' := ConfigOk.hasTyp_of_closedAlias hσ Round5.Pos.findTyp_resulttype h
  obtain ⟨l, rfl, -, hall⟩ := listT_inv ⟨rfl, rfl, rfl⟩ (by decide) h'
  have hsz : ∀ u ∈ l, sizeOf u < sizeOf v := fun u hu =>
    ((sz_list hu).trans ((sz_tuple (List.mem_singleton_self _)).trans (sz_case _ _))).trans hx
  obtain ⟨ts, hts⟩ := img_list (k := .val) fun u hu => (ih u (hsz u hu)).2.2.2.2.2.2.2 (hall u hu)
  exact ⟨ts, by rw [← hts]⟩

/-- `FUNC resulttype -> resulttype`. -/
theorem img_funcPay {v w : Value} (hw : sizeOf w < sizeOf v) (ih : IHB B v)
    (h : HasTyp (simEnv B) VarEnv.empty (.tupT [.mk "resulttype" (.varT "resulttype" []),
      .mk "resulttype" (.varT "resulttype" [])]) w) :
    ∃ c : CCompType, Value.case "FUNC%->%" w = tyV c := by
  obtain ⟨x, y, rfl, hx, hy⟩ := tup2_inv h
  obtain ⟨ps, rfl⟩ := img_results ⟨rfl, rfl, rfl⟩
    ((sz_tuple (List.mem_cons_self ..)).trans hw) ih hx
  obtain ⟨rs, rfl⟩ := img_results ⟨rfl, rfl, rfl⟩
    ((sz_tuple (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hw) ih hy
  exact ⟨.func ps rs, rfl⟩

/-- `comptype`. -/
theorem img_compS {v : Value} (ih : IHB B v) (h : HasE B "comptype" v) : Img .comp v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_comptype' h
  unfold compCases at hf
  rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf₁
  · obtain ⟨ts, rfl⟩ := img_listPay (k := .field) (by decide) ⟨rfl, rfl, rfl⟩
      (fun u hu hu' => (ih u hu).2.2.2.2.2.1 hu') ((Prod.mk.inj hr).1 ▸ ht)
    exact ⟨.struct ts, rfl⟩
  rcases findCase_cons_inv hf₁ with ⟨rfl, hr⟩ | hf₂
  · obtain ⟨f, rfl⟩ := (ih w (sz_case _ _)).2.2.2.2.2.1
      ((Prod.mk.inj hr).1 ▸ ht : HasTyp (simEnv B) VarEnv.empty (.varT "fieldtype" []) w)
    exact ⟨.array f, rfl⟩
  rcases findCase_cons_inv hf₂ with ⟨rfl, hr⟩ | hf₃
  · exact img_funcPay (sz_case _ _) ih ((Prod.mk.inj hr).1 ▸ ht)
  · exact absurd hf₃ findCase_nil

/-- `subtype`. -/
theorem img_subS {v : Value} (ih : IHB B v) (h : HasE B "subtype" v) : Img .sub v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_subtype' h
  unfold subCases at hf
  rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
  · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
    obtain ⟨x, y, z, rfl, hx, hy, hz⟩ := tup3_inv ht
    obtain ⟨b, rfl⟩ := finalOpt_inv ⟨rfl, rfl, rfl⟩ hx
    obtain ⟨l, rfl, hl⟩ := hasTyp_iterT_list_iff.1 hy
    have hsy : sizeOf (Value.list l) < sizeOf (Value.case "SUB" (.tuple [Silmaril.SpecTec.Equiv.Validation.finalV b, .list l, z])) :=
      (sz_tuple (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans (sz_case _ _)
    obtain ⟨sups, hsups⟩ := img_list (k := .use) fun u hu =>
      (ih u ((sz_list hu).trans hsy)).2.1
        (hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ (hasTypList_iff.1 hl u hu))
    obtain ⟨ct, rfl⟩ := (ih z ((sz_tuple (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))).trans (sz_case _ _))).2.2.2.2.1
        (hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ hz)
    exact ⟨.sub b sups ct, by rw [hsups]; rfl⟩
  · simp [IntNumeric.findCase] at hf

/-- `rectype`. -/
theorem img_recS {v : Value} (ih : IHB B v) (h : HasE B "rectype" v) : Img .group v := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_rectype' h
  unfold recCases at hf
  rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
  · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
    obtain ⟨ts, rfl⟩ := img_listPay (k := .sub) (by decide)
      ⟨rfl, rfl, rfl⟩ (fun u hu hu' => (ih u hu).2.2.2.1 hu') ht
    exact ⟨.group ts, rfl⟩
  · simp [IntNumeric.findCase] at hf

/-- **Typed type values are images**, by strong induction on their size. -/
theorem img_all : ∀ (n : Nat) (v : Value), sizeOf v < n → ImgAll B v
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, v, hv => by
    have ih : IHB B v := fun u hu => img_all n u (by omega)
    exact ⟨img_heapS ih, img_use ih, img_recS ih, img_subS ih, img_compS ih, img_fieldS ih,
      img_storageS ih, img_valS ih⟩

/-- **A typed `heaptype` value is the image of a Core heap type.** -/
theorem img_heap {v : Value} (h : HasE B "heaptype" v) : ∃ hp : CHeapType, v = tyV hp :=
  (img_all _ v (Nat.lt_succ_self _)).1 h

/-- `absheaptype`'s cases. -/
def absCases : List TypCase := (absOps ++ ["BOT"]).map nullCase

set_option maxRecDepth 100000 in
theorem findTyp_absheaptype' : (simEnv B).findTyp? "absheaptype" =
    some ([], [.instD [] [] (.variantT absCases)]) := rfl

/-- **A typed `absheaptype` value is an abstract heap type or `BOT`.** -/
theorem abs_inv {v : Value} (h : HasE B "absheaptype" v) :
    (∃ a, v = Silmaril.SpecTec.Equiv.Validation.absV a) ∨ v = .case "BOT" (.tuple []) := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_absheaptype' h
  obtain ⟨hop, hr⟩ := findCase_nullOnly hf
  have hw : w = .tuple [] := tup0_inv ((Prod.mk.inj hr).1 ▸ ht)
  rw [hw]
  rcases List.mem_append.1 hop with h | h
  · obtain ⟨a, ha⟩ := absOps_img h
    exact .inl ⟨a, ha.symm⟩
  · exact .inr (by rw [List.mem_singleton.1 h])

/-- **A typed `deftype` value is the image of a Core defined type.** -/
theorem img_def {v : Value} (h : HasE B "deftype" v) : ∃ d : DefType, v = tyV d := by
  obtain ⟨op, w, t, prems, rfl, hf, ht⟩ := case_of_hasE findTyp_deftype' h
  unfold defCases at hf
  rcases findCase_cons_inv hf with ⟨rfl, hr⟩ | hf
  · obtain ⟨rfl, -⟩ := Prod.mk.inj hr.symm
    exact img_defPay (v := .case "_DEF" w) (sz_case _ _)
      (fun u _ => img_all _ u (Nat.lt_succ_self _)) ht
  · simp [IntNumeric.findCase] at hf

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
