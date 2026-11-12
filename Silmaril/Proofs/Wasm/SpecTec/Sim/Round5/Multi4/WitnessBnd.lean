module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# Round 5, track multi (pass 4): typed witnesses have bounded code

`Int2.WitnessBnd B hn` holds for every `B` and encoding (`witnessBnd`). A typed `d ≈ c` differs
from `c` only in its `CALL_REF` annotations, and a typed `CALL_REF dt` has a bounded `dt`:

* `tyBnd_of_tyI`: the converse of `tyT_tyV`. If the image `tyV t` of a runtime type
  inhabits one of the IL types of its sort (`TyI`), then `t` is within SpecTec's bounds
  (`Round4.tyBnd t`). By induction on Core's `Ty`, inverting the type grammar: `_IDX x` through
  `typeidx` (`ConfigOk.lt_of_hasTyp_typeuse_idx`, `ConfigOk.lt_of_hasTyp_typeidx`), and every
  `list(X)` position through its premise `|X*| < 2^32` (`listT_inv`).
* `tyBnd_of_callRef`: so the annotation of a typed `CALL_REF` is bounded.
* `codeBnd_of_eq`: `AdminsBnd` carries over along `CodeEq` to a typed code sequence.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)

variable {B : Builtins}

/-- `v` inhabits the closed named type `x`, in the empty scope. -/
abbrev HasE (B : Builtins) (x : IL.Id) (v : Value) : Prop :=
  HasTyp (simEnv B) VarEnv.empty (.varT x []) v

/-! ## Scopes -/

/-- A closed named type, typed in a scope that does not bind it, is typed in the empty
scope. -/
theorem hasE_of_global {σ : VarEnv} {y : IL.Id} {u : Value} (hσ : localTyp? σ y [] = none)
    (h : HasTyp (simEnv B) σ (.varT y []) u) : HasE B y u := by
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff hσ).1 h
  have hws : ws = [] := Equiv.Validation.evalArgs_nil_iff.1 hargs
  exact (hasTyp_varT_global_iff rfl).2 ⟨td, [], htd, Equiv.evalArgs_nil, hws ▸ hi⟩

/-- The same, from a term-only scope. -/
theorem hasE_of_valsOnly {σ : VarEnv} (hσ : ValsOnly σ) {y : IL.Id} {u : Value}
    (h : HasTyp (simEnv B) σ (.varT y []) u) : HasE B y u :=
  IntNumeric.hasTyp_varT_nil_congr hσ ⟨rfl, rfl, rfl⟩ h

/-- The payload of a case of a closed variant. -/
theorem payload {x op : IL.Id} {cs : List TypCase} {t : Typ} {prems : List Prem} {w : Value}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (hf : IntNumeric.findCase cs op = some (t, prems)) (h : HasE B x (.case op w)) :
    HasTyp (simEnv B) VarEnv.empty t w :=
  IntNumeric.hasTyp_of_hasTypCase (Typing.hasTypCase_of_closedVariant htd h) hf

/-- The second component of a typed pair, in the empty scope. -/
theorem pair_snd {a b y : IL.Id} {τ₁ : Typ} {u v : Value}
    (h : HasTyp (simEnv B) VarEnv.empty (.tupT [.mk a τ₁, .mk b (.varT y [])]) (.tuple [u, v])) :
    HasE B y v :=
  hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ (Typing.hasTyp_pair_inv h).2

/-! ## `list(X)`, inverted -/

/-- `list(X)`'s premise is false from `2^32` elements on. -/
theorem evalExp_listPrem_false {σ : VarEnv} {l : List Value} (hl : 2 ^ 32 ≤ l.length) :
    EvalExp (simEnv B) (σ.bindVal "X*" (.list l)) Pos.listPrem (.bool false) := by
  have hit : EvalExp (simEnv B) (σ.bindVal "X*" (.list l))
      (.iterE (.varE "X") (.mk .list [.mk "X" (.varE "X*")])) (.list (l.map id)) :=
    evalExp_iterMap (by simp [Equiv.Execution.findVal?_bindVal_lit])
      (fun w _ => evalExp_varE_iff.2
        (by simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind]))
  rw [List.map_id] at hit
  refine evalExp_cmpE_iff.2 ⟨_, .num (.natN (2 ^ 32)), evalExp_lenE_iff.2 ⟨_, hit, rfl⟩,
    evalExp_twoPowE (evalExp_numE_iff.2 rfl), ?_⟩
  have hd : decide (l.length < 2 ^ 32) = false := decide_eq_false (Nat.not_lt.2 hl)
  simp only [cmpValues, Num.cmp, hd]
  rfl

/-- The scope `list(y)`'s case is typed in. -/
abbrev listScope (y : IL.Id) : VarEnv := VarEnv.empty.bindTyp "X" (.varT y [])

/-- The instance of `list(y)`, after its argument pattern `X` matched `y`. -/
theorem hasTypDef_of_listT {σ : VarEnv} (hσ : ValsOnly σ) {y : IL.Id} {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "list" [.typA (.varT y [])]) v) :
    HasTypDef (simEnv B) (listScope y) (.variantT [.mk "%"
      (.tupT [.mk "X*" (.iterT (.varT "X" []) .list)]) [] [.ifPr Pos.listPrem]]) v := by
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  have htd' : td = _ := (Option.some.inj ((Pos.findTyp_list B).symm.trans htd)).symm
  have hargs0 : EvalArgs (simEnv B) σ [.typA (.varT y [])] [.typ (.varT y [])] :=
    ⟨2, by simp [evalArgs, evalArg, resolveTyp, VarEnv.findTyp?, hσ.1]⟩
  have hws : ws = _ := Equiv.ExecNumeric.evalArgs_unique hargs hargs0
  have hm : MatchArgs (simEnv B) VarEnv.empty [.typA (.varT "X" [])] [.typ (.varT y [])]
      (listScope y) :=
    ⟨2, by simp [matchArgs, matchArg, matchTypV, Pos.memTyp_X, VarEnv.findTyp?, VarEnv.empty,
      Map.find?, Map.empty]; rfl⟩
  rw [htd', hws] at hi
  rcases hasTypInsts_cons_inv hi with ⟨σ', ⟨k, hk⟩, hd⟩ | hrest
  · exact IntNumeric.matchArgs_det hm hk ▸ hd
  · exact absurd hrest not_hasTypInsts_nil

/-- An element of `list(y)`'s payload is a `y`. -/
theorem elem_of_listScope {y : IL.Id} (hy : y ≠ "X") {u : Value}
    (h : HasTyp (simEnv B) (listScope y) (.varT "X" []) u) : HasE B y u := by
  have hl : localTyp? (listScope y) "X" [] = some (.varT y []) := by
    simp [localTyp?, VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, VarEnv.empty]
  have hl' : localTyp? (listScope y) y [] = none := by
    simp [localTyp?, VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, Map.find?, VarEnv.empty,
      Map.empty, Ne.symm hy]
  exact hasE_of_global hl' ((hasTyp_varT_local_iff hl).1 h)

/-- **`list(y)`, inverted**: fewer than `2^32` elements, each a `y`. -/
theorem listT_inv {σ : VarEnv} (hσ : ValsOnly σ) {y : IL.Id} (hy : y ≠ "X") {v : Value}
    (h : HasTyp (simEnv B) σ (.varT "list" [.typA (.varT y [])]) v) :
    ∃ l, v = .case "%" (.tuple [.list l]) ∧ l.length < 2 ^ 32 ∧ ∀ u ∈ l, HasE B y u := by
  obtain ⟨op, w, hv, hc⟩ := hasTypDef_variantT_iff.1 (hasTypDef_of_listT hσ h)
  by_cases ho : "%" = op
  · obtain ⟨ht, hp⟩ := (hasTypCase_cons_hit_iff ho).1 hc
    obtain ⟨vs, hw, htup⟩ := hasTyp_tupT_iff.1 ht
    obtain ⟨x, vs', hvs, hx, hrest⟩ := hasTypTup_cons_iff.1 htup
    have hvs' : vs' = [] := hasTypTup_nil_iff.1 hrest
    obtain ⟨l, hxl, hl⟩ := hasTyp_iterT_list_iff.1 hx
    have hw' : w = .tuple [.list l] := by rw [hw, hvs, hvs', hxl]
    have htrue : EvalExp (simEnv B) ((listScope y).bindVal "X*" (.list l)) Pos.listPrem
        (.bool true) := ConfigOk.evalExp_of_premsOk_if (by rw [hw'] at hp; exact hp)
    refine ⟨l, by rw [hv, ← ho, hw'], Nat.lt_of_not_le fun hn => ?_, fun u hu =>
      elem_of_listScope hy (hasTypList_iff.1 hl u hu)⟩
    cases htrue.unique (evalExp_listPrem_false hn)
  · exact absurd ((hasTypCase_cons_miss_iff ho).1 hc) not_hasTypCase_nil

/-! ## The type grammar, inverted -/

/-- The IL types at which the image of a runtime type of sort `k` occurs: `TyT`, as
a disjunction. -/
def TyI (B : Builtins) : TKind → Value → Prop
  | .use, v => HasE B "typeuse" v ∨ HasE B "heaptype" v
  | .heap, v => HasE B "heaptype" v
  | .ref, v => HasE B "reftype" v ∨ HasE B "valtype" v ∨ HasE B "storagetype" v
  | .val, v => HasE B "valtype" v ∨ HasE B "storagetype" v
  | .storage, v => HasE B "storagetype" v
  | .field, v => HasE B "fieldtype" v
  | .comp, v => HasE B "comptype" v
  | .sub, v => HasE B "subtype" v
  | .group, v => HasE B "rectype" v
  | .def, v => HasE B "deftype" v ∨ HasE B "typeuse" v ∨ HasE B "heaptype" v
  | .list k, v => ∃ l, v = .list l ∧ ∀ u ∈ l, TyI B k u

/-- A sequence's image, typed elementwise. -/
theorem tyI_list {k : TKind} {t : Ty (.list k)} (h : ∀ u ∈ t.toList.map tyV, TyI B k u) :
    TyI B (.list k) (tyV t) :=
  ⟨_, Equiv.Validation.tyV_list t, h⟩

/-- A sequence's elements, read off `TyI`. -/
theorem tyI_elems {k : TKind} {t : Ty (.list k)} (h : TyI B (.list k) (tyV t)) :
    ∀ u ∈ t.toList.map tyV, TyI B k u := by
  obtain ⟨l, hl, hall⟩ := h
  have e : t.toList.map tyV = l := Value.list.inj ((Equiv.Validation.tyV_list t).symm.trans hl)
  exact e ▸ hall

/-- `list(y)` at a sequence's image: its length and elements. -/
theorem listT_tyV {y : IL.Id} (hy : y ≠ "X") {k : TKind} {t : Ty (.list k)}
    (h : HasTyp (simEnv B) VarEnv.empty (.varT "list" [.typA (.varT y [])])
      (.case "%" (.tuple [tyV t]))) :
    t.toList.length < 2 ^ 32 ∧ ∀ u ∈ t.toList.map tyV, HasE B y u := by
  obtain ⟨l, hl, hlen, hall⟩ := listT_inv ⟨rfl, rfl, rfl⟩ hy h
  have e : tyV t = .list l := by simpa using hl
  have e' : t.toList.map tyV = l := Value.list.inj ((Equiv.Validation.tyV_list t).symm.trans e)
  exact ⟨by simpa [← e'] using hlen, e' ▸ hall⟩

/-- `_IDX x` occurs typed only below `2^32`. -/
theorem tyBnd_idx {x : Nat} (h : TyI B .use (tyV (Ty.idx x))) :
    Round4.tyBnd (Ty.idx x) = true := by
  have hx : x < 2 ^ 32 := by
    rcases h with h | h
    · exact ConfigOk.lt_of_hasTyp_typeuse_idx h
    · exact ConfigOk.lt_of_hasTyp_typeidx ⟨rfl, rfl, rfl⟩
        (payload Typing.findTyp_heaptype (t := .varT "typeidx" []) (prems := []) rfl h)
  simpa [Round4.tyBnd, Round4.bnd32] using hx

/-- `_DEF rectype n`: its rectype. -/
theorem rectype_of_defn {g : Ty .group} {i : Nat} (h : TyI B .def (tyV (Ty.defn g i))) :
    HasE B "rectype" (tyV g) := by
  have hp : HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "rectype" (.varT "rectype" []), .mk "n" (.varT "n" [])])
      (.tuple [tyV g, Equiv.Validation.natV i]) := by
    rcases h with h | h | h
    · exact payload Pos.findTyp_deftype rfl h
    · exact payload Typing.findTyp_typeuse rfl h
    · exact payload Typing.findTyp_heaptype rfl h
  exact (Typing.hasTyp_pair_inv hp).1

/-- `REF null? heaptype`: its heap type. -/
theorem heap_of_ref {n : Bool} {hp : Ty .heap} (h : TyI B .ref (tyV (Ty.ref n hp))) :
    HasE B "heaptype" (tyV hp) := by
  have hq : HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "null?" (.iterT (.varT "null" []) .opt), .mk "heaptype" (.varT "heaptype" [])])
      (.tuple [Equiv.Validation.nullV n, tyV hp]) := by
    rcases h with h | h | h
    · exact payload Pos.findTyp_reftype rfl h
    · exact payload Typing.findTyp_valtype rfl h
    · exact payload Pos.findTyp_storagetype rfl h
  exact pair_snd hq

/-- `mut? storagetype`: its storage type. -/
theorem storage_of_field {m : Mutability} {st : Ty .storage}
    (h : TyI B .field (tyV (Ty.field m st))) : HasE B "storagetype" (tyV st) :=
  pair_snd (payload Pos.findTyp_fieldtype
    (t := .tupT [.mk "mut?" (.iterT (.varT "mut" []) .opt), .mk "storagetype" (.varT "storagetype" [])])
    (prems := []) rfl h)

/-- `STRUCT list(fieldtype)`: its length and fields. -/
theorem fields_of_struct {fs : Ty (.list .field)} (h : TyI B .comp (tyV (Ty.struct fs))) :
    fs.toList.length < 2 ^ 32 ∧ ∀ u ∈ fs.toList.map tyV, HasE B "fieldtype" u := by
  have hv : tyV (Ty.struct fs) = .case "STRUCT" (.case "%" (.tuple [tyV fs])) := rfl
  exact listT_tyV (by decide) (payload Pos.findTyp_comptype
    (t := .varT "list" [.typA (.varT "fieldtype" [])]) (prems := []) rfl (hv ▸ h))

/-- `ARRAY fieldtype`: its field. -/
theorem field_of_array {f : Ty .field} (h : TyI B .comp (tyV (Ty.array f))) :
    HasE B "fieldtype" (tyV f) :=
  payload Pos.findTyp_comptype (t := .varT "fieldtype" []) (prems := []) rfl h

/-- `resulttype`: its length and value types. -/
theorem resulttype_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {ts : Ty (.list .val)}
    (h : HasTyp (simEnv B) ρ (.varT "resulttype" []) (.case "%" (.tuple [tyV ts]))) :
    ts.toList.length < 2 ^ 32 ∧ ∀ u ∈ ts.toList.map tyV, HasE B "valtype" u :=
  listT_tyV (by decide) (ConfigOk.hasTyp_of_closedAlias hρ Pos.findTyp_resulttype h)

/-- `FUNC resulttype -> resulttype`: its two result types. -/
theorem results_of_func {ps rs : Ty (.list .val)} (h : TyI B .comp (tyV (Ty.func ps rs))) :
    (ps.toList.length < 2 ^ 32 ∧ ∀ u ∈ ps.toList.map tyV, HasE B "valtype" u) ∧
      (rs.toList.length < 2 ^ 32 ∧ ∀ u ∈ rs.toList.map tyV, HasE B "valtype" u) := by
  have hv : tyV (Ty.func ps rs) = .case "FUNC%->%" (.tuple
      [.case "%" (.tuple [tyV ps]), .case "%" (.tuple [tyV rs])]) := rfl
  have hp := Typing.hasTyp_pair_inv (payload Pos.findTyp_comptype
    (t := .tupT [.mk "resulttype" (.varT "resulttype" []),
      .mk "resulttype" (.varT "resulttype" [])]) (prems := []) rfl (hv ▸ h))
  exact ⟨resulttype_inv ⟨rfl, rfl, rfl⟩ hp.1, resulttype_inv ⟨rfl, rfl, rfl⟩ hp.2⟩

/-- `SUB final? typeuse* comptype`: its supertypes and body. -/
theorem parts_of_sub {fin : Bool} {sups : Ty (.list .use)} {body : Ty .comp}
    (h : TyI B .sub (tyV (Ty.sub fin sups body))) :
    (∀ u ∈ sups.toList.map tyV, HasE B "typeuse" u) ∧ HasE B "comptype" (tyV body) := by
  have hp := ConfigOk.hasTyp_triple_inv (payload Pos.findTyp_subtype
    (t := .tupT [.mk "final?" (.iterT (.varT "final" []) .opt),
      .mk "typeuse*" (.iterT (.varT "typeuse" []) .list), .mk "comptype" (.varT "comptype" [])])
    (prems := []) rfl h)
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 hp.2.1
  have e : sups.toList.map tyV = l := Value.list.inj ((Equiv.Validation.tyV_list sups).symm.trans hl)
  exact ⟨fun u hu => hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ (hasTypList_iff.1 hall u (e ▸ hu)),
    hasE_of_valsOnly ⟨rfl, rfl, rfl⟩ hp.2.2⟩

/-- `REC list(subtype)`: its length and members. -/
theorem subs_of_group {subs : Ty (.list .sub)} (h : TyI B .group (tyV (Ty.group subs))) :
    subs.toList.length < 2 ^ 32 ∧ ∀ u ∈ subs.toList.map tyV, HasE B "subtype" u := by
  have hv : tyV (Ty.group subs) = .case "REC" (.case "%" (.tuple [tyV subs])) := rfl
  exact listT_tyV (by decide) (payload Pos.findTyp_rectype
    (t := .varT "list" [.typA (.varT "subtype" [])]) (prems := []) rfl (hv ▸ h))

/-- `cons`, read off `TyI`. -/
theorem tyI_cons {k : TKind} {a : Ty k} {l : Ty (.list k)} (h : TyI B (.list k) (tyV (.cons a l))) :
    TyI B k (tyV a) ∧ TyI B (.list k) (tyV l) := by
  have hall := tyI_elems h
  simp only [Ty.toList_cons, List.map_cons, List.mem_cons, forall_eq_or_imp] at hall
  exact ⟨hall.1, tyI_list hall.2⟩

set_option maxRecDepth 100000 in
/-- **A typed runtime type is bounded**: the converse of `tyT_tyV`. -/
theorem tyBnd_of_tyI : ∀ {k : TKind} (t : Ty k), TyI B k (tyV t) → Round4.tyBnd t = true := by
  intro k t
  induction t with
  | nil => exact fun _ => rfl
  | cons a l iha ihl =>
    exact fun h => Pos.tyBnd_cons.2 ⟨iha (tyI_cons h).1, ihl (tyI_cons h).2⟩
  | idx x => exact tyBnd_idx
  | recv i => exact fun _ => rfl
  | dt d ih => exact fun h => ih (h.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h)))
  | defn g i ih => exact fun h => ih (rectype_of_defn h)
  | abs a => exact fun _ => rfl
  | bot => exact fun _ => rfl
  | use u ih => exact fun h => ih (.inr h)
  | ref n hp ih => exact fun h => ih (heap_of_ref h)
  | num t => exact fun _ => rfl
  | vec t => exact fun _ => rfl
  | refv r ih => exact fun h => ih (.inr h)
  | botv => exact fun _ => rfl
  | val t ih => exact fun h => ih (.inr h)
  | pack p => exact fun _ => rfl
  | field m st ih => exact fun h => ih (storage_of_field h)
  | struct fs ih =>
    exact fun h => Pos.tyBnd_struct.2 ⟨(fields_of_struct h).1,
      ih (tyI_list (k := .field) (fields_of_struct h).2)⟩
  | array f ih => exact fun h => ih (field_of_array h)
  | func ps rs ihp ihr =>
    exact fun h => Pos.tyBnd_func.2 ⟨⟨(results_of_func h).1.1, (results_of_func h).2.1⟩,
      ihp (tyI_list fun u hu => .inl ((results_of_func h).1.2 u hu)),
      ihr (tyI_list fun u hu => .inl ((results_of_func h).2.2 u hu))⟩
  | sub fin sups body ihs ihb =>
    exact fun h => Pos.tyBnd_sub.2 ⟨ihs (tyI_list fun u hu => .inl ((parts_of_sub h).1 u hu)),
      ihb (parts_of_sub h).2⟩
  | group subs ih =>
    exact fun h => Pos.tyBnd_group.2 ⟨(subs_of_group h).1,
      ih (tyI_list (k := .sub) (subs_of_group h).2)⟩

/-! ## Witnesses -/

set_option maxRecDepth 100000 in
/-- **The annotation of a typed `CALL_REF` is bounded.** -/
theorem tyBnd_of_callRef {d : DefType}
    (h : TypedV (simEnv B) instrT (adminToV (.callRefType d))) : Round4.tyBnd d = true :=
  tyBnd_of_tyI d (.inr (.inl (payload (IntNumeric.findTyp_instr' B) (t := .varT "typeuse" [])
    (prems := []) rfl (h _ ⟨rfl, rfl, rfl⟩))))

section Witness

variable {H : Type} {hn : H → String}

mutual
/-- `AdminBnd` carries over along `AdminEq` to a typed instruction. -/
theorem adminBnd_of_eq (T : TypingFacts (simEnv B) hn) :
    ∀ {a b : Admin}, Bwd.AdminEq a b → Round4.AdminBnd a →
      TypedV (simEnv B) instrT (adminToV b) → Round4.AdminBnd b
  | _, _, .refl _, h, _ => h
  | _, _, .call _ hb, _, ht => by
    rcases Bwd.isCallRef_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · exact rfl
    · exact tyBnd_of_callRef ht
  | _, _, .label h₁, h, ht =>
    ⟨h.1, codeBnd_of_eq T h₁ h.2 (T.label _ _ _ (typedV_list_single.2 ht)).2.2⟩
  | _, _, .handler h₁, h, ht =>
    codeBnd_of_eq T h₁ h (T.handler _ _ _ (typedV_list_single.2 ht)).2.2
  | _, _, .frame h₁, h, ht =>
    ⟨h.1, codeBnd_of_eq T h₁ h.2 (T.frame _ _ _ (typedV_list_single.2 ht)).2.2⟩

/-- `AdminsBnd` carries over along `CodeEq` to typed code. -/
theorem codeBnd_of_eq (T : TypingFacts (simEnv B) hn) :
    ∀ {l j : List Admin}, Bwd.CodeEq l j → Round4.AdminsBnd l →
      TypedV (simEnv B) instrsT (.list (adminsToV j)) → Round4.AdminsBnd j
  | _, _, .nil, h, _ => h
  | _, _, .cons ha hl, h, ht => by
    rw [adminsToV_eq_map, List.map_cons, typedV_list_cons_iff, ← adminsToV_eq_map] at ht
    exact ⟨adminBnd_of_eq T ha h.1 ht.1, codeBnd_of_eq T hl h.2 ht.2⟩
end

end Witness

/-- **Typed witnesses have bounded code**, for every `B` and encoding: `Round5.Int2.WitnessBnd`
holds. -/
theorem witnessBnd {H : Type} (B : Builtins) (hn : H → String) : Int2.WitnessBnd B hn :=
  fun _ d hb he ht =>
    codeBnd_of_eq (Typing.typingFacts_simEnv B hn) he.2.2 hb
      (((Typing.typingFacts_simEnv B hn).config d).1 ht).2

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
