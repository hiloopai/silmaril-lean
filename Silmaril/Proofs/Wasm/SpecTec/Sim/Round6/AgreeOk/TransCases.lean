module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.TransAux

/-!
# Round 6: the cases of the transcription

The motives `OkD` (validation) and `SubD` (subtyping) of the transcription of canonical
derivations, and one lemma per case that is more than a direct application of a rule lemma:
sequences (`okD_cons`, `subD_cons`), `STRUCT` and `FUNC` validity, `Resulttype_sub` and
`Comptype_sub/struct`, `func` from the pointwise readings of their sequences, and `Deftype_ok`
in the group's own context.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.AgreeSub (CtxT)
open Round4 (tyBnd)

variable {B : Builtins}

/-! ## The motives -/

/-- **What a canonical validity derivation is read as**, at each sort, in the context `c`:
`Heaptype_ok`, …, `Comptype_ok`, and pointwise on sequences. -/
def OkD (B : Builtins) (O : ElseI) (c : Value) : (k : TKind) → Ty k → Prop
  | .heap, t => DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .use, t => DDerivesB (simEnv B) O "Typeuse_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .def, t => DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .ref, t => DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .val, t => DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .storage, t => DDerivesB (simEnv B) O "Storagetype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .field, t => DDerivesB (simEnv B) O "Fieldtype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .comp, t => DDerivesB (simEnv B) O "Comptype_ok" "%|-%:OK" [] (.tuple [c, tyV t])
  | .list k, t => ∀ a ∈ t.toList, OkD B O c k a
  | .sub, _ => True
  | .group, _ => True

/-- **What a canonical subtyping derivation is read as**, at each sort, in the context `c`:
`Heaptype_sub`, …, `Deftype_sub`, and pointwise on sequences. -/
def SubD (B : Builtins) (O : ElseI) (c : Value) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => DDerivesB (simEnv B) O "Heaptype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .ref, a, b => DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .val, a, b => DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .storage, a, b =>
    DDerivesB (simEnv B) O "Storagetype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .field, a, b => DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .comp, a, b => DDerivesB (simEnv B) O "Comptype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .def, a, b => DDerivesB (simEnv B) O "Deftype_sub" "%|-%<:%" [] (.tuple [c, tyV a, tyV b])
  | .list k, a, b => List.Forall₂ (SubD B O c k) a.toList b.toList
  | .use, _, _ => True
  | .sub, _, _ => True
  | .group, _, _ => True

/-! ## Sequences -/

theorem okD_nil {O : ElseI} {c : Value} {k : TKind} : OkD B O c (.list k) .nil :=
  fun _ h => absurd h List.not_mem_nil

theorem okD_cons {O : ElseI} {c : Value} {k : TKind} {a : Ty k} {l : Ty (.list k)}
    (ha : OkD B O c k a) (hl : OkD B O c (.list k) l) : OkD B O c (.list k) (.cons a l) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hl x hx

theorem subD_nil {O : ElseI} {c : Value} {k : TKind} : SubD B O c (.list k) .nil .nil :=
  List.Forall₂.nil

theorem subD_cons {O : ElseI} {c : Value} {k : TKind} {a b : Ty k} {l l' : Ty (.list k)}
    (h : SubD B O c k a b) (hl : SubD B O c (.list k) l l') :
    SubD B O c (.list k) (.cons a l) (.cons b l') :=
  List.Forall₂.cons h hl

/-! ## Images of composite types -/

theorem tyV_struct_eq (fs : Ty (.list .field)) :
    tyV (Ty.struct fs) = .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
  rw [tyV, tyV_list]
  rfl

theorem tyV_func_eq (ps rs : Ty (.list .val)) :
    tyV (Ty.func ps rs) = .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list (ps.toList.map tyV)]),
      .case "%" (.tuple [.list (rs.toList.map tyV)])]) := by
  rw [tyV, tyV_list, tyV_list]
  rfl

theorem tyV_group_eq (subs : Ty (.list .sub)) :
    tyV (Ty.group subs : CRecType) =
      .case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)])) := by
  rw [tyV, tyV_list]
  rfl

/-- The elements of a bounded sequence are typed at their sort. -/
theorem tyT_elems {k : TKind} {l : Ty (.list k)} (hb : tyBnd l = true) :
    ∀ w ∈ l.toList.map tyV, Round5.Pos.TyT B k w :=
  Round5.Pos.tyT_list_of l (Round5.Pos.tyT_tyV l hb)

/-! ## Validity of composite types -/

/-- `Comptype_ok/struct`, from the fields' readings. -/
theorem okD_struct {O : ElseI} {c : Value} (hc : CtxT B c) {fs : Ty (.list .field)}
    (hb : tyBnd fs = true) (h : OkD B O c (.list .field) fs) : OkD B O c .comp (.struct fs) := by
  show DDerivesB _ _ _ _ _ (.tuple [c, tyV (Ty.struct fs)])
  rw [tyV_struct_eq]
  refine dd_comptypeOkStruct O hc (tyT_elems hb) fun w hw => ?_
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hw
  exact h f hf

/-- `Resulttype_ok`, from the elements' readings. -/
theorem resultOk_of {O : ElseI} {c : Value} (hc : CtxT B c) {ts : Ty (.list .val)}
    (hb : tyBnd ts = true) (h : OkD B O c (.list .val) ts) :
    DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [c, .case "%" (.tuple [.list (ts.toList.map tyV)])]) := by
  refine dd_resulttypeOk O hc (fun w hw => (tyT_elems hb w hw).1) fun w hw => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
  exact h t ht

/-- `Comptype_ok/func`, from the readings of both sequences. -/
theorem okD_func {O : ElseI} {c : Value} (hc : CtxT B c) {ps rs : Ty (.list .val)}
    (hbp : tyBnd ps = true) (hbr : tyBnd rs = true) (hp : OkD B O c (.list .val) ps)
    (hr : OkD B O c (.list .val) rs) : OkD B O c .comp (.func ps rs) := by
  show DDerivesB _ _ _ _ _ (.tuple [c, tyV (Ty.func ps rs)])
  rw [tyV_func_eq]
  exact dd_comptypeOkFunc O hc (fun w hw => (tyT_elems hbp w hw).1)
    (fun w hw => (tyT_elems hbr w hw).1) (resultOk_of hc hbp hp) (resultOk_of hc hbr hr)

/-! ## Pointwise subtyping -/

/-- A pointwise relation between bounded sequences, at their images. -/
theorem forall2_map_tyV {k : TKind} {R : Ty k → Ty k → Prop} {S : Value → Value → Prop}
    (hRS : ∀ a b, tyBnd a = true → tyBnd b = true → R a b → S (tyV a) (tyV b)) :
    ∀ {l₁ l₂ : List (Ty k)}, List.Forall₂ R l₁ l₂ → (∀ a ∈ l₁, tyBnd a = true) →
      (∀ b ∈ l₂, tyBnd b = true) → List.Forall₂ S (l₁.map tyV) (l₂.map tyV)
  | [], [], _, _, _ => .nil
  | _ :: _, _ :: _, .cons h hs, h₁, h₂ =>
    .cons (hRS _ _ (h₁ _ List.mem_cons_self) (h₂ _ List.mem_cons_self) h)
      (forall2_map_tyV hRS hs (fun a ha => h₁ a (List.mem_cons_of_mem _ ha))
        (fun b hb => h₂ b (List.mem_cons_of_mem _ hb)))

/-- **`Resulttype_sub`** from the pointwise reading of `Valtype_sub`. -/
theorem resultSub_of {O : ElseI} {c : Value} (hc : CtxT B c) {l₁ l₂ : Ty (.list .val)}
    (hb₁ : tyBnd l₁ = true) (hb₂ : tyBnd l₂ = true) (h : SubD B O c (.list .val) l₁ l₂) :
    DDerivesB (simEnv B) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [c, .case "%" (.tuple [.list (l₁.toList.map tyV)]),
        .case "%" (.tuple [.list (l₂.toList.map tyV)])]) := by
  have hF := forall2_map_tyV (S := fun v w => (Round5.Pos.TyT B .val v ∧ Round5.Pos.TyT B .val w) ∧
      DDerivesB (simEnv B) O "Valtype_sub" "%|-%<:%" [] (.tuple [c, v, w]))
    (fun a b ha hb hab => ⟨⟨Round5.Pos.tyT_tyV a ha, Round5.Pos.tyT_tyV b hb⟩, hab⟩) h
    ((tyBnd_list_iff l₁).1 hb₁) ((tyBnd_list_iff l₂).1 hb₂)
  obtain ⟨ps, e₁, e₂, hps⟩ := forall2_zip hF
  rw [e₁, e₂]
  exact dd_resulttypeSub O hc (fun p hp => ⟨(hps p hp).1.1.1, (hps p hp).1.2.1⟩)
    fun p hp => (hps p hp).2

/-- **`Comptype_sub/func`**, from the pointwise readings of both sequences. -/
theorem subD_func {O : ElseI} {c : Value} (hc : CtxT B c) {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)}
    (hb₁ : tyBnd (Ty.func ps₁ rs₁) = true) (hb₂ : tyBnd (Ty.func ps₂ rs₂) = true)
    (hp : SubD B O c (.list .val) ps₂ ps₁) (hr : SubD B O c (.list .val) rs₁ rs₂) :
    SubD B O c .comp (.func ps₁ rs₁) (.func ps₂ rs₂) := by
  have b₁ := tyBnd_func' hb₁
  have b₂ := tyBnd_func' hb₂
  show DDerivesB _ _ _ _ _ (.tuple [c, tyV (Ty.func ps₁ rs₁), tyV (Ty.func ps₂ rs₂)])
  rw [tyV_func_eq, tyV_func_eq]
  refine dd_comptypeSubFunc O hc ?_ (resultSub_of hc b₂.1 b₁.1 hp) (resultSub_of hc b₁.2 b₂.2 hr)
  intro l hl t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact (tyT_elems b₁.1 t ht).1
  · exact (tyT_elems b₁.2 t ht).1
  · exact (tyT_elems b₂.1 t ht).1
  · exact (tyT_elems b₂.2 t ht).1

/-- **`Comptype_sub/struct`**, from the pointwise reading of `Fieldtype_sub` on the prefix. -/
theorem subD_struct {O : ElseI} {c : Value} (hc : CtxT B c) {fs₁ extra fs₂ : Ty (.list .field)}
    (hb₁ : tyBnd (Ty.struct (fs₁.app extra)) = true) (hb₂ : tyBnd (Ty.struct fs₂) = true)
    (h : SubD B O c (.list .field) fs₁ fs₂) :
    SubD B O c .comp (.struct (fs₁.app extra)) (.struct fs₂) := by
  have b₁ := tyBnd_structApp hb₁
  have b₂ := tyBnd_struct' hb₂
  have hF := forall2_map_tyV (S := fun v w => (Round5.Pos.TyT B .field v ∧
      Round5.Pos.TyT B .field w) ∧
      DDerivesB (simEnv B) O "Fieldtype_sub" "%|-%<:%" [] (.tuple [c, v, w]))
    (fun a b ha hb hab => ⟨⟨Round5.Pos.tyT_tyV a ha, Round5.Pos.tyT_tyV b hb⟩, hab⟩) h
    ((tyBnd_list_iff fs₁).1 b₁.1) ((tyBnd_list_iff fs₂).1 b₂)
  obtain ⟨ps, e₁, e₂, hps⟩ := forall2_zip hF
  show DDerivesB _ _ _ _ _ (.tuple [c, tyV (Ty.struct (fs₁.app extra)), tyV (Ty.struct fs₂)])
  rw [tyV_struct_eq, tyV_struct_eq, e₂]
  have ha : (fs₁.app extra).toList.map tyV = ps.map Prod.fst ++ extra.toList.map tyV := by
    rw [Ty.app, Ty.toList_ofList, List.map_append, e₁]
  rw [ha]
  exact dd_comptypeSubStruct O hc (fun p hp => ⟨(hps p hp).1.1, (hps p hp).1.2⟩)
    (tyT_elems b₁.2) fun p hp => (hps p hp).2

/-! ## `Deftype_ok` in the group's own context -/

/-- **`Deftype_ok`**, from `Rectype_ok2` read in the group's own context `ctxOf (withRecsA Δ subs)`. -/
theorem okD_defn {O : ElseI} {Δ : TypeCtx} (hc : CtxT B (ctxOf Δ)) {subs : Ty (.list .sub)}
    {i : Nat} (hb : tyBnd (Ty.defn (.group subs) i : DefType) = true) (hi : i < subs.length)
    (hg : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOf (RefOkV.withRecsA Δ subs.toList), tyV (Ty.group subs : CRecType),
        .case "OK" (natV 0)])) :
    OkD B O (ctxOf Δ) .def (.defn (.group subs) i) := by
  rw [ctxOf_withRecsA] at hg
  exact dd_deftypeOk O hc hb hi hg

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
