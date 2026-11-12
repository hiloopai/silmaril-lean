module

public import Silmaril.Proofs.Wasm.Component.Wat.Parts

/-!
# Component WAT: type definitions read back

`R.defType (P.defType t) = some (normDefType t)`, by induction on type definitions
together with the declarations of component and instance types.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary Sexp

theorem valType_atom (t : Silmaril.Wasm.Component.Binary.ValType) : ∃ a, P.valType t = .atom a := by
  cases t with
  | prim p => cases p <;> exact ⟨_, rfl⟩
  | idx i => exact ⟨_, rfl⟩

theorem result_rt (ok err : Option Silmaril.Wasm.Component.Binary.ValType) :
    R.defValType (P.defValType (.result ok err)) = some (.result ok err) := by
  cases ok with
  | none => cases err <;> simp [P.defValType, R.defValType, R.resultBody, valType_rt]
  | some t =>
    obtain ⟨a, ha⟩ := valType_atom t
    have ht : R.valType (.atom a) = some t := ha ▸ valType_rt t
    cases err <;> simp [P.defValType, R.defValType, R.resultBody, ht, ha, valType_rt]

theorem stream_rt (t : Option Silmaril.Wasm.Component.Binary.ValType) :
    R.defValType (P.defValType (.stream t)) = some (.stream t) := by
  have h : R.optValType (t.map P.valType).toList = some t := optValType_rt t
  exact (show R.defValType (.list (kw "stream" :: (t.map P.valType).toList)) =
    (R.optValType (t.map P.valType).toList).map .stream by cases t <;> rfl).trans
    (by rw [h]; rfl)

theorem future_rt (t : Option Silmaril.Wasm.Component.Binary.ValType) :
    R.defValType (P.defValType (.future t)) = some (.future t) := by
  have h : R.optValType (t.map P.valType).toList = some t := optValType_rt t
  exact (show R.defValType (.list (kw "future" :: (t.map P.valType).toList)) =
    (R.optValType (t.map P.valType).toList).map .future by cases t <;> rfl).trans
    (by rw [h]; rfl)

theorem defValType_rt (d : DefValType) : R.defValType (P.defValType d) = some d := by
  cases d with
  | prim p => cases p <;> rfl
  | record fs =>
    simp only [P.defValType, R.defValType, Option.map_eq_some_iff]
    exact ⟨fs, mapO_map_id _ _ fs (fun f _ => by simp [R.field, valType_rt]), rfl⟩
  | variant cs =>
    simp only [P.defValType, R.defValType, Option.map_eq_some_iff]
    refine ⟨cs, mapO_map_id _ _ cs (fun c _ => ?_), rfl⟩
    obtain ⟨n, t⟩ := c
    cases t <;> simp [R.case, valType_rt]
  | tuple ts =>
    simp [P.defValType, R.defValType, mapO_map_id _ _ ts (fun t _ => valType_rt t)]
  | flags ls => simp [P.defValType, R.defValType, mapO_map_id _ _ ls (fun t _ => nm?_nm t)]
  | enum ls => simp [P.defValType, R.defValType, mapO_map_id _ _ ls (fun t _ => nm?_nm t)]
  | result ok err => exact result_rt ok err
  | stream t => exact stream_rt t
  | future t => exact future_rt t
  | _ => simp [P.defValType, R.defValType, valType_rt]

theorem params_rt (rest : List Sexp)
    (h : ∀ p r, rest = .list (.atom "param" :: p) :: r → False) :
    ∀ ps : List (String × Silmaril.Wasm.Component.Binary.ValType),
      R.params (ps.map (fun p => .list [kw "param", nm p.1, P.valType p.2]) ++ rest) =
        some (ps, rest)
  | [] => by
    match rest, h with
    | [], _ => rfl
    | .atom a :: r, _ => rfl
    | .str b :: r, _ => rfl
    | .list [] :: r, _ => rfl
    | .list (.str b :: q) :: r, _ => rfl
    | .list (.list x :: q) :: r, _ => rfl
    | .list (.atom a :: q) :: r, h =>
      by_cases ha : a = "param"
      · subst ha; exact absurd rfl (h q r)
      · simp [R.params]
  | p :: ps => by
    simp [R.params, R.param, valType_rt, params_rt rest h ps]

theorem funcType_rt (f : Silmaril.Wasm.Component.Binary.FuncType) :
    R.funcType (match P.funcType f with
      | .list (_ :: ss) => ss
      | _ => []) = some f := by
  obtain ⟨ps, res, async⟩ := f
  have hb : R.funcBody async (ps.map (fun p => .list [kw "param", nm p.1, P.valType p.2]) ++
      (res.map fun r => .list [kw "result", P.valType r]).toList) = some ⟨ps, res, async⟩ := by
    rw [R.funcBody, params_rt _ (by cases res <;> simp)]
    cases res <;> simp [valType_rt]
  cases async with
  | true => exact hb
  | false =>
    rcases ps with _ | ⟨p, ps⟩
    · cases res <;> exact hb
    · exact hb

theorem resource_rt (r : CoreValType) (d : Option Nat) :
    R.resource (.list [kw "rep", P.coreValType r] ::
      (d.map fun d => .list [kw "dtor", num d]).toList) = some (.resource r d) := by
  cases d <;> simp [R.resource, coreValType_rt]

theorem defType_atom (a : String) :
    R.defType (.atom a) = (R.defValType (.atom a)).map .val := by
  rw [R.defType.eq_def]

theorem defType_list (k : String) (ss : List Sexp) (h1 : k ≠ "func") (h2 : k ≠ "component")
    (h3 : k ≠ "instance") (h4 : k ≠ "resource") :
    R.defType (.list (.atom k :: ss)) = (R.defValType (.list (.atom k :: ss))).map .val := by
  rw [R.defType.eq_def]
  split <;> simp_all

theorem defValType_shape (d : DefValType) : (∃ a, P.defValType d = .atom a) ∨
    ∃ k ss, P.defValType d = .list (.atom k :: ss) ∧ k ≠ "func" ∧ k ≠ "component" ∧
      k ≠ "instance" ∧ k ≠ "resource" := by
  cases d with
  | prim p => cases p <;> exact .inl ⟨_, rfl⟩
  | _ => exact .inr ⟨_, _, rfl, by decide, by decide, by decide, by decide⟩

theorem defType_val (d : DefValType) :
    R.defType (P.defValType d) = (R.defValType (P.defValType d)).map .val := by
  rcases defValType_shape d with ⟨a, ha⟩ | ⟨k, ss, hk, h1, h2, h3, h4⟩
  · rw [ha]; exact defType_atom a
  · rw [hk]; exact defType_list k ss h1 h2 h3 h4

/-! ## Equations of the readers -/

theorem defType_func (ss : List Sexp) :
    R.defType (.list (.atom "func" :: ss)) = (R.funcType ss).map .func := by
  rw [R.defType.eq_def]
  try rfl

theorem defType_component (ss : List Sexp) :
    R.defType (.list (.atom "component" :: ss)) = (R.componentDecls ss).map .component := by
  rw [R.defType.eq_def]
  try rfl

theorem defType_instance (ss : List Sexp) :
    R.defType (.list (.atom "instance" :: ss)) = (R.instanceDecls ss).map .instance := by
  rw [R.defType.eq_def]
  try rfl

theorem defType_resource (ss : List Sexp) :
    R.defType (.list (.atom "resource" :: ss)) = R.resource ss := by
  rw [R.defType.eq_def]
  try rfl

theorem instanceDecl_coreType (t : Sexp) :
    R.instanceDecl (.list [.atom "core", .atom "type", t]) = (R.coreType t).map .coreType := by
  rw [R.instanceDecl.eq_def]
  try rfl

theorem instanceDecl_type (t : Sexp) :
    R.instanceDecl (.list [.atom "type", t]) = (R.defType t).map .type := by
  rw [R.instanceDecl.eq_def]
  try rfl

theorem instanceDecl_alias' (ss : List Sexp) :
    R.instanceDecl (.list (.atom "alias" :: ss)) = (R.alias_ ss).map .alias := by
  rw [R.instanceDecl.eq_def]
  try rfl

theorem instanceDecl_export (ss : List Sexp) :
    R.instanceDecl (.list (.atom "export" :: ss)) =
      (R.nameDesc ss).map fun p => .export p.1 p.2 := by
  rw [R.instanceDecl.eq_def]
  try rfl

theorem componentDecl_import (ss : List Sexp) :
    R.componentDecl (.list (.atom "import" :: ss)) =
      (R.nameDesc ss).map fun p => .import p.1 p.2 := by
  rw [R.componentDecl.eq_def]
  try rfl

theorem componentDecl_other (k : String) (ss : List Sexp) (h : k ≠ "import") :
    R.componentDecl (.list (.atom k :: ss)) =
      (R.instanceDecl (.list (.atom k :: ss))).map .inst := by
  rw [R.componentDecl.eq_def]
  split <;> simp_all

theorem instanceDecls_cons (s : Sexp) (ss : List Sexp) :
    R.instanceDecls (s :: ss) = (do
      let d ← R.instanceDecl s
      let ds ← R.instanceDecls ss
      pure (d :: ds)) := by
  rw [R.instanceDecls.eq_def]

theorem componentDecls_cons (s : Sexp) (ss : List Sexp) :
    R.componentDecls (s :: ss) = (do
      let d ← R.componentDecl s
      let ds ← R.componentDecls ss
      pure (d :: ds)) := by
  rw [R.componentDecls.eq_def]

theorem instanceDecl_alias (a : Alias) :
    R.instanceDecl (P.alias_ a) = some (.alias a) := by
  have h := alias_rt a
  obtain ⟨ss, hs⟩ := alias_list a
  rw [hs] at h ⊢
  rw [instanceDecl_alias']
  simp only at h
  rw [h]; rfl

theorem instanceDecl_shape (d : InstanceDecl) :
    ∃ k ss, P.instanceDecl d = .list (.atom k :: ss) ∧ k ≠ "import" := by
  rcases d with t | t | a | ⟨n, d⟩
  · exact ⟨_, _, rfl, by decide⟩
  · exact ⟨_, _, rfl, by decide⟩
  · obtain ⟨ss, hs⟩ := alias_list a
    exact ⟨_, _, hs, by decide⟩
  · exact ⟨_, _, rfl, by decide⟩

theorem componentDecl_inst (d : InstanceDecl) :
    R.componentDecl (P.instanceDecl d) = (R.instanceDecl (P.instanceDecl d)).map .inst := by
  obtain ⟨k, ss, hk, h⟩ := instanceDecl_shape d
  rw [hk]
  exact componentDecl_other k ss h

mutual
theorem defType_rt : ∀ t : DefType, R.defType (P.defType t) = some (normDefType t)
  | .val d => by
    show R.defType (P.defValType d) = some (.val d)
    rw [defType_val, defValType_rt]; rfl
  | .func f => by
    have := funcType_rt f
    simp only [P.funcType] at this
    show R.defType (.list (.atom "func" :: _)) = _
    rw [defType_func, this]; rfl
  | .component ds => by
    show R.defType (.list (.atom "component" :: P.componentDecls ds)) = _
    rw [defType_component, componentDecls_rt ds]; rfl
  | .instance ds => by
    show R.defType (.list (.atom "instance" :: P.instanceDecls ds)) = _
    rw [defType_instance, instanceDecls_rt ds]; rfl
  | .resource r d => by
    show R.defType (.list (.atom "resource" :: _)) = _
    rw [defType_resource]
    exact resource_rt r d

theorem instanceDecl_rt : ∀ d : InstanceDecl,
    R.instanceDecl (P.instanceDecl d) = some (normInstanceDecl d)
  | .coreType t => by
    show R.instanceDecl (.list [.atom "core", .atom "type", P.coreType t]) = _
    rw [instanceDecl_coreType, coreType_rt]; rfl
  | .type t => by
    show R.instanceDecl (.list [.atom "type", P.defType t]) = _
    rw [instanceDecl_type, defType_rt t]; rfl
  | .alias a => instanceDecl_alias a
  | .export n d => by
    show R.instanceDecl (.list (.atom "export" :: (P.name n ++ [P.externDesc d]))) = _
    rw [instanceDecl_export, nameDesc_rt]; rfl

theorem componentDecl_rt : ∀ d : ComponentDecl,
    R.componentDecl (P.componentDecl d) = some (normComponentDecl d)
  | .import n d => by
    show R.componentDecl (.list (.atom "import" :: (P.name n ++ [P.externDesc d]))) = _
    rw [componentDecl_import, nameDesc_rt]; rfl
  | .inst d => by
    show R.componentDecl (P.instanceDecl d) = _
    rw [componentDecl_inst, instanceDecl_rt d]; rfl

theorem instanceDecls_rt : ∀ ds : List InstanceDecl,
    R.instanceDecls (P.instanceDecls ds) = some (normInstanceDecls ds)
  | [] => by rw [R.instanceDecls.eq_def]; rfl
  | d :: ds => by
    show R.instanceDecls (P.instanceDecl d :: P.instanceDecls ds) = _
    rw [instanceDecls_cons, instanceDecl_rt d, instanceDecls_rt ds]; rfl

theorem componentDecls_rt : ∀ ds : List ComponentDecl,
    R.componentDecls (P.componentDecls ds) = some (normComponentDecls ds)
  | [] => by rw [R.componentDecls.eq_def]; rfl
  | d :: ds => by
    show R.componentDecls (P.componentDecl d :: P.componentDecls ds) = _
    rw [componentDecls_cons, componentDecl_rt d, componentDecls_rt ds]; rfl
end

end Silmaril.Wasm.Component.Wat
