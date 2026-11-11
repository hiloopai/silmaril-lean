module

public import Silmaril.Proofs.Wasm.Verify.Reach.Store

/-!
# Function reachability: the delegated reduction families

Each per-family relation of Core 3.0 (`ParametricStep`, `NumericStep`, `VectorStep`,
`VariableStep`, `TableStep`, `MemoryStep`, `RefStep`, `AggregateStep`) preserves `CfgIn G fs`.
References produced by a step come from the code, the frame or the store (all in `G`), or name
no function; `ref.func x` resolves through the frame's module, whose function list is `fs` (or
empty), and `x` is named by the instruction itself, so its address is in `G`.

New proofs, following the case split of silmaril-lean's `Step.good`
(`Silmaril.Wasm.SingleThreaded.Locality`).
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop} {Bad : Nat → Prop}

/-- The source instructions of a value. -/
def valPlains : Val → List Instr
  | .num ⟨.int t, b⟩ => [.intConst t b]
  | .num ⟨.float t, b⟩ => [.floatConst t b]
  | .vec b => [.vecConst b]
  | .ref _ => []

@[simp] theorem codePlains_toAdmin' (v : Val) (l : List Admin) :
    codePlains (v.toAdmin :: l) = valPlains v ++ codePlains l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, valPlains]

theorem valPlains_callees {v : Val} : ∀ i ∈ valPlains v, instrCallees i = [] := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [valPlains] <;> rfl

theorem CodeIn.nil : CodeIn G fs Pl [] := ⟨by simp, by simp, by simp⟩

theorem CodeIn.trap : CodeIn G fs Pl [.trap] := ⟨by simp, by simp, by simp⟩

/-- A single source instruction naming no function. -/
theorem CodeIn.plain {i : Instr} (h : instrCallees i = []) : CodeIn G fs Pl [.plain i] :=
  ⟨by simp, by simp, fun j hj => (List.mem_singleton.1 (by simpa using hj)) ▸ Or.inl h⟩

/-- A single value whose references are in `G`. -/
theorem CodeIn.val {v : Val} (h : ∀ r, v = .ref r → RefIn G r) : CodeIn G fs Pl [v.toAdmin] := by
  refine ⟨fun r hr => h r (by simpa using hr), fun fr hf => by simp at hf, fun i hi => ?_⟩
  simp only [codePlains_toAdmin', codePlains_nil, List.append_nil] at hi
  exact .inl (valPlains_callees i hi)

/-- The head value of invariant code has its references in `G`. -/
theorem CodeIn.head_val {v : Val} {l : List Admin} (h : CodeIn G fs Pl (v.toAdmin :: l)) :
    ∀ r, v = .ref r → RefIn G r :=
  fun r hr => h.1 r (by simp [hr])

theorem CodeIn.tail {x : Admin} {l : List Admin} (h : CodeIn G fs Pl (x :: l)) : CodeIn G fs Pl l :=
  (CodeIn.append (l₁ := [x]) (l₂ := l)).1 h |>.2

theorem CodeIn.mem_ref {code : List Admin} (h : CodeIn G fs Pl code) {r : Ref}
    (hr : r ∈ codeRefs code) : RefIn G r :=
  h.1 r hr

/-- Pure steps whose result is a trap or a single source instruction naming no function. -/
theorem CodeIn.of_out {is' : List Admin}
    (h : is' = [.trap] ∨ (∃ i, is' = [.plain i] ∧ instrCallees i = []) ∨
      ∃ n : NumVal, is' = [(Val.num n).toAdmin]) : CodeIn G fs Pl is' := by
  rcases h with rfl | ⟨i, rfl, hi⟩ | ⟨n, rfl⟩
  · exact CodeIn.trap
  · exact CodeIn.plain hi
  · exact CodeIn.val (fun r hr => by cases hr)

theorem NumericStep.out {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    is' = [.trap] ∨ (∃ i, is' = [.plain i] ∧ instrCallees i = []) ∨
      ∃ n : NumVal, is' = [(Val.num n).toAdmin] := by
  cases h <;> first | exact .inl rfl | (refine .inr (.inl ⟨_, rfl, ?_⟩); rfl) |
    exact .inr (.inr ⟨_, rfl⟩)

theorem VectorStep.out {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    is' = [.trap] ∨ (∃ i, is' = [.plain i] ∧ instrCallees i = []) ∨
      ∃ n : NumVal, is' = [(Val.num n).toAdmin] := by
  cases h <;> first | exact .inl rfl | (refine .inr (.inl ⟨_, rfl, ?_⟩); rfl) |
    exact .inr (.inr ⟨_, rfl⟩)

theorem ParametricStep.out {is is' : List Admin} (h : ParametricStep is is')
    (hc : CodeIn G fs Pl is) :
    CodeIn G fs Pl is' := by
  cases h with
  | unreachable => exact CodeIn.trap
  | nop => exact CodeIn.nil
  | drop => exact CodeIn.nil
  | selectTrue => exact CodeIn.val (CodeIn.head_val hc)
  | selectFalse => exact CodeIn.val (CodeIn.head_val (CodeIn.tail hc))


/-! ## Building the code invariant element by element -/

theorem CodeIn.cons {x : Admin} {l : List Admin} (hx : CodeIn G fs Pl [x]) (hl : CodeIn G fs Pl l) :
    CodeIn G fs Pl (x :: l) :=
  (CodeIn.append (l₁ := [x]) (l₂ := l)).2 ⟨hx, hl⟩

theorem CodeIn.ref {r : Ref} (h : RefIn G r) : CodeIn G fs Pl [.ref r] :=
  ⟨by simpa using h, by simp, by simp⟩

theorem mem_codeRefs_of_mem {code : List Admin} {r : Ref} (h : Admin.ref r ∈ code) :
    r ∈ codeRefs code := by
  induction code with
  | nil => cases h
  | cons x l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · rw [show x :: l = [x] ++ l from rfl, codeRefs_append]
      exact List.mem_append_right _ (ih h)

theorem CodeIn.ref_of_mem {code : List Admin} (h : CodeIn G fs Pl code) {r : Ref}
    (hr : Admin.ref r ∈ code) : RefIn G r :=
  h.1 r (mem_codeRefs_of_mem hr)

theorem CodeIn.val_of_mem {code : List Admin} (h : CodeIn G fs Pl code) {v : Val}
    (hv : v.toAdmin ∈ code) : ∀ r, v = .ref r → RefIn G r := by
  intro r hr
  subst hr
  exact h.ref_of_mem hv

theorem CodeIn.singleton_of_mem {l : List Admin} (h : CodeIn G fs Pl l) {x : Admin} (hx : x ∈ l) :
    CodeIn G fs Pl [x] := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  exact (CodeIn.append.1 (CodeIn.append.1 h).2).1

theorem CodeIn.of_forall : ∀ {l : List Admin}, (∀ x ∈ l, CodeIn G fs Pl [x]) → CodeIn G fs Pl l
  | [], _ => CodeIn.nil
  | x :: l, h => CodeIn.cons (h x (by simp)) (CodeIn.of_forall fun y hy => h y (by simp [hy]))

/-- Code made of elements of invariant code is invariant. -/
theorem CodeIn.subset {l l' : List Admin} (h : CodeIn G fs Pl l) (hs : ∀ x ∈ l', x ∈ l) :
    CodeIn G fs Pl l' :=
  CodeIn.of_forall fun x hx => h.singleton_of_mem (hs x hx)

/-- Build `CodeIn` of an explicit code list from the invariant `hc` of the code it came from:
values and references of `hc`'s code, references with a `RefIn` hypothesis in context, traps,
and source instructions naming no function. -/
macro "verify_code_tac" hc:term : tactic => `(tactic| repeat' (first
  | exact CodeIn.nil
  | refine CodeIn.cons CodeIn.trap ?_
  | refine CodeIn.cons (CodeIn.ref (RefIn.of_funcs_nil rfl)) ?_
  | refine CodeIn.cons (CodeIn.plain (by rfl)) ?_
  | refine CodeIn.cons (CodeIn.ref ‹_›) ?_
  | refine CodeIn.cons (CodeIn.val ‹_›) ?_
  | (refine CodeIn.cons (CodeIn.val (CodeIn.val_of_mem $hc ?m)) ?_
     case m => simp)
  | (refine CodeIn.cons (CodeIn.ref (CodeIn.ref_of_mem $hc ?m)) ?_
     case m => simp)
  | (refine CodeIn.subset $hc ?_; intro x hx
     simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  | (refine CodeIn.append.2 ⟨CodeIn.subset $hc ?m, ?_⟩
     case m => intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
       or_false] at hx ⊢; tauto)))

/-! ## Frames -/

theorem FrameIn.setLocal {f : Frame} (hf : FrameIn G fs f) {x : LocalIdx} {v : Val}
    (hv : ∀ r, v = .ref r → RefIn G r) : FrameIn G fs (f.setLocal x v) := by
  refine ⟨hf.1, fun r hr => ?_⟩
  rcases List.mem_or_eq_of_mem_set hr with hr | hr
  · exact hf.2 r hr
  · exact hv r (Option.some.inj hr).symm

theorem FrameIn.local {f : Frame} (hf : FrameIn G fs f) {x : LocalIdx} {v : Val}
    (h : f.local? x = some (some v)) : ∀ r, v = .ref r → RefIn G r := by
  intro r hr
  subst hr
  exact hf.2 r (List.mem_of_getElem? h)

/-! ## The families -/

section
variable {P : Profile}

theorem VariableStep.cfgIn {c c' : Config H} (h : VariableStep c c') (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl c' := by
  cases h with
  | localGet hl => exact ⟨hc.1, hc.2.1, CodeIn.val (hc.2.1.local hl)⟩
  | localSet => exact ⟨hc.1, hc.2.1.setLocal (CodeIn.head_val hc.2.2), CodeIn.nil⟩
  | localTee => exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩
  | globalGet hg => exact ⟨hc.1, hc.2.1, CodeIn.val (fun r hr => hc.1.global hg hr)⟩
  | globalSet => exact ⟨hc.1.setGlobal (CodeIn.head_val hc.2.2), hc.2.1, CodeIn.nil⟩

theorem StoreIn.setTable_set {s : Store H} (hs : StoreIn G s) {f : Frame} {x : TableIdx}
    {a : Nat} {ti : TableInst} (ht : s.table? f x = some (a, ti)) {i : Nat} {r : Ref}
    (hr : RefIn G r) : StoreIn G (s.setTable a { ti with refs := ti.refs.set i r }) := by
  refine hs.setTable fun r' hr' => ?_
  rcases List.mem_or_eq_of_mem_set hr' with hr' | rfl
  · exact hs.table ht hr'
  · exact hr

theorem StoreIn.setTable_grow {s : Store H} (hs : StoreIn G s) {f : Frame} {x : TableIdx}
    {a : Nat} {ti ti' : TableInst} (ht : s.table? f x = some (a, ti)) {n : Nat} {r : Ref}
    (hg : ti.grow? n r = some ti') (hr : RefIn G r) : StoreIn G (s.setTable a ti') := by
  refine hs.setTable fun r' hr' => ?_
  rw [TableInst.grow?_refs hg, List.mem_append] at hr'
  rcases hr' with hr' | hr'
  · exact hs.table ht hr'
  · exact (List.mem_replicate.1 hr').2 ▸ hr

theorem TableStep.cfgIn {c c' : Config H} (h : TableStep P c c') (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl c' := by
  cases h with
  | getVal ht hr => exact ⟨hc.1, hc.2.1, CodeIn.ref (hc.1.table ht (List.mem_of_getElem? hr))⟩
  | setVal ht => exact ⟨hc.1.setTable_set ht (hc.2.2.ref_of_mem (by simp)), hc.2.1, CodeIn.nil⟩
  | growSucceed ht hg =>
    exact ⟨hc.1.setTable_grow ht hg (hc.2.2.ref_of_mem (by simp)), hc.2.1,
      by verify_code_tac hc.2.2⟩
  | initSucc ht he _ _ hr =>
    have hr' : RefIn G _ := hc.1.elem he (List.mem_of_getElem? hr)
    exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩
  | elemDrop => exact ⟨hc.1.setElemNil, hc.2.1, CodeIn.nil⟩
  | _ => exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩

theorem MemoryStep.cfgIn {c c' : Config H} (h : MemoryStep P c c') (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl c' := by
  cases h <;> first
    | exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩
    | exact ⟨hc.1.setMem, hc.2.1, by verify_code_tac hc.2.2⟩
    | exact ⟨hc.1.setData, hc.2.1, by verify_code_tac hc.2.2⟩

/-- The value prefix of invariant code has its references in `G`. -/
theorem CodeIn.vals_refs {vs : List Val} {l : List Admin} (h : CodeIn G fs Pl (vals vs ++ l)) :
    ∀ r, Val.ref r ∈ vs → RefIn G r :=
  fun r hr => h.1 r (by simp [hr])

theorem CodeIn.vals_append {vs : List Val} {l : List Admin} (hv : ∀ r, Val.ref r ∈ vs → RefIn G r)
    (hl : CodeIn G fs Pl l) : CodeIn G fs Pl (vals vs ++ l) :=
  CodeIn.append.2 ⟨CodeIn.ofVals hv, hl⟩

theorem CodeIn.plain_head {i : Instr} {l : List Admin} (h : CodeIn G fs Pl (.plain i :: l)) :
    PlOK Pl i :=
  h.2.2 i (by simp)

/-- A source instruction naming a function satisfies `Pl`. -/
theorem PlOK.of_callee {i : Instr} (h : PlOK Pl i) {x : Nat} (hx : x ∈ instrCallees i) : Pl i :=
  h.elim (fun h' => by simp [h'] at hx) id

/-- A function index resolved in a `FrameIn` frame is resolved in `fs`. -/
theorem FrameIn.resolve {f : Frame} (hf : FrameIn G fs f) {x a : Nat}
    (h : f.module.funcs[x]? = some a) : fs[x]? = some a := by
  rcases hf.1 with hm | hm
  · exact hm ▸ h
  · simp [hm] at h

theorem RefStep.cfgIn (hP : PlainOK G Bad fs Pl) {c c' : Config H} (h : RefStep c c')
    (hc : CfgIn G fs Pl c) : CfgIn G fs Pl c' := by
  cases h with
  | refFunc hx =>
    have hi : Pl (.refFunc _) := hc.2.2.plain_head.of_callee (x := _) (by simp [instrCallees]; rfl)
    exact ⟨hc.1, hc.2.1, CodeIn.ref (by simpa using hP.refFunc _ _ hi (hc.2.1.resolve hx))⟩
  | externConvertAddr =>
    exact ⟨hc.1, hc.2.1, CodeIn.ref (by simpa using hc.2.2.ref_of_mem (by simp))⟩
  | anyConvertAddr r =>
    exact ⟨hc.1, hc.2.1, CodeIn.ref (by simpa using hc.2.2.ref_of_mem (r := .extern r) (by simp))⟩
  | _ => exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩

theorem refIn_packField_zip {α : Type} {F : α × Val → FieldVal}
    (hF : ∀ ft v r, F (ft, v) = .val (.ref r) → v = .ref r) {l : List α} {vs : List Val}
    (hvs : ∀ r, Val.ref r ∈ vs → RefIn G r) :
    ∀ r, FieldVal.val (.ref r) ∈ (l.zip vs).map F → RefIn G r := by
  intro r hr
  obtain ⟨⟨ft, v⟩, hmem, hp⟩ := List.mem_map.1 hr
  have hv : v = .ref r := hF ft v r hp
  exact hvs r (hv ▸ (List.of_mem_zip hmem).2)

theorem refIn_packField_map {z : CStorageType} {vs : List Val}
    (hvs : ∀ r, Val.ref r ∈ vs → RefIn G r) :
    ∀ r, FieldVal.val (.ref r) ∈ vs.map (packField z) → RefIn G r := by
  intro r hr
  obtain ⟨v, hmem, hp⟩ := List.mem_map.1 hr
  have hv : v = .ref r := packField_eq_ref hp
  exact hvs r (hv ▸ hmem)

theorem refIn_packField {z : CStorageType} {v : Val} (hv : ∀ r, v = .ref r → RefIn G r) :
    ∀ r, packField z v = .val (.ref r) → RefIn G r :=
  fun r hr => hv r (packField_eq_ref hr)

theorem refIn_defaults {α : Type} {g : α → Option Val}
    (hg : ∀ x v, g x = some v → ∀ r, v ≠ .ref r ∨ r = .null)
    {l : List α} {vs : List Val} (h : l.mapM g = some vs) : ∀ r, Val.ref r ∈ vs → RefIn G r := by
  intro r hr
  obtain ⟨x, -, hx⟩ := mapM_some_mem h _ hr
  rcases hg x _ hx r with h' | rfl
  · exact absurd rfl h'
  · exact refIn_null

theorem defaultVal?_refs {t : CValType} {v : Val} (h : defaultVal? t = some v) :
    ∀ r, v ≠ .ref r ∨ r = .null := by
  intro r
  by_cases hv : v = .ref r
  · subst hv
    exact .inr (defaultVal?_ref h)
  · exact .inl hv

theorem readField?_refs {z : CStorageType} {b : ByteArray} {o : Nat} {v : Val}
    (h : readField? z b o = some v) : ∀ r, v ≠ .ref r ∨ r = .null := by
  intro r
  left
  rintro rfl
  exact readField?_ne_ref h

theorem refIn_of_not_ref {v : Val} (h : ∀ r, v ≠ .ref r ∨ r = .null) :
    ∀ r, v = .ref r → RefIn G r := by
  intro r hr
  rcases h r with h' | rfl
  · exact absurd hr h'
  · exact refIn_null

theorem refIn_unpack {sx : Option Signedness} {fv : FieldVal}
    {fields : List FieldVal} (hmem : fv ∈ fields)
    (hf : ∀ r, FieldVal.val (.ref r) ∈ fields → RefIn G r) :
    ∀ r, unpackField sx fv = .ref r → RefIn G r := by
  intro r hr
  have hfv : fv = .val (.ref r) := unpackField_eq_ref hr
  exact hf r (hfv ▸ hmem)

theorem CodeIn.map_ref_append {l : List Ref} {rest : List Admin} (hl : ∀ r ∈ l, RefIn G r)
    (hr : CodeIn G fs Pl rest) : CodeIn G fs Pl (l.map Admin.ref ++ rest) := by
  refine CodeIn.append.2 ⟨⟨fun r hr' => hl r (by simpa using hr'), by simp, by simp⟩, hr⟩

theorem refIn_replicate {n : Nat} {v : Val} (hv : ∀ r, v = .ref r → RefIn G r) :
    ∀ r, Val.ref r ∈ List.replicate n v → RefIn G r :=
  fun r hr => hv r (List.mem_replicate.1 hr).2.symm

theorem AggregateStep.cfgIn {c c' : Config H} (h : AggregateStep c c') (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl c' := by
  cases h with
  | structNew =>
    exact ⟨hc.1.addStruct (refIn_packField_zip (fun _ _ _ hp => packField_eq_ref hp)
      (CodeIn.vals_refs hc.2.2)), hc.2.1, by verify_code_tac hc.2.2⟩
  | structNewDefault _ _ hdef =>
    exact ⟨hc.1, hc.2.1, CodeIn.vals_append
      (refIn_defaults (fun _ _ h => defaultVal?_refs h) hdef) (CodeIn.plain rfl)⟩
  | structGetStruct hs hf =>
    exact ⟨hc.1, hc.2.1, CodeIn.val (refIn_unpack (List.mem_of_getElem? hf)
      (fun _ hr => hc.1.struct hs hr))⟩
  | structSetStruct =>
    exact ⟨hc.1.setStructField (refIn_packField (CodeIn.val_of_mem hc.2.2 (by simp))), hc.2.1,
      CodeIn.nil⟩
  | arrayNew v n =>
    exact ⟨hc.1, hc.2.1, CodeIn.vals_append (refIn_replicate (CodeIn.val_of_mem hc.2.2 (by simp)))
      (CodeIn.plain rfl)⟩
  | arrayNewDefault _ _ hv =>
    exact ⟨hc.1, hc.2.1, CodeIn.vals_append (refIn_replicate (refIn_of_not_ref
      (defaultVal?_refs hv))) (CodeIn.plain rfl)⟩
  | arrayNewFixed =>
    exact ⟨hc.1.addArray (refIn_packField_map (CodeIn.vals_refs hc.2.2)), hc.2.1,
      by verify_code_tac hc.2.2⟩
  | arrayNewElemAlloc he =>
    exact ⟨hc.1, hc.2.1, CodeIn.map_ref_append
      (fun _ hr => hc.1.elem he (List.mem_of_mem_drop (List.mem_of_mem_take hr)))
      (CodeIn.plain rfl)⟩
  | arrayNewDataNum _ _ _ _ _ hvs =>
    exact ⟨hc.1, hc.2.1, CodeIn.vals_append
      (refIn_defaults (fun _ _ h => readField?_refs h) hvs) (CodeIn.plain rfl)⟩
  | arrayGetArray ha hf =>
    exact ⟨hc.1, hc.2.1, CodeIn.val (refIn_unpack (List.mem_of_getElem? hf)
      (fun _ hr => hc.1.array ha hr))⟩
  | arraySetArray =>
    exact ⟨hc.1.setArrayField (refIn_packField (CodeIn.val_of_mem hc.2.2 (by simp))), hc.2.1,
      CodeIn.nil⟩
  | arrayInitElemSucc _ he _ _ hr =>
    have hr' : RefIn G _ := hc.1.elem he (List.mem_of_getElem? hr)
    exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩
  | arrayInitDataNum _ _ _ _ _ _ hv =>
    have hv' : ∀ r, _ = Val.ref r → RefIn G r := refIn_of_not_ref (readField?_refs hv)
    exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩
  | _ => exact ⟨hc.1, hc.2.1, by verify_code_tac hc.2.2⟩

end

end Silmaril.Wasm.Verify
