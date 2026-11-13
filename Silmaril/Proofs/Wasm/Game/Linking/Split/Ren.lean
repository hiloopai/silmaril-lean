module

public import Silmaril.Wasm.SingleThreaded.Locality
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Static linking, separation: Ren

Original module documentation:

# Renaming of GC addresses and ownership (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B): the
vocabulary of the store-splitting relation used by `Linking.Setup.shared_objPlays_eq_split`.

The shared world runs provider and consumer in one store; the split world runs each in its own
store. Both allocate GC structs and arrays, so a *part* store (provider or consumer) embeds
into the shared store through a renaming `Ren` of struct and array addresses. Function and
global addresses are not renamed (no function or global is allocated at run time).

* `Ren.ref`, `Ren.val`, `Ren.fval`, `Ren.frame`, `Ren.code`: the renaming applied to
  references, values, field values, frames and administrative code.
* `Own`: what a part owns (struct, array, function and global addresses);
  `GoodRef`/`GoodVal`/`ModGood`/`FrameGood`/`CodeGood`: the references and module instances a
  part's thread may hold (no exception or host references; module instances without tags,
  memories, tables, element or data segments, whose globals and functions are owned).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- A renaming of struct and array addresses. -/
structure Ren where
  st : Nat → Nat
  ar : Nat → Nat

namespace Ren

variable (ρ : Ren)

/-- Renaming of a reference. -/
def ref : Ref → Ref
  | .struct a => .struct (ρ.st a)
  | .array a => .array (ρ.ar a)
  | .extern r => .extern (ref r)
  | r => r

/-- Renaming of a value. -/
def val : Val → Val
  | .ref r => .ref (ρ.ref r)
  | v => v

/-- Renaming of a field value. -/
def fval : FieldVal → FieldVal
  | .val v => .val (ρ.val v)
  | p => p

/-- Renaming of a frame (its locals). -/
def frame (f : Frame) : Frame := { f with locals := f.locals.map (Option.map ρ.val) }

/-- Renaming of administrative code. -/
def code : List Admin → List Admin
  | [] => []
  | .ref r :: l => .ref (ρ.ref r) :: code l
  | .label n c b :: l => .label n c (code b) :: code l
  | .handler n cs b :: l => .handler n cs (code b) :: code l
  | .frame n f b :: l => .frame n (ρ.frame f) (code b) :: code l
  | a :: l => a :: code l

/-- Renaming of a struct instance. -/
def sinst (si : StructInst) : StructInst := { si with fields := si.fields.map ρ.fval }

/-- Renaming of an array instance. -/
def ainst (ai : ArrayInst) : ArrayInst := { ai with fields := ai.fields.map ρ.fval }

/-- Renaming of a global instance. -/
def ginst (g : GlobalInst) : GlobalInst := { g with value := ρ.val g.value }

/-- Renaming of a result. -/
def result : Result → Result
  | .values vs => .values (vs.map ρ.val)
  | r => r

@[simp] theorem frame_module (f : Frame) : (ρ.frame f).module = f.module := rfl
@[simp] theorem frame_locals (f : Frame) :
    (ρ.frame f).locals = f.locals.map (Option.map ρ.val) := rfl

@[simp] theorem code_nil : ρ.code [] = [] := by simp [code]
@[simp] theorem code_plain (i : Instr) (l : List Admin) :
    ρ.code (.plain i :: l) = .plain i :: ρ.code l := by simp [code]
@[simp] theorem code_ref (r : Ref) (l : List Admin) :
    ρ.code (.ref r :: l) = .ref (ρ.ref r) :: ρ.code l := by simp [code]
@[simp] theorem code_callRefType (d : DefType) (l : List Admin) :
    ρ.code (.callRefType d :: l) = .callRefType d :: ρ.code l := by simp [code]
@[simp] theorem code_returnCallRefType (d : DefType) (l : List Admin) :
    ρ.code (.returnCallRefType d :: l) = .returnCallRefType d :: ρ.code l := by simp [code]
@[simp] theorem code_trap (l : List Admin) : ρ.code (.trap :: l) = .trap :: ρ.code l := by
  simp [code]
@[simp] theorem code_label (n : Nat) (c : List Instr) (b l : List Admin) :
    ρ.code (.label n c b :: l) = .label n c (ρ.code b) :: ρ.code l := by simp [code]
@[simp] theorem code_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    ρ.code (.handler n cs b :: l) = .handler n cs (ρ.code b) :: ρ.code l := by simp [code]
@[simp] theorem code_frame (n : Nat) (f : Frame) (b l : List Admin) :
    ρ.code (.frame n f b :: l) = .frame n (ρ.frame f) (ρ.code b) :: ρ.code l := by simp [code]

@[simp] theorem code_append (l₁ l₂ : List Admin) :
    ρ.code (l₁ ++ l₂) = ρ.code l₁ ++ ρ.code l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem code_cons_toAdmin (v : Val) (l : List Admin) :
    ρ.code (v.toAdmin :: l) = (ρ.val v).toAdmin :: ρ.code l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, val]

@[simp] theorem code_vals (vs : List Val) : ρ.code (vals vs) = vals (vs.map ρ.val) := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simp [vals_cons, ih]

@[simp] theorem code_expression (es : List Instr) : ρ.code (expression es) = expression es := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem code_map_ref (l : List Ref) :
    ρ.code (l.map Admin.ref) = (l.map ρ.ref).map Admin.ref := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem code_constI32 (b : BitVec 32) (l : List Admin) :
    ρ.code (constI32 b :: l) = constI32 b :: ρ.code l := by
  simp [constI32, Val.i32, Val.toAdmin]

@[simp] theorem val_num (v : NumVal) : ρ.val (.num v) = .num v := rfl
@[simp] theorem val_vec (b : BitVec 128) : ρ.val (.vec b) = .vec b := rfl
@[simp] theorem val_ref (r : Ref) : ρ.val (.ref r) = .ref (ρ.ref r) := rfl
@[simp] theorem val_i32 (b : BitVec 32) : ρ.val (Val.i32 b) = Val.i32 b := rfl
@[simp] theorem ref_null : ρ.ref .null = .null := rfl
@[simp] theorem ref_i31 (b : BitVec 31) : ρ.ref (.i31 b) = .i31 b := rfl
@[simp] theorem ref_struct (a : Nat) : ρ.ref (.struct a) = .struct (ρ.st a) := rfl
@[simp] theorem ref_array (a : Nat) : ρ.ref (.array a) = .array (ρ.ar a) := rfl
@[simp] theorem ref_func (a : Nat) : ρ.ref (.func a) = .func a := rfl
@[simp] theorem ref_exn (a : Nat) : ρ.ref (.exn a) = .exn a := rfl
@[simp] theorem ref_host (a : Nat) : ρ.ref (.host a) = .host a := rfl
@[simp] theorem ref_extern (r : Ref) : ρ.ref (.extern r) = .extern (ρ.ref r) := rfl
@[simp] theorem fval_val (v : Val) : ρ.fval (.val v) = .val (ρ.val v) := rfl
@[simp] theorem fval_pack (p : PackType) (b : BitVec p.width) :
    ρ.fval (.pack p b) = .pack p b := rfl

theorem ref_eq_null_iff {r : Ref} : ρ.ref r = .null ↔ r = .null := by
  cases r <;> simp [ref]

theorem result_toAdmin (r : Result) (h : ∀ a, r ≠ .throw a) :
    ρ.code r.toAdmin = (ρ.result r).toAdmin := by
  cases r with
  | values vs => simp [Result.toAdmin, result]
  | throw a => exact absurd rfl (h a)
  | trap => simp [Result.toAdmin, result]

end Ren

/-- What a part (provider or consumer) owns. -/
structure Own where
  st : Nat → Prop
  ar : Nat → Prop
  fn : Nat → Prop
  gl : Nat → Prop

namespace Own

variable (O : Own)

/-- References a part's thread may hold. -/
def GoodRef : Ref → Prop
  | .i31 _ => True
  | .null => True
  | .struct a => O.st a
  | .array a => O.ar a
  | .func a => O.fn a
  | .exn _ => False
  | .host _ => False
  | .extern r => GoodRef r

/-- Values a part's thread may hold. -/
def GoodVal : Val → Prop
  | .ref r => O.GoodRef r
  | _ => True

/-- Field values a part may store. -/
def GoodFV : FieldVal → Prop
  | .val v => O.GoodVal v
  | _ => True

/-- Module instances a part's frames may use. -/
structure ModGood (m : ModuleInst) : Prop where
  tags : m.tags = []
  mems : m.mems = []
  tables : m.tables = []
  elems : m.elems = []
  datas : m.datas = []
  globals : ∀ g ∈ m.globals, O.gl g
  funcs : ∀ a ∈ m.funcs, O.fn a

/-- Frames a part's thread may hold. -/
def FrameGood (f : Frame) : Prop :=
  O.ModGood f.module ∧ ∀ v, some v ∈ f.locals → O.GoodVal v

/-- Code a part's thread may hold. -/
def CodeGood (l : List Admin) : Prop :=
  (∀ r ∈ codeRefs l, O.GoodRef r) ∧ ∀ fr ∈ codeFrames l, O.FrameGood fr

@[simp] theorem goodVal_ref (r : Ref) : O.GoodVal (.ref r) ↔ O.GoodRef r := Iff.rfl
@[simp] theorem goodVal_num (v : NumVal) : O.GoodVal (.num v) := trivial
@[simp] theorem goodVal_vec (b : BitVec 128) : O.GoodVal (.vec b) := trivial
@[simp] theorem goodFV_val (v : Val) : O.GoodFV (.val v) ↔ O.GoodVal v := Iff.rfl
@[simp] theorem goodFV_pack (p : PackType) (b : BitVec p.width) : O.GoodFV (.pack p b) := trivial
@[simp] theorem goodRef_null : O.GoodRef .null := trivial
@[simp] theorem goodRef_i31 (b : BitVec 31) : O.GoodRef (.i31 b) := trivial
@[simp] theorem goodRef_struct (a : Nat) : O.GoodRef (.struct a) ↔ O.st a := Iff.rfl
@[simp] theorem goodRef_array (a : Nat) : O.GoodRef (.array a) ↔ O.ar a := Iff.rfl
@[simp] theorem goodRef_func (a : Nat) : O.GoodRef (.func a) ↔ O.fn a := Iff.rfl
@[simp] theorem goodRef_exn (a : Nat) : ¬ O.GoodRef (.exn a) := id
@[simp] theorem goodRef_host (a : Nat) : ¬ O.GoodRef (.host a) := id
@[simp] theorem goodRef_extern (r : Ref) : O.GoodRef (.extern r) ↔ O.GoodRef r := Iff.rfl

theorem codeGood_append {l₁ l₂ : List Admin} :
    O.CodeGood (l₁ ++ l₂) ↔ O.CodeGood l₁ ∧ O.CodeGood l₂ := by
  simp only [CodeGood, codeRefs_append, codeFrames_append, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun r hr => h1 r (Or.inl hr), fun f hf => h2 f (Or.inl hf)⟩,
      ⟨fun r hr => h1 r (Or.inr hr), fun f hf => h2 f (Or.inr hf)⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun r hr => hr.elim (h1 r) (h3 r), fun f hf => hf.elim (h2 f) (h4 f)⟩

theorem codeGood_vals {vs : List Val} : O.CodeGood (vals vs) ↔ ∀ v ∈ vs, O.GoodVal v := by
  simp only [CodeGood, codeRefs_vals, codeFrames_vals, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, List.mem_flatMap]
  constructor
  · intro h v hv
    cases v with
    | ref r => exact h r ⟨_, hv, by simp [Val.heapRefs]⟩
    | num => trivial
    | vec => trivial
  · rintro h r ⟨v, hv, hr⟩
    have := h v hv
    cases v with
    | ref r' =>
      simp only [Val.heapRefs, List.mem_singleton] at hr
      subst hr; exact this
    | num => simp [Val.heapRefs] at hr
    | vec => simp [Val.heapRefs] at hr

theorem codeGood_expression (es : List Instr) : O.CodeGood (expression es) := by
  simp [CodeGood]

theorem codeGood_nil : O.CodeGood [] := by simp [CodeGood]

theorem codeGood_cons {a : Admin} {l : List Admin} :
    O.CodeGood (a :: l) ↔ O.CodeGood [a] ∧ O.CodeGood l := by
  rw [show a :: l = [a] ++ l from rfl, codeGood_append]

@[simp] theorem codeGood_single_plain (i : Instr) : O.CodeGood [.plain i] := by simp [CodeGood]
@[simp] theorem codeGood_single_trap : O.CodeGood [.trap] := by simp [CodeGood]
@[simp] theorem codeGood_single_ref (r : Ref) : O.CodeGood [.ref r] ↔ O.GoodRef r := by
  simp [CodeGood]
@[simp] theorem codeGood_single_callRefType (d : DefType) : O.CodeGood [.callRefType d] := by
  simp [CodeGood]
@[simp] theorem codeGood_single_returnCallRefType (d : DefType) :
    O.CodeGood [.returnCallRefType d] := by
  simp [CodeGood]
@[simp] theorem codeGood_single_label (n : Nat) (c : List Instr) (b : List Admin) :
    O.CodeGood [.label n c b] ↔ O.CodeGood b := by
  simp [CodeGood]
@[simp] theorem codeGood_single_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    O.CodeGood [.handler n cs b] ↔ O.CodeGood b := by
  simp [CodeGood]
@[simp] theorem codeGood_single_frame (n : Nat) (f : Frame) (b : List Admin) :
    O.CodeGood [.frame n f b] ↔ O.FrameGood f ∧ O.CodeGood b := by
  simp only [CodeGood, codeRefs_frame, codeRefs_nil, List.append_nil, codeFrames_frame,
    codeFrames_nil, List.mem_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 f (Or.inl rfl), h1, fun g hg => h2 g (Or.inr hg)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, fun g hg => hg.elim (fun e => e ▸ h1) (h3 g)⟩
@[simp] theorem codeGood_single_toAdmin (v : Val) : O.CodeGood [v.toAdmin] ↔ O.GoodVal v := by
  have := O.codeGood_vals (vs := [v])
  simpa [vals] using this

end Own

end Silmaril.Proofs.Wasm.Game.Linking.Split
