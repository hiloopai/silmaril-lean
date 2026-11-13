module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# Global-address embeddings of stores and configurations

The specification's `$instantiate` allocates every global twice (`$evalglobals`,
then `$allocmodule`), and the module instance names the second copies; silmaril-lean's
`instantiateOnce?` allocates each global once. The two stores agree up to an
**injective** map `ρ` of global addresses: the once-store's global `a` is the spec
store's global `ρ a`, and the spec store has further, unreachable globals.

* `moduleView ρ`, `frame ρ`, `function ρ`, `admins ρ`, `config ρ t c`: rename the global
  addresses of module instances (their `globals` and global exports), everywhere in a
  configuration (nested frames included) and in every function instance;
* `Emb ρ D s t`: the store `t` is the store `s` with global `a` at `ρ a` for every `a` in
  the domain `D` (`ρ` injective on `D`), every other component equal and every function
  instance renamed; the module instances of `s` only name globals in `D` (`ModDom`);
* `CfgDom D c`: the module instances of the frames of `c` (nested frames included) only
  name globals in `D`.

With `D` everything (`Emb ρ ⊤`), `ρ` is a global embedding of the once-store into the
spec store; with `D` the range of an embedding `ι` and `ρ` a left inverse of `ι`, the
reverse direction: the unreachable globals are outside `D`.

The definitions follow silmaril-lean's `Silmaril.Wasm.Link.GC.GlobalPermutation`
(`moduleView`, `frame`, `function`, `Renamed`), with the permutation `Nat ≃ Nat`
replaced by an arbitrary map, a domain, and the renaming applied to every function
(host functions included). New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The full domain. -/
abbrev Univ : Nat → Prop := fun _ => True

/-- Rename a global external address. -/
def external (ρ : Nat → Nat) : ExternAddr → ExternAddr
  | .global a => .global (ρ a)
  | other => other

/-- Rename the global addresses of a module instance (its globals and global exports). -/
def moduleView (ρ : Nat → Nat) (m : ModuleInst) : ModuleInst :=
  { m with
    globals := m.globals.map ρ
    exports := m.exports.map fun e => { e with addr := external ρ e.addr } }

/-- Rename the global addresses of a frame's module instance. -/
def frame (ρ : Nat → Nat) (f : Frame) : Frame :=
  { f with module := moduleView ρ f.module }

/-- Rename the global addresses of a function's module instance. -/
def function (ρ : Nat → Nat) (fi : FuncInst H) : FuncInst H :=
  { fi with module := moduleView ρ fi.module }

mutual
/-- Rename the global addresses of the frames of an administrative instruction. -/
def admin (ρ : Nat → Nat) : Admin → Admin
  | .label n cont body => .label n cont (admins ρ body)
  | .handler n catches body => .handler n catches (admins ρ body)
  | .frame n f body => .frame n (frame ρ f) (admins ρ body)
  | .plain i => .plain i
  | .ref r => .ref r
  | .callRefType d => .callRefType d
  | .returnCallRefType d => .returnCallRefType d
  | .trap => .trap

/-- Rename the global addresses of the frames of a code sequence. -/
def admins (ρ : Nat → Nat) : List Admin → List Admin
  | [] => []
  | a :: rest => admin ρ a :: admins ρ rest
end

/-- Rename the frames of a configuration and replace its store. -/
def config (ρ : Nat → Nat) (t : Store H) (c : Config H) : Config H :=
  ⟨t, frame ρ c.frame, admins ρ c.code⟩

/-- The global addresses named by a module instance lie in `D`. -/
def ModDom (D : Nat → Prop) (m : ModuleInst) : Prop :=
  (∀ a ∈ m.globals, D a) ∧ ∀ e ∈ m.exports, ∀ a, e.addr = .global a → D a

mutual
/-- The frames of an administrative instruction only name globals in `D`. -/
def AdminDom (D : Nat → Prop) : Admin → Prop
  | .label _ _ body => AdminsDom D body
  | .handler _ _ body => AdminsDom D body
  | .frame _ f body => ModDom D f.module ∧ AdminsDom D body
  | .plain _ => True
  | .ref _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | .trap => True

/-- The frames of a code sequence only name globals in `D`. -/
def AdminsDom (D : Nat → Prop) : List Admin → Prop
  | [] => True
  | a :: rest => AdminDom D a ∧ AdminsDom D rest
end

/-- The frames of a configuration only name globals in `D`. -/
abbrev CfgDom (D : Nat → Prop) (c : Config H) : Prop :=
  ModDom D c.frame.module ∧ AdminsDom D c.code

/-- **Global embedding of stores**: `t` is `s` with the global `a` at `ρ a` for `a ∈ D`
(`ρ` injective on `D`), every function renamed, the other components equal; the module
instances of the functions of `s` only name globals in `D`. -/
structure Emb (ρ : Nat → Nat) (D : Nat → Prop) (s t : Store H) : Prop where
  globals : ∀ a, D a → t.globals[ρ a]? = s.globals[a]?
  inj : ∀ a b, D a → D b → ρ a = ρ b → a = b
  funcs : t.funcs = s.funcs.map (function ρ)
  fdom : ∀ fi ∈ s.funcs, ModDom D fi.module
  tags : s.tags = t.tags
  mems : s.mems = t.mems
  tables : s.tables = t.tables
  datas : s.datas = t.datas
  elems : s.elems = t.elems
  structs : s.structs = t.structs
  arrays : s.arrays = t.arrays
  exns : s.exns = t.exns

/-! ## Renaming code -/

@[simp] theorem admin_value (ρ : Nat → Nat) (v : Val) : admin ρ v.toAdmin = v.toAdmin := by
  cases v with
  | num n => cases n with | mk t b => cases t <;> rfl
  | vec b => rfl
  | ref r => rfl

@[simp] theorem admins_nil (ρ : Nat → Nat) : admins ρ [] = [] := rfl

@[simp] theorem admins_cons (ρ : Nat → Nat) (a : Admin) (l : List Admin) :
    admins ρ (a :: l) = admin ρ a :: admins ρ l := rfl

@[simp] theorem admins_append (ρ : Nat → Nat) (xs ys : List Admin) :
    admins ρ (xs ++ ys) = admins ρ xs ++ admins ρ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, admins, ih]

@[simp] theorem admins_vals (ρ : Nat → Nat) (vs : List Val) : admins ρ (vals vs) = vals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, admins, admin_value]
    exact congrArg (List.cons v.toAdmin) ih

@[simp] theorem admins_expression (ρ : Nat → Nat) (code : List Instr) :
    admins ρ (expression code) = expression code := by
  induction code with
  | nil => rfl
  | cons i code ih =>
    simp only [expression, List.map_cons, admins, admin]
    exact congrArg (List.cons (.plain i)) ih

@[simp] theorem admins_refs (ρ : Nat → Nat) (refs : List Ref) :
    admins ρ (refs.map Admin.ref) = refs.map Admin.ref := by
  induction refs with
  | nil => rfl
  | cons r refs ih =>
    simp only [List.map_cons, admins, admin]
    exact congrArg (List.cons (.ref r)) ih

@[simp] theorem admins_length (ρ : Nat → Nat) (code : List Admin) :
    (admins ρ code).length = code.length := by
  induction code with
  | nil => rfl
  | cons i code ih => simp only [admins, List.length_cons, ih]

@[simp] theorem admins_result (ρ : Nat → Nat) (r : Result) : admins ρ r.toAdmin = r.toAdmin := by
  cases r with
  | values vs => exact admins_vals ρ vs
  | throw a => rfl
  | trap => rfl

theorem admins_ne_nil {ρ : Nat → Nat} {code : List Admin} (h : code ≠ []) : admins ρ code ≠ [] := by
  intro e
  have hl := congrArg List.length e
  rw [admins_length, List.length_nil, List.length_eq_zero_iff] at hl
  exact h hl

/-! ## Composition and inverses -/

theorem external_comp (ρ σ : Nat → Nat) (x : ExternAddr) :
    external σ (external ρ x) = external (σ ∘ ρ) x := by
  cases x <;> rfl

theorem moduleView_comp (ρ σ : Nat → Nat) (m : ModuleInst) :
    moduleView σ (moduleView ρ m) = moduleView (σ ∘ ρ) m := by
  have hx : ((fun e : ExportInst => { e with addr := external σ e.addr }) ∘
      fun e : ExportInst => { e with addr := external ρ e.addr }) =
      fun e => { e with addr := external (σ ∘ ρ) e.addr } := by
    funext e
    simp only [Function.comp_apply, external_comp]
  simp only [moduleView, List.map_map, hx]

theorem moduleView_id (m : ModuleInst) : moduleView id m = m := by
  have he : ∀ x : ExternAddr, external id x = x := fun x => by cases x <;> rfl
  have hx : (fun e : ExportInst => { e with addr := external id e.addr }) = id := by
    funext e
    simp only [he, id_eq]
  cases m
  simp only [moduleView, List.map_id_fun, id_eq, hx]

theorem moduleView_congr {ρ σ : Nat → Nat} {D : Nat → Prop} {m : ModuleInst} (hm : ModDom D m)
    (h : ∀ a, D a → ρ a = σ a) : moduleView ρ m = moduleView σ m := by
  have hg : m.globals.map ρ = m.globals.map σ :=
    List.map_congr_left fun a ha => h a (hm.1 a ha)
  have hx : m.exports.map (fun e => { e with addr := external ρ e.addr }) =
      m.exports.map (fun e => { e with addr := external σ e.addr }) := by
    refine List.map_congr_left fun e he => ?_
    cases hx : e.addr with
    | global a =>
      have hd : D a := hm.2 e he a hx
      simp only [external, h a hd]
    | _ => simp only [external]
  simp only [moduleView, hg, hx]

/-- Renaming by a left inverse after a renaming that names only images undoes it. -/
theorem moduleView_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) (m : ModuleInst) :
    moduleView κ (moduleView ι m) = m := by
  rw [moduleView_comp]
  have h : κ ∘ ι = id := funext hκ
  rw [h, moduleView_id]

/-- Renaming back a module instance whose globals are images. -/
theorem moduleView_inv' {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) {m : ModuleInst}
    (hm : ModDom (fun b => ∃ a, ι a = b) m) : moduleView ι (moduleView κ m) = m := by
  rw [moduleView_comp, moduleView_congr hm (σ := id), moduleView_id]
  rintro _ ⟨a, rfl⟩
  simp only [Function.comp_apply, hκ, id_eq]

theorem frame_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) (f : Frame) :
    frame κ (frame ι f) = f := by
  simp only [frame, moduleView_inv hκ]

theorem function_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) (fi : FuncInst H) :
    function κ (function ι fi) = fi := by
  simp only [function, moduleView_inv hκ]

mutual
theorem admin_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) :
    ∀ a : Admin, admin κ (admin ι a) = a
  | .label n cont body => by simp only [admin, admins_inv hκ body]
  | .handler n cs body => by simp only [admin, admins_inv hκ body]
  | .frame n f body => by simp only [admin, admins_inv hκ body, frame_inv hκ f]
  | .plain _ => rfl
  | .ref _ => rfl
  | .callRefType _ => rfl
  | .returnCallRefType _ => rfl
  | .trap => rfl

theorem admins_inv {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) :
    ∀ l : List Admin, admins κ (admins ι l) = l
  | [] => rfl
  | a :: l => by simp only [admins, admin_inv hκ a, admins_inv hκ l]
end

/-- The range of `ι`. -/
def Img (ι : Nat → Nat) : Nat → Prop := fun b => ∃ a, ι a = b

mutual
theorem admin_inv' {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) :
    ∀ a : Admin, AdminDom (Img ι) a → admin ι (admin κ a) = a
  | .label n cont body, h => by simp only [admin, admins_inv' hκ body h]
  | .handler n cs body, h => by simp only [admin, admins_inv' hκ body h]
  | .frame n f body, h => by
    simp only [admin, admins_inv' hκ body h.2, frame, moduleView_inv' hκ h.1]
  | .plain _, _ => rfl
  | .ref _, _ => rfl
  | .callRefType _, _ => rfl
  | .returnCallRefType _, _ => rfl
  | .trap, _ => rfl

theorem admins_inv' {ι κ : Nat → Nat} (hκ : ∀ a, κ (ι a) = a) :
    ∀ l : List Admin, AdminsDom (Img ι) l → admins ι (admins κ l) = l
  | [], _ => rfl
  | a :: l, h => by simp only [admins, admin_inv' hκ a h.1, admins_inv' hκ l h.2]
end

/-! ## Domains -/

theorem modDom_univ (m : ModuleInst) : ModDom (fun _ => True) m :=
  ⟨fun _ _ => trivial, fun _ _ _ _ => trivial⟩

theorem modDom_img (ι : Nat → Nat) (m : ModuleInst) : ModDom (Img ι) (moduleView ι m) := by
  refine ⟨fun a ha => ?_, fun e he a ha => ?_⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact ⟨b, rfl⟩
  · obtain ⟨e', -, rfl⟩ := List.mem_map.1 he
    cases hx : e'.addr with
    | global b =>
      simp only [hx, external, ExternAddr.global.injEq] at ha
      exact ⟨b, ha⟩
    | _ => simp only [hx, external, reduceCtorEq] at ha

mutual
theorem adminDom_univ : ∀ a : Admin, AdminDom (fun _ => True) a
  | .label _ _ body => adminsDom_univ body
  | .handler _ _ body => adminsDom_univ body
  | .frame _ f body => ⟨modDom_univ f.module, adminsDom_univ body⟩
  | .plain _ => trivial
  | .ref _ => trivial
  | .callRefType _ => trivial
  | .returnCallRefType _ => trivial
  | .trap => trivial

theorem adminsDom_univ : ∀ l : List Admin, AdminsDom (fun _ => True) l
  | [] => trivial
  | a :: l => ⟨adminDom_univ a, adminsDom_univ l⟩
end

mutual
theorem adminDom_img (ι : Nat → Nat) : ∀ a : Admin, AdminDom (Img ι) (admin ι a)
  | .label _ _ body => adminsDom_img ι body
  | .handler _ _ body => adminsDom_img ι body
  | .frame _ f body => ⟨modDom_img ι f.module, adminsDom_img ι body⟩
  | .plain _ => trivial
  | .ref _ => trivial
  | .callRefType _ => trivial
  | .returnCallRefType _ => trivial
  | .trap => trivial

theorem adminsDom_img (ι : Nat → Nat) : ∀ l : List Admin, AdminsDom (Img ι) (admins ι l)
  | [] => trivial
  | a :: l => ⟨adminDom_img ι a, adminsDom_img ι l⟩
end

@[simp] theorem adminsDom_nil (D : Nat → Prop) : AdminsDom D [] := trivial

@[simp] theorem adminsDom_cons (D : Nat → Prop) (a : Admin) (l : List Admin) :
    AdminsDom D (a :: l) ↔ AdminDom D a ∧ AdminsDom D l := Iff.rfl

@[simp] theorem adminsDom_append (D : Nat → Prop) (xs ys : List Admin) :
    AdminsDom D (xs ++ ys) ↔ AdminsDom D xs ∧ AdminsDom D ys := by
  induction xs with
  | nil => simp only [List.nil_append, adminsDom_nil, true_and]
  | cons x xs ih => simp only [List.cons_append, adminsDom_cons, ih, and_assoc]

@[simp] theorem adminDom_value (D : Nat → Prop) (v : Val) : AdminDom D v.toAdmin := by
  cases v with
  | num n => cases n with | mk t b => cases t <;> trivial
  | vec b => trivial
  | ref r => trivial

@[simp] theorem adminsDom_vals (D : Nat → Prop) (vs : List Val) : AdminsDom D (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨adminDom_value D v, ih⟩

@[simp] theorem adminsDom_refs (D : Nat → Prop) (refs : List Ref) :
    AdminsDom D (refs.map Admin.ref) := by
  induction refs with
  | nil => trivial
  | cons r refs ih => exact ⟨trivial, ih⟩

@[simp] theorem adminsDom_expression (D : Nat → Prop) (code : List Instr) :
    AdminsDom D (expression code) := by
  induction code with
  | nil => trivial
  | cons i code ih => exact ⟨trivial, ih⟩

@[simp] theorem adminsDom_result (D : Nat → Prop) (r : Result) : AdminsDom D r.toAdmin := by
  cases r with
  | values vs => exact adminsDom_vals D vs
  | throw a => exact ⟨trivial, trivial, trivial⟩
  | trap => exact ⟨trivial, trivial⟩

@[simp] theorem adminDom_label (D : Nat → Prop) (n : Nat) (cont : List Instr) (body : List Admin) :
    AdminDom D (.label n cont body) ↔ AdminsDom D body := Iff.rfl

@[simp] theorem adminDom_handler (D : Nat → Prop) (n : Nat) (cs : List Catch) (body : List Admin) :
    AdminDom D (.handler n cs body) ↔ AdminsDom D body := Iff.rfl

@[simp] theorem adminDom_frame (D : Nat → Prop) (n : Nat) (f : Frame) (body : List Admin) :
    AdminDom D (.frame n f body) ↔ ModDom D f.module ∧ AdminsDom D body := Iff.rfl

@[simp] theorem adminDom_plain (D : Nat → Prop) (i : Instr) : AdminDom D (.plain i) := trivial

@[simp] theorem adminDom_ref (D : Nat → Prop) (r : Ref) : AdminDom D (.ref r) := trivial

@[simp] theorem adminDom_callRefType (D : Nat → Prop) (d : DefType) :
    AdminDom D (.callRefType d) := trivial

@[simp] theorem adminDom_returnCallRefType (D : Nat → Prop) (d : DefType) :
    AdminDom D (.returnCallRefType d) := trivial

@[simp] theorem adminDom_trap (D : Nat → Prop) : AdminDom D .trap := trivial

/-! ## Store lemmas -/

namespace Emb

variable {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H}

theorem func_lookup (h : Emb ρ D s t) {a : Nat} {fi : FuncInst H} (hf : s.funcs[a]? = some fi) :
    t.funcs[a]? = some (function ρ fi) := by
  simp only [h.funcs, List.getElem?_map, hf, Option.map_some]

theorem func_lookup' (h : Emb ρ D s t) {a : Nat} {gi : FuncInst H} (hg : t.funcs[a]? = some gi) :
    ∃ fi, s.funcs[a]? = some fi ∧ gi = function ρ fi := by
  rw [h.funcs, List.getElem?_map] at hg
  cases hf : s.funcs[a]? with
  | none => simp only [hf, Option.map_none, reduceCtorEq] at hg
  | some fi =>
    simp only [hf, Option.map_some, Option.some.injEq] at hg
    exact ⟨fi, rfl, hg.symm⟩

theorem func_types (h : Emb ρ D s t) (a : Nat) :
    s.funcs[a]?.map FuncInst.type = t.funcs[a]?.map FuncInst.type := by
  simp only [h.funcs, List.getElem?_map, Option.map_map]
  rfl

theorem funcs_length (h : Emb ρ D s t) : t.funcs.length = s.funcs.length := by
  rw [h.funcs, List.length_map]

theorem refOk {r : Ref} {τ : CRefType} (h : Emb ρ D s t) (valid : RefOk s r τ) : RefOk t r τ := by
  induction valid with
  | null => exact .null
  | i31 bits => exact .i31 bits
  | struct lookup => exact .struct (h.structs ▸ lookup)
  | array lookup => exact .array (h.arrays ▸ lookup)
  | func lookup => exact .func (fi := function ρ _) (h.func_lookup lookup)
  | exn lookup => exact .exn (h.exns ▸ lookup)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_back {r : Ref} {τ : CRefType} (h : Emb ρ D s t) (valid : RefOk t r τ) :
    RefOk s r τ := by
  induction valid with
  | null => exact .null
  | i31 bits => exact .i31 bits
  | struct lookup => exact .struct (h.structs ▸ lookup)
  | array lookup => exact .array (h.arrays ▸ lookup)
  | func lookup =>
    obtain ⟨fi, hf, rfl⟩ := h.func_lookup' lookup
    exact RefOk.func (fi := fi) hf
  | exn lookup => exact .exn (h.exns ▸ lookup)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_iff (h : Emb ρ D s t) (r : Ref) (τ : CRefType) : RefOk s r τ ↔ RefOk t r τ :=
  ⟨h.refOk, h.refOk_back⟩

theorem setGlobal (h : Emb ρ D s t) {a : Nat} (ha : D a) (v : Val) :
    Emb ρ D (s.setGlobal a v) (t.setGlobal (ρ a) v) where
  globals b hb := by
    simp only [Store.setGlobal, List.getElem?_modify, h.globals b hb]
    by_cases e : a = b
    · subst e; simp only [ite_true]
    · have e' : ρ a ≠ ρ b := fun he => e (h.inj a b ha hb he)
      simp only [e, e', ite_false]
  inj := h.inj
  funcs := h.funcs
  fdom := h.fdom
  tags := h.tags
  mems := h.mems
  tables := h.tables
  datas := h.datas
  elems := h.elems
  structs := h.structs
  arrays := h.arrays
  exns := h.exns

theorem setMem (h : Emb ρ D s t) (a : Nat) (v : MemInst) :
    Emb ρ D (s.setMem a v) (t.setMem a v) :=
  { h with mems := congrArg (fun ms => ms.set a v) h.mems }

theorem setTable (h : Emb ρ D s t) (a : Nat) (v : TableInst) :
    Emb ρ D (s.setTable a v) (t.setTable a v) :=
  { h with tables := congrArg (fun ts => ts.set a v) h.tables }

theorem setElem (h : Emb ρ D s t) (a : Nat) (refs : List Ref) :
    Emb ρ D (s.setElem a refs) (t.setElem a refs) :=
  { h with elems := congrArg (fun es => es.modify a (fun e => { e with refs := refs })) h.elems }

theorem setData (h : Emb ρ D s t) (a : Nat) (bytes : ByteArray) :
    Emb ρ D (s.setData a bytes) (t.setData a bytes) :=
  { h with datas := congrArg (fun ds => ds.modify a (fun _ => ⟨bytes⟩)) h.datas }

theorem setStructField (h : Emb ρ D s t) (a i : Nat) (v : FieldVal) :
    Emb ρ D (s.setStructField a i v) (t.setStructField a i v) :=
  have e : (s.setStructField a i v).structs = (t.setStructField a i v).structs := by
    simp only [Store.setStructField, h.structs]
  { h with structs := e }

theorem setArrayField (h : Emb ρ D s t) (a i : Nat) (v : FieldVal) :
    Emb ρ D (s.setArrayField a i v) (t.setArrayField a i v) :=
  have e : (s.setArrayField a i v).arrays = (t.setArrayField a i v).arrays := by
    simp only [Store.setArrayField, h.arrays]
  { h with arrays := e }

theorem addStruct (h : Emb ρ D s t) (v : StructInst) :
    Emb ρ D (s.addStruct v) (t.addStruct v) :=
  { h with structs := congrArg (fun ss => ss ++ [v]) h.structs }

theorem addArray (h : Emb ρ D s t) (v : ArrayInst) :
    Emb ρ D (s.addArray v) (t.addArray v) :=
  { h with arrays := congrArg (fun ss => ss ++ [v]) h.arrays }

theorem addExn (h : Emb ρ D s t) (v : ExnInst) :
    Emb ρ D (s.addExn v) (t.addExn v) :=
  { h with exns := congrArg (fun es => es ++ [v]) h.exns }

/-- A global lookup through a frame naming globals in `D`. -/
theorem global_lookup (h : Emb ρ D s t) {f : Frame} (hf : ModDom D f.module) {x : GlobalIdx}
    {a : Nat} {g : GlobalInst} (lookup : s.global? f x = some (a, g)) :
    t.global? (frame ρ f) x = some (ρ a, g) ∧ D a := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff] at lookup
  obtain ⟨a', ha, g', hg, he⟩ := lookup
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hd : D a' := hf.1 a' (List.mem_of_getElem? ha)
  refine ⟨?_, hd⟩
  simp only [Store.global?, frame, moduleView, List.getElem?_map, ha, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, h.globals a' hd, hg, Option.pure_def]

end Emb

end Silmaril.Proofs.Wasm.Game.SpecGlobals
