module

public import Silmaril.Wasm.Binaryen.InlHost

@[expose] public section

/-! # Appending a dead function: the relation

The module with one more defined function instantiates to the instance of the original
module with one more trailing `funcs` entry (`mext`), and to a store with one more function
instance at the end, whose existing function instances may have such extended instances.

* `FExt f g`: the frame `g` is `f` with its instance extended;
* `FL fs gs`: `gs` extends `fs`, with pointwise the same types and code, and extended
  instances (`FIRel`);
* `SRel s t`: `t` is `s` with its function list replaced by an `FL`-extension;
* `CRel`: code equal up to extended frames.

Related configurations step in lockstep (`InlDeadFuncSim.lean`). The only rules that can
tell the two stores apart are the negative reference tests, for a reference to the extra
function; references of typed configurations name existing functions (`RefsIn`,
`refsIn_of_configOk`).
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS

variable {H : Type}

/-! ## Extended instances and frames -/

/-- The instance `a` with the function addresses `l` appended. -/
def mext (a : ModuleInst) (l : List Nat) : ModuleInst := { a with funcs := a.funcs ++ l }

@[simp] theorem mext_types (a : ModuleInst) (l : List Nat) : (mext a l).types = a.types := rfl
@[simp] theorem mext_tags (a : ModuleInst) (l : List Nat) : (mext a l).tags = a.tags := rfl
@[simp] theorem mext_globals (a : ModuleInst) (l : List Nat) : (mext a l).globals = a.globals :=
  rfl
@[simp] theorem mext_mems (a : ModuleInst) (l : List Nat) : (mext a l).mems = a.mems := rfl
@[simp] theorem mext_tables (a : ModuleInst) (l : List Nat) : (mext a l).tables = a.tables := rfl
@[simp] theorem mext_datas (a : ModuleInst) (l : List Nat) : (mext a l).datas = a.datas := rfl
@[simp] theorem mext_elems (a : ModuleInst) (l : List Nat) : (mext a l).elems = a.elems := rfl
@[simp] theorem mext_exports (a : ModuleInst) (l : List Nat) : (mext a l).exports = a.exports :=
  rfl
@[simp] theorem mext_funcs (a : ModuleInst) (l : List Nat) : (mext a l).funcs = a.funcs ++ l :=
  rfl

@[simp] theorem mext_nil (a : ModuleInst) : mext a [] = a := by
  simp [mext]

theorem mext_mext (a : ModuleInst) (l l' : List Nat) : mext (mext a l) l' = mext a (l ++ l') := by
  simp [mext, List.append_assoc]

theorem mext_funcs_get {a : ModuleInst} {l : List Nat} {x b : Nat} (h : a.funcs[x]? = some b) :
    (mext a l).funcs[x]? = some b := by
  rw [mext_funcs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- `b` is `a` with function addresses appended. -/
def MExt (a b : ModuleInst) : Prop := ∃ l, b = mext a l

theorem MExt.refl (a : ModuleInst) : MExt a a := ⟨[], (mext_nil a).symm⟩

theorem MExt.trans {a b c : ModuleInst} (h₁ : MExt a b) (h₂ : MExt b c) : MExt a c := by
  obtain ⟨l, rfl⟩ := h₁
  obtain ⟨l', rfl⟩ := h₂
  exact ⟨l ++ l', mext_mext a l l'⟩

/-- The frame `f` with its instance extended by `l`. -/
def fext (f : Frame) (l : List Nat) : Frame := ⟨f.locals, mext f.module l⟩

@[simp] theorem fext_locals (f : Frame) (l : List Nat) : (fext f l).locals = f.locals := rfl
@[simp] theorem fext_module (f : Frame) (l : List Nat) : (fext f l).module = mext f.module l := rfl

@[simp] theorem fext_nil (f : Frame) : fext f [] = f := by
  simp [fext]

/-- `g` is `f` with its instance extended. -/
def FExt (f g : Frame) : Prop := ∃ l, g = fext f l

theorem FExt.refl (f : Frame) : FExt f f := ⟨[], (fext_nil f).symm⟩

theorem FExt.of_mext {f : Frame} {m : ModuleInst} (h : MExt f.module m) :
    FExt f ⟨f.locals, m⟩ := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨l, rfl⟩

theorem FExt.module {f g : Frame} (h : FExt f g) : MExt f.module g.module := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨l, rfl⟩

theorem FExt.locals {f g : Frame} (h : FExt f g) : g.locals = f.locals := by
  obtain ⟨l, rfl⟩ := h
  rfl

/-! ## Stores -/

/-- Function instances of the two stores at the same address. -/
structure FIRel (fi fi' : FuncInst H) : Prop where
  type : fi'.type = fi.type
  code : fi'.code = fi.code
  module : MExt fi.module fi'.module

theorem FIRel.refl (fi : FuncInst H) : FIRel fi fi := ⟨rfl, rfl, MExt.refl _⟩

/-- `gs` extends `fs` with related function instances. -/
def FL (fs gs : List (FuncInst H)) : Prop :=
  fs.length ≤ gs.length ∧
    ∀ (i : Nat) (fi : FuncInst H), fs[i]? = some fi → ∃ fi', gs[i]? = some fi' ∧ FIRel fi fi'

theorem FL.refl (fs : List (FuncInst H)) : FL fs fs :=
  ⟨le_refl _, fun _ fi h => ⟨fi, h, FIRel.refl fi⟩⟩

theorem FL.get {fs gs : List (FuncInst H)} (h : FL fs gs) {i : Nat} {fi : FuncInst H}
    (hi : fs[i]? = some fi) : ∃ fi', gs[i]? = some fi' ∧ FIRel fi fi' :=
  h.2 i fi hi

theorem FL.type {fs gs : List (FuncInst H)} (h : FL fs gs) {i : Nat} (hi : i < fs.length) :
    gs[i]?.map FuncInst.type = fs[i]?.map FuncInst.type := by
  obtain ⟨fi', h1, h2⟩ := h.get (List.getElem?_eq_getElem hi)
  rw [h1, List.getElem?_eq_getElem hi]
  simp [h2.type]

/-- Related stores: the same, but for the function instances. -/
def SRel (s t : Store H) : Prop := ∃ X, t = withFuncs s X ∧ FL s.funcs X

theorem SRel.refl (s : Store H) : SRel s s := ⟨s.funcs, rfl, FL.refl _⟩

/-! ## Code -/

mutual
/-- Related administrative instructions: equal, up to extended frames. -/
inductive ARel : Admin → Admin → Prop where
  | plain (i : Instr) : ARel (.plain i) (.plain i)
  | ref (r : Ref) : ARel (.ref r) (.ref r)
  | callRefType (d : DefType) : ARel (.callRefType d) (.callRefType d)
  | returnCallRefType (d : DefType) : ARel (.returnCallRefType d) (.returnCallRefType d)
  | trap : ARel .trap .trap
  | label {n : Nat} {cont : List Instr} {b b' : List Admin} (h : CRel b b') :
      ARel (.label n cont b) (.label n cont b')
  | handler {n : Nat} {cs : List Catch} {b b' : List Admin} (h : CRel b b') :
      ARel (.handler n cs b) (.handler n cs b')
  | frame {n : Nat} {f f' : Frame} {b b' : List Admin} (hf : FExt f f') (h : CRel b b') :
      ARel (.frame n f b) (.frame n f' b')
/-- Pointwise `ARel`. -/
inductive CRel : List Admin → List Admin → Prop where
  | nil : CRel [] []
  | cons {x y : Admin} {xs ys : List Admin} (h : ARel x y) (t : CRel xs ys) :
      CRel (x :: xs) (y :: ys)
end

/-- Related configurations. -/
def Rel (c c' : Config H) : Prop :=
  SRel c.store c'.store ∧ FExt c.frame c'.frame ∧ CRel c.code c'.code

mutual
theorem ARel.refl : ∀ a : Admin, ARel a a
  | .plain i => .plain i
  | .ref r => .ref r
  | .callRefType d => .callRefType d
  | .returnCallRefType d => .returnCallRefType d
  | .trap => .trap
  | .label _ _ b => .label (CRel.refl b)
  | .handler _ _ b => .handler (CRel.refl b)
  | .frame _ f b => .frame (FExt.refl f) (CRel.refl b)
theorem CRel.refl : ∀ l : List Admin, CRel l l
  | [] => .nil
  | a :: l => .cons (ARel.refl a) (CRel.refl l)
end

theorem CRel.append : ∀ {xs ys xs' ys' : List Admin}, CRel xs ys → CRel xs' ys' →
    CRel (xs ++ xs') (ys ++ ys')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha t, h => .cons ha (CRel.append t h)

theorem CRel.cons_inv {x : Admin} {xs ys : List Admin} (h : CRel (x :: xs) ys) :
    ∃ y ys', ys = y :: ys' ∧ ARel x y ∧ CRel xs ys' := by
  cases h with
  | cons ha t => exact ⟨_, _, rfl, ha, t⟩

theorem CRel.nil_inv {ys : List Admin} (h : CRel [] ys) : ys = [] := by
  cases h; rfl

theorem CRel.split : ∀ {xs xs' ys : List Admin}, CRel (xs ++ xs') ys →
    ∃ y₁ y₂, ys = y₁ ++ y₂ ∧ CRel xs y₁ ∧ CRel xs' y₂
  | [], _, ys, h => ⟨[], ys, rfl, .nil, h⟩
  | x :: xs, xs', ys, h => by
    obtain ⟨y, ys', rfl, ha, t⟩ := CRel.cons_inv h
    obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := CRel.split t
    exact ⟨y :: y₁, y₂, rfl, .cons ha h₁, h₂⟩

/-- Instructions with no body. -/
def isFlat : Admin → Bool
  | .label .. | .handler .. | .frame .. => false
  | _ => true

theorem ARel.eq_of_flat {x y : Admin} (h : ARel x y) (hx : isFlat x = true) : y = x := by
  cases h <;> first | rfl | simp [isFlat] at hx

theorem CRel.eq_of_flat : ∀ {xs ys : List Admin}, CRel xs ys → (∀ x ∈ xs, isFlat x = true) →
    ys = xs
  | _, _, .nil, _ => rfl
  | _, _, .cons ha t, hf => by
    rw [ARel.eq_of_flat ha (hf _ (List.mem_cons_self ..)),
      CRel.eq_of_flat t (fun x hx => hf x (List.mem_cons_of_mem _ hx))]

theorem ARel.eq_of_flat' {x y : Admin} (h : ARel x y) (hy : isFlat y = true) : y = x := by
  cases h <;> first | rfl | simp [isFlat] at hy

theorem CRel.eq_of_flat' : ∀ {xs ys : List Admin}, CRel xs ys → (∀ y ∈ ys, isFlat y = true) →
    ys = xs
  | _, _, .nil, _ => rfl
  | _, _, .cons ha t, hf => by
    rw [ARel.eq_of_flat' ha (hf _ (List.mem_cons_self ..)),
      CRel.eq_of_flat' t (fun x hx => hf x (List.mem_cons_of_mem _ hx))]

@[simp] theorem isFlat_toAdmin (v : Val) : isFlat v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

@[simp] theorem isFlat_plain (i : Instr) : isFlat (Admin.plain i) = true := rfl
@[simp] theorem isFlat_ref (r : Ref) : isFlat (Admin.ref r) = true := rfl
@[simp] theorem isFlat_trap : isFlat Admin.trap = true := rfl
@[simp] theorem isFlat_callRefType (d : DefType) : isFlat (Admin.callRefType d) = true := rfl
@[simp] theorem isFlat_returnCallRefType (d : DefType) :
    isFlat (Admin.returnCallRefType d) = true := rfl
@[simp] theorem isFlat_constI32 (b : BitVec 32) : isFlat (constI32 b) = true := rfl

theorem flat_vals (vs : List Val) : ∀ x ∈ vals vs, isFlat x = true := by
  intro x hx
  simp only [vals, List.mem_map] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact isFlat_toAdmin v

theorem flat_expression (is : List Instr) : ∀ x ∈ expression is, isFlat x = true := by
  intro x hx
  simp only [expression, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rfl

/-- All instructions are flat. -/
def allFlat (l : List Admin) : Bool := l.all isFlat

theorem allFlat_iff {l : List Admin} : allFlat l = true ↔ ∀ x ∈ l, isFlat x = true :=
  List.all_eq_true

@[simp] theorem allFlat_nil : allFlat [] = true := rfl
@[simp] theorem allFlat_cons (a : Admin) (l : List Admin) :
    allFlat (a :: l) = (isFlat a && allFlat l) := rfl
@[simp] theorem allFlat_append (l₁ l₂ : List Admin) :
    allFlat (l₁ ++ l₂) = (allFlat l₁ && allFlat l₂) := List.all_append
@[simp] theorem allFlat_vals (vs : List Val) : allFlat (vals vs) = true :=
  allFlat_iff.2 (flat_vals vs)
@[simp] theorem allFlat_expression (is : List Instr) : allFlat (expression is) = true :=
  allFlat_iff.2 (flat_expression is)

theorem CRel.vals_inv {vs : List Val} {ys : List Admin} (h : CRel (vals vs) ys) : ys = vals vs :=
  CRel.eq_of_flat h (flat_vals vs)

theorem isFlat_of_isCallRef {c : Admin} (h : c.IsCallRef) : isFlat c = true := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsCallRef, isFlat]

theorem isFlat_of_isReturnCallRef {c : Admin} (h : c.IsReturnCallRef) : isFlat c = true := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp_all [Admin.IsReturnCallRef, isFlat]

theorem ARel.label_inv {n : Nat} {cont : List Instr} {b : List Admin} {y : Admin}
    (h : ARel (.label n cont b) y) : ∃ b', y = .label n cont b' ∧ CRel b b' := by
  cases h with
  | label h => exact ⟨_, rfl, h⟩

theorem ARel.handler_inv {n : Nat} {cs : List Catch} {b : List Admin} {y : Admin}
    (h : ARel (.handler n cs b) y) : ∃ b', y = .handler n cs b' ∧ CRel b b' := by
  cases h with
  | handler h => exact ⟨_, rfl, h⟩

theorem ARel.frame_inv {n : Nat} {f : Frame} {b : List Admin} {y : Admin}
    (h : ARel (.frame n f b) y) : ∃ f' b', y = .frame n f' b' ∧ FExt f f' ∧ CRel b b' := by
  cases h with
  | frame hf h => exact ⟨_, _, rfl, hf, h⟩

/-- A one-element sequence: inversion. -/
theorem CRel.single_inv {x : Admin} {ys : List Admin} (h : CRel [x] ys) :
    ∃ y, ys = [y] ∧ ARel x y := by
  obtain ⟨y, ys', rfl, ha, t⟩ := CRel.cons_inv h
  rw [CRel.nil_inv t]
  exact ⟨y, rfl, ha⟩

theorem CRel.label_inv {n : Nat} {cont : List Instr} {b : List Admin} {ys : List Admin}
    (h : CRel [.label n cont b] ys) : ∃ b', ys = [.label n cont b'] ∧ CRel b b' := by
  obtain ⟨y, rfl, hy⟩ := CRel.single_inv h
  obtain ⟨b', rfl, hb⟩ := ARel.label_inv hy
  exact ⟨b', rfl, hb⟩

theorem CRel.handler_inv {n : Nat} {cs : List Catch} {b : List Admin} {ys : List Admin}
    (h : CRel [.handler n cs b] ys) : ∃ b', ys = [.handler n cs b'] ∧ CRel b b' := by
  obtain ⟨y, rfl, hy⟩ := CRel.single_inv h
  obtain ⟨b', rfl, hb⟩ := ARel.handler_inv hy
  exact ⟨b', rfl, hb⟩

theorem CRel.frame_inv {n : Nat} {f : Frame} {b : List Admin} {ys : List Admin}
    (h : CRel [.frame n f b] ys) : ∃ f' b', ys = [.frame n f' b'] ∧ FExt f f' ∧ CRel b b' := by
  obtain ⟨y, rfl, hy⟩ := CRel.single_inv h
  obtain ⟨f', b', rfl, hf, hb⟩ := ARel.frame_inv hy
  exact ⟨f', b', rfl, hf, hb⟩

/-- A flat prefix followed by anything. -/
theorem CRel.flat_append {xs rest ys : List Admin} (h : CRel (xs ++ rest) ys)
    (hf : ∀ x ∈ xs, isFlat x = true) : ∃ rest', ys = xs ++ rest' ∧ CRel rest rest' := by
  obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := CRel.split h
  rw [CRel.eq_of_flat h₁ hf]
  exact ⟨y₂, rfl, h₂⟩

/-! ## References of typed configurations -/

/-- A reference that names an existing function (of `n` functions). -/
def RefIn (n : Nat) : Ref → Prop
  | .func a => a < n
  | .extern r => RefIn n r
  | _ => True

/-- The reference `r` occurs in the administrative instruction. -/
inductive AOcc (r : Ref) : Admin → Prop where
  | ref : AOcc r (.ref r)
  | label {n : Nat} {cont : List Instr} {b : List Admin} {a : Admin} (hm : a ∈ b) (h : AOcc r a) :
      AOcc r (.label n cont b)
  | handler {n : Nat} {cs : List Catch} {b : List Admin} {a : Admin} (hm : a ∈ b)
      (h : AOcc r a) : AOcc r (.handler n cs b)
  | frame {n : Nat} {f : Frame} {b : List Admin} {a : Admin} (hm : a ∈ b) (h : AOcc r a) :
      AOcc r (.frame n f b)

/-- Every reference in the code names an existing function. -/
def RefsIn (n : Nat) (code : List Admin) : Prop := ∀ a ∈ code, ∀ r, AOcc r a → RefIn n r

theorem RefsIn.mono {n : Nat} {xs ys : List Admin} (h : RefsIn n ys) (hs : ∀ a ∈ xs, a ∈ ys) :
    RefsIn n xs := fun a ha => h a (hs a ha)

theorem RefsIn.label {n k : Nat} {cont : List Instr} {b : List Admin}
    (h : RefsIn n [.label k cont b]) : RefsIn n b :=
  fun _ ha r hr => h _ (List.mem_singleton_self _) r (.label ha hr)

theorem RefsIn.handler {n k : Nat} {cs : List Catch} {b : List Admin}
    (h : RefsIn n [.handler k cs b]) : RefsIn n b :=
  fun _ ha r hr => h _ (List.mem_singleton_self _) r (.handler ha hr)

theorem RefsIn.frame {n k : Nat} {f : Frame} {b : List Admin}
    (h : RefsIn n [.frame k f b]) : RefsIn n b :=
  fun _ ha r hr => h _ (List.mem_singleton_self _) r (.frame ha hr)

theorem RefsIn.ref {n : Nat} {code : List Admin} {r : Ref} (h : RefsIn n code)
    (hm : Admin.ref r ∈ code) : RefIn n r :=
  h _ hm r .ref

theorem refIn_of_refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    RefIn s.funcs.length r := by
  induction h with
  | func h => exact (List.getElem?_eq_some_iff.mp h).1
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

theorem AOcc.not_plain {r : Ref} {i : Instr} (h : AOcc r (.plain i)) : False := by
  cases h

mutual
theorem AdminOk.refsIn {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it →
      ∀ r, AOcc r a → RefIn s.funcs.length r
  | _, _, _, .plain _, _, h => nomatch h
  | _, _, _, .callRefType _ _, _, h => nomatch h
  | _, _, _, .returnCallRefType _ _ _ _ _, _, h => nomatch h
  | _, _, _, .ref h, _, .ref => refIn_of_refOk h
  | _, _, _, .label _ _ hb, r, .label hm h => AdminsOk.refsIn hb _ hm r h
  | _, _, _, .frame _ _ hb _, r, .frame hm h => AdminsOk.refsIn hb _ hm r h
  | _, _, _, .handler _ hb, r, .handler hm h => AdminsOk.refsIn hb _ hm r h
  | _, _, _, .trap _, _, h => nomatch h
  | _, _, _, .throwRefInits _, _, h => nomatch h
theorem AdminsOk.refsIn {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
      ∀ a ∈ as, ∀ r, AOcc r a → RefIn s.funcs.length r
  | _, _, _, .nil, _, ha, _, _ => nomatch ha
  | _, _, _, .single h, _, ha, r, hr => AdminOk.refsIn h r (List.mem_singleton.mp ha ▸ hr)
  | _, _, _, .seq h₁ _ h₂, a, ha, r, hr =>
    (List.mem_append.mp ha).elim (fun ha => AdminsOk.refsIn h₁ a ha r hr)
      (fun ha => AdminsOk.refsIn h₂ a ha r hr)
  | _, _, _, .cons h₁ _ h₂, a, ha, r, hr =>
    (List.mem_cons.mp ha).elim (fun e => AdminOk.refsIn h₁ r (e ▸ hr))
      (fun ha => AdminsOk.refsIn h₂ a ha r hr)
  | _, _, _, .sub h _ _, a, ha, r, hr => AdminsOk.refsIn h a ha r hr
  | _, _, _, .frame h _, a, ha, r, hr => AdminsOk.refsIn h a ha r hr
end

/-- **The references of a typed configuration name existing functions.** -/
theorem refsIn_of_configOk {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    RefsIn c.store.funcs.length c.code := by
  obtain ⟨C, -, hc⟩ := h
  exact AdminsOk.refsIn hc

/-! ## Reference typing in related stores -/

theorem refOk_fl {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {r : Ref}
    {rt : CRefType} (h : RefOk s r rt) : RefOk (withFuncs s X) r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
    obtain ⟨fi', h1, h2⟩ := hX.get h
    rw [← h2.type]
    exact .func h1
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_fl_back {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {r : Ref}
    {rt : CRefType} (h : RefOk (withFuncs s X) r rt) (hr : RefIn s.funcs.length r) :
    RefOk s r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | @func a fi h =>
    have ha : a < s.funcs.length := hr
    obtain ⟨fi', h1, h2⟩ := hX.get (List.getElem?_eq_getElem ha)
    have h1' : X[a]? = some fi := h
    rw [h1'] at h1
    cases h1
    rw [h2.type]
    exact .func (List.getElem?_eq_getElem ha)
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern (ih hr) hn
  | sub _ hok hs ih => exact .sub (ih hr) hok hs

theorem refOk_fl_iff {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {r : Ref}
    (hr : RefIn s.funcs.length r) {rt : CRefType} :
    RefOk (withFuncs s X) r rt ↔ RefOk s r rt :=
  ⟨fun h => refOk_fl_back hX h hr, refOk_fl hX⟩

theorem valOk_fl {s : Store H} {X : List (FuncInst H)} (hX : FL s.funcs X) {v : Val}
    {t : CValType} (h : ValOk s v t) : ValOk (withFuncs s X) v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (refOk_fl hX h)

end Silmaril.Wasm.Binaryen.InlDF
