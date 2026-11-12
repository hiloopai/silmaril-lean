module

public import Silmaril.Wasm.Wac.Bridge.Encode.Defs
public import Silmaril.Wasm.Wac.Bridge.Graph.Defs

/-!
# WAC bridge: type scopes only add type definitions

`Pres m`: a type-scope computation `m` that succeeds only appends type definitions to
the scope's declarations, increases the type count by their number, and keeps the
sharing flag. Every computation that types an item (`valTy`, `funcTy`, `externDesc`,
`typeBound`, `worldDef`, `ifaceDef`, `defnTy`) has it (`Pres.externDesc`, …); nested scopes do not
touch the enclosing one.

`Ret.externDesc`: the descriptor of a kind has the kind's sort. `externDesc_inst`:
without sharing, an instance kind is one new instance type, whose function exports are
the kind's function exports, in order (`exportDecls_ifuncs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)

/-- `s'` extends `s` by type definitions only. -/
def TInv (s s' : Scope) : Prop :=
  ∃ ts : List DefType, s'.decls = s.decls ++ ts.map (fun d => .inst (.type d)) ∧
    s'.ntypes = s.ntypes + ts.length ∧ s'.share = s.share

theorem TInv.refl (s : Scope) : TInv s s := ⟨[], by simp, by simp, rfl⟩

theorem TInv.trans {s₁ s₂ s₃ : Scope} (h₁ : TInv s₁ s₂) (h₂ : TInv s₂ s₃) : TInv s₁ s₃ := by
  obtain ⟨ts, hd, hn, hs⟩ := h₁
  obtain ⟨us, hd', hn', hs'⟩ := h₂
  refine ⟨ts ++ us, ?_, ?_, hs'.trans hs⟩
  · rw [hd', hd, List.map_append, List.append_assoc]
  · rw [hn', hn, List.length_append, Nat.add_assoc]

/-- A computation that only adds type definitions. -/
def Pres {α : Type} (m : TM α) : Prop := ∀ s a s', m.run s = .ok (a, s') → TInv s s'

theorem Pres.pure {α : Type} (a : α) : Pres (Pure.pure a : TM α) := by
  intro s b s' h
  have : s' = s := by cases h; rfl
  rw [this]; exact TInv.refl s

theorem Pres.bind {α β : Type} {m : TM α} {f : α → TM β} (hm : Pres m) (hf : ∀ a, Pres (f a)) :
    Pres (m >>= f) := by
  intro s b s' h
  rw [StateT.run_bind] at h
  cases hr : m.run s with
  | error e => rw [hr] at h; cases h
  | ok p => rw [hr] at h; exact (hm s p.1 p.2 hr).trans (hf p.1 p.2 b s' h)

theorem Pres.get : Pres (MonadState.get : TM Scope) := by
  intro s b s' h
  have : s' = s := by cases h; rfl
  rw [this]; exact TInv.refl s

theorem Pres.throw {α : Type} (e : String) : Pres (throw e : TM α) := by
  intro s b s' h; cases h

/-- A state change that keeps the declarations, the type count and the sharing flag. -/
theorem Pres.modify {f : Scope → Scope}
    (hf : ∀ s, (f s).decls = s.decls ∧ (f s).ntypes = s.ntypes ∧ (f s).share = s.share) :
    Pres (modify f : TM Unit) := by
  intro s b s' h
  have : s' = f s := by cases h; rfl
  obtain ⟨hd, hn, hs⟩ := hf s
  rw [this]; exact ⟨[], by simp [hd], by simp [hn], hs⟩

theorem Pres.defTy (d : DefType) : Pres (Bridge.defTy d) := by
  intro s b s' h
  have : s' = { s with decls := s.decls ++ [.inst (.type d)], ntypes := s.ntypes + 1 } := by
    cases h; rfl
  rw [this]; exact ⟨[d], rfl, rfl, rfl⟩

theorem Pres.namedTy (n : String) : Pres (Bridge.namedTy n) := by
  unfold Bridge.namedTy
  refine Pres.bind Pres.get fun s => ?_
  split
  · exact Pres.pure _
  · exact Pres.throw _

theorem Pres.defVal (d : DefValType) : Pres (Bridge.defVal d) := by
  unfold Bridge.defVal
  refine Pres.bind Pres.get fun s => ?_
  split
  · exact Pres.pure _
  · exact Pres.bind (Pres.defTy _) fun j => Pres.bind (Pres.modify fun _ => ⟨rfl, rfl, rfl⟩) fun _ => Pres.pure _

theorem Pres.handle (o : Bool) (i : Nat) : Pres (Bridge.handle o i) := by
  unfold Bridge.handle
  refine Pres.bind Pres.get fun s => ?_
  split
  · exact Pres.pure _
  · exact Pres.bind (Pres.defTy _) fun j => Pres.bind (Pres.modify fun _ => ⟨rfl, rfl, rfl⟩) fun _ => Pres.pure _

theorem Pres.map' {α β : Type} {m : TM α} (f : α → β) (hm : Pres m) : Pres (do let a ← m; Pure.pure (f a)) :=
  Pres.bind hm fun _ => Pres.pure _

mutual
theorem Pres.valTy : (t : Silmaril.Wasm.Wit.Binary.Ty) → Pres (Bridge.valTy t)
  | .prim _ => by unfold Bridge.valTy; exact Pres.pure _
  | .ref r => by
    unfold Bridge.valTy
    refine Pres.bind (Pres.namedTy _) fun i => Pres.bind Pres.get fun s => ?_
    split
    · exact Pres.handle _ _
    · exact Pres.pure _
  | .list t => by unfold Bridge.valTy; exact Pres.bind (Pres.valTy t) fun _ => Pres.defVal _
  | .fixedList t _ => by unfold Bridge.valTy; exact Pres.bind (Pres.valTy t) fun _ => Pres.defVal _
  | .map k v => by
    unfold Bridge.valTy
    exact Pres.bind (Pres.valTy k) fun _ => Pres.bind (Pres.valTy v) fun _ => Pres.defVal _
  | .option t => by unfold Bridge.valTy; exact Pres.bind (Pres.valTy t) fun _ => Pres.defVal _
  | .result a b => by
    unfold Bridge.valTy
    exact Pres.bind (Pres.valTyOpt a) fun _ => Pres.bind (Pres.valTyOpt b) fun _ => Pres.defVal _
  | .tuple ts => by unfold Bridge.valTy; exact Pres.bind (Pres.valTys ts) fun _ => Pres.defVal _
  | .own _ => by unfold Bridge.valTy; exact Pres.bind (Pres.namedTy _) fun _ => Pres.handle _ _
  | .borrow _ => by unfold Bridge.valTy; exact Pres.bind (Pres.namedTy _) fun _ => Pres.handle _ _
  | .future t => by unfold Bridge.valTy; exact Pres.bind (Pres.valTyOpt t) fun _ => Pres.defVal _
  | .stream t => by unfold Bridge.valTy; exact Pres.bind (Pres.valTyOpt t) fun _ => Pres.defVal _
theorem Pres.valTyOpt : (t : Option Silmaril.Wasm.Wit.Binary.Ty) → Pres (Bridge.valTyOpt t)
  | none => by unfold Bridge.valTyOpt; exact Pres.pure _
  | some t => by unfold Bridge.valTyOpt; exact Pres.bind (Pres.valTy t) fun _ => Pres.pure _
theorem Pres.valTys : (ts : List Silmaril.Wasm.Wit.Binary.Ty) → Pres (Bridge.valTys ts)
  | [] => by unfold Bridge.valTys; exact Pres.pure _
  | t :: ts => by
    unfold Bridge.valTys
    exact Pres.bind (Pres.valTy t) fun _ => Pres.bind (Pres.valTys ts) fun _ => Pres.pure _
end

theorem Pres.mapM {α β : Type} {f : α → TM β} (hf : ∀ a, Pres (f a)) :
    ∀ xs : List α, Pres (xs.mapM f)
  | [] => by rw [List.mapM_nil]; exact Pres.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact Pres.bind (hf x) fun _ => Pres.bind (Pres.mapM hf xs) fun _ => Pres.pure _

theorem Pres.paramTys : (ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)) → Pres (Bridge.paramTys ps)
  | [] => by unfold Bridge.paramTys; exact Pres.pure _
  | (_, t) :: ps => by
    unfold Bridge.paramTys
    exact Pres.bind (Pres.valTy t) fun _ => Pres.bind (Pres.paramTys ps) fun _ => Pres.pure _

theorem Pres.funcTy (s : Sig) : Pres (Bridge.funcTy s) := by
  unfold Bridge.funcTy
  refine Pres.bind Pres.get fun _ => Pres.bind Pres.get fun _ => ?_
  split
  · exact Pres.pure _
  · exact Pres.bind (Pres.paramTys _) fun _ => Pres.bind (Pres.valTyOpt _) fun _ =>
      Pres.bind (Pres.defTy _) fun _ => Pres.bind (Pres.modify fun _ => ⟨rfl, rfl, rfl⟩) fun _ => Pres.pure _

theorem Pres.shared (k : Kind) {m : TM Nat} (hm : Pres m) : Pres (Bridge.shared k m) := by
  unfold Bridge.shared
  refine Pres.bind Pres.get fun _ => Pres.bind Pres.get fun _ => ?_
  split
  · exact Pres.pure _
  · exact Pres.bind hm fun _ => Pres.bind (Pres.modify fun _ => ⟨rfl, rfl, rfl⟩) fun _ => Pres.pure _

theorem Pres.nested (sh : Bool) (m : TM Unit) : Pres (Bridge.nested sh m) := by
  unfold Bridge.nested
  refine Pres.bind Pres.get fun _ => ?_
  split
  · exact Pres.pure _
  · exact Pres.throw _

theorem Pres.nominalTy (d : Nominal) : Pres (Bridge.nominalTy d) := by
  cases d with
  | record fs =>
    unfold Bridge.nominalTy
    exact Pres.bind (Pres.mapM (fun _ => Pres.bind (Pres.valTy _) fun _ => Pres.pure _) fs) fun _ => Pres.defTy _
  | variant cs =>
    unfold Bridge.nominalTy
    exact Pres.bind (Pres.mapM (fun _ => Pres.bind (Pres.valTyOpt _) fun _ => Pres.pure _) cs) fun _ => Pres.defTy _
  | enum _ => unfold Bridge.nominalTy; exact Pres.defTy _
  | flags _ => unfold Bridge.nominalTy; exact Pres.defTy _

theorem Pres.freshVal (t : Silmaril.Wasm.Wit.Binary.Ty) : Pres (Bridge.freshVal t) := by
  cases t with
  | list t | option t => unfold Bridge.freshVal; exact Pres.bind (Pres.valTy t) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | fixedList t n => unfold Bridge.freshVal; exact Pres.bind (Pres.valTy t) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | map k v =>
    unfold Bridge.freshVal
    exact Pres.bind (Pres.valTy k) fun _ => Pres.bind (Pres.valTy v) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | result a b =>
    unfold Bridge.freshVal
    exact Pres.bind (Pres.valTyOpt a) fun _ => Pres.bind (Pres.valTyOpt b) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | tuple ts => unfold Bridge.freshVal; exact Pres.bind (Pres.valTys ts) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | future t | stream t => unfold Bridge.freshVal; exact Pres.bind (Pres.valTyOpt t) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | _ => unfold Bridge.freshVal; exact Pres.pure _

theorem Pres.typeBound_value (t : Silmaril.Wasm.Wit.Binary.Ty) : Pres (Bridge.typeBound (.value t)) := by
  unfold Bridge.typeBound
  refine Pres.bind Pres.get fun s => ?_
  split
  · exact Pres.bind (Pres.namedTy _) fun _ => Pres.pure _
  · split
    · exact Pres.bind (Pres.nominalTy _) fun _ => Pres.pure _
    · exact Pres.bind (Pres.namedTy _) fun _ => Pres.pure _
  · refine Pres.bind (Pres.freshVal _) fun o => ?_
    split
    · exact Pres.pure _
    · refine Pres.bind (Pres.valTy _) fun v => ?_
      split
      · exact Pres.pure _
      · exact Pres.bind (Pres.defTy _) fun _ => Pres.pure _

theorem Pres.typeBound (k : Kind) : Pres (Bridge.typeBound k) := by
  cases k with
  | resource _ => unfold Bridge.typeBound; exact Pres.pure _
  | value t => exact Pres.typeBound_value t
  | func s => unfold Bridge.typeBound; exact Pres.bind (Pres.funcTy s) fun _ => Pres.pure _
  | inst i es =>
    unfold Bridge.typeBound
    exact Pres.bind (Pres.nested _ _) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | comp i is es =>
    unfold Bridge.typeBound
    exact Pres.bind (Pres.nested _ _) fun _ => Pres.bind (Pres.defTy _) fun _ => Pres.pure _
  | type _ => unfold Bridge.typeBound; exact Pres.throw _

theorem Pres.externDesc (k : Kind) : Pres (Bridge.externDesc k) := by
  cases k with
  | func s => unfold Bridge.externDesc; exact Pres.bind (Pres.funcTy s) fun _ => Pres.pure _
  | value t => unfold Bridge.externDesc; exact Pres.bind (Pres.valTy t) fun _ => Pres.pure _
  | resource _ => unfold Bridge.externDesc; exact Pres.pure _
  | type k => unfold Bridge.externDesc; exact Pres.typeBound k
  | inst i es =>
    unfold Bridge.externDesc
    exact Pres.bind (Pres.shared _ (Pres.bind (Pres.nested _ _) fun _ => Pres.defTy _)) fun _ => Pres.pure _
  | comp i is es =>
    unfold Bridge.externDesc
    exact Pres.bind (Pres.shared _ (Pres.bind (Pres.nested _ _) fun _ => Pres.defTy _)) fun _ => Pres.pure _

theorem Pres.worldDef (id : String) (is es : Externs) : Pres (Bridge.worldDef id is es) := by
  unfold Bridge.worldDef
  exact Pres.bind (Pres.nested _ _) fun _ => Pres.bind (Pres.nested _ _) fun _ =>
    Pres.bind (Pres.defTy _) fun _ => Pres.pure _

theorem Pres.ifaceDef (id : String) (es : Externs) : Pres (Bridge.ifaceDef id es) := by
  unfold Bridge.ifaceDef
  exact Pres.bind (Pres.nested _ _) fun _ => Pres.bind (Pres.nested _ _) fun _ =>
    Pres.bind (Pres.defTy _) fun _ => Pres.pure _

theorem Pres.defnTy (k : Kind) : Pres (Bridge.defnTy k) := by
  unfold Bridge.defnTy
  split
  · exact Pres.worldDef _ _ _
  · exact Pres.ifaceDef _ _
  · exact Pres.typeBound _

theorem run_bind_ok {α β : Type} {m : TM α} {f : α → TM β} {s : Scope} {b : β} {s' : Scope}
    (h : (m >>= f).run s = .ok (b, s')) : ∃ a s₁, m.run s = .ok (a, s₁) ∧ (f a).run s₁ = .ok (b, s') := by
  rw [StateT.run_bind] at h
  cases hr : m.run s with
  | error e => rw [hr] at h; cases h
  | ok p => rw [hr] at h; exact ⟨p.1, p.2, rfl, h⟩

/-- What a computation returns, whatever the state. -/
def Ret {α : Type} (P : α → Prop) (m : TM α) : Prop := ∀ s a s', m.run s = .ok (a, s') → P a

theorem Ret.pure {α : Type} {P : α → Prop} {a : α} (h : P a) : Ret P (Pure.pure a : TM α) := by
  intro s b s' hr; cases hr; exact h

theorem Ret.bind {α β : Type} {P : β → Prop} {m : TM α} {f : α → TM β} (hf : ∀ a, Ret P (f a)) :
    Ret P (m >>= f) := by
  intro s b s' h
  obtain ⟨a, s₁, _, h₂⟩ := run_bind_ok h
  exact hf a s₁ b s' h₂

theorem Ret.throw {α : Type} {P : α → Prop} (e : String) : Ret P (throw e : TM α) := by
  intro s b s' h; cases h

def isTypeDesc : ExternDesc → Prop
  | .type _ => True
  | _ => False

theorem Ret.typeBound_value (t : Silmaril.Wasm.Wit.Binary.Ty) : Ret isTypeDesc (Bridge.typeBound (.value t)) := by
  unfold Bridge.typeBound
  refine Ret.bind fun s => ?_
  split
  · exact Ret.bind fun _ => Ret.pure trivial
  · split
    · exact Ret.bind fun _ => Ret.pure trivial
    · exact Ret.bind fun _ => Ret.pure trivial
  · refine Ret.bind fun o => ?_
    split
    · exact Ret.pure trivial
    · refine Ret.bind fun v => ?_
      split
      · exact Ret.pure trivial
      · exact Ret.bind fun _ => Ret.pure trivial

theorem Ret.typeBound (k : Kind) : Ret isTypeDesc (Bridge.typeBound k) := by
  cases k with
  | resource _ => unfold Bridge.typeBound; exact Ret.pure trivial
  | value t => exact Ret.typeBound_value t
  | func s => unfold Bridge.typeBound; exact Ret.bind fun _ => Ret.pure trivial
  | inst i es => unfold Bridge.typeBound; exact Ret.bind fun _ => Ret.bind fun _ => Ret.pure trivial
  | comp i is es => unfold Bridge.typeBound; exact Ret.bind fun _ => Ret.bind fun _ => Ret.pure trivial
  | type _ => unfold Bridge.typeBound; exact Ret.throw _

theorem Ret.externDesc (k : Kind) : Ret (fun d => descSort d = kindSort k) (Bridge.externDesc k) := by
  cases k with
  | func s => unfold Bridge.externDesc; exact Ret.bind fun _ => Ret.pure rfl
  | value t => unfold Bridge.externDesc; exact Ret.bind fun _ => Ret.pure rfl
  | resource _ => unfold Bridge.externDesc; exact Ret.pure rfl
  | type k =>
    unfold Bridge.externDesc
    intro s d s' h
    have hd : isTypeDesc d := Ret.typeBound k s d s' h
    cases d <;> first | rfl | exact hd.elim
  | inst i es => unfold Bridge.externDesc; exact Ret.bind fun _ => Ret.pure rfl
  | comp i is es => unfold Bridge.externDesc; exact Ret.bind fun _ => Ret.pure rfl

/-- The function exports of instance declarations (as `Lower.instTypeFuncs` reads them). -/
def ifuncs (ds : List InstanceDecl) : List String :=
  ds.filterMap fun | .export n (.func _) => some n.name | _ => none

theorem instDecls_append (a b : List ComponentDecl) : instDecls (a ++ b) = instDecls a ++ instDecls b :=
  List.filterMap_append

theorem ifuncs_append (a b : List InstanceDecl) : ifuncs (a ++ b) = ifuncs a ++ ifuncs b :=
  List.filterMap_append

theorem ifuncs_types (ds : List ComponentDecl) (ts : List DefType) :
    ifuncs (instDecls (ds ++ ts.map fun d => .inst (.type d))) = ifuncs (instDecls ds) := by
  have h : ifuncs (instDecls (ts.map fun d => .inst (.type d))) = [] := by
    induction ts with
    | nil => rfl
    | cons t ts ih => exact ih
  rw [instDecls_append, ifuncs_append, h, List.append_nil]

theorem ifuncs_tinv {s s' : Scope} (h : TInv s s') : ifuncs (instDecls s'.decls) = ifuncs (instDecls s.decls) := by
  obtain ⟨ts, hd, _, _⟩ := h
  rw [hd, ifuncs_types]

theorem declared_decls {n : String} {d : ExternDesc} {s s' : Scope}
    (h : (declared n d).run s = .ok ((), s')) : s'.decls = s.decls := by
  unfold declared at h
  cases d with
  | type b => cases h; rfl
  | _ => cases h; rfl

/-- A function descriptor. -/
def isFuncDesc : ExternDesc → Bool
  | .func _ => true
  | _ => false

theorem isFuncDesc_of_sort {d : ExternDesc} {k : Kind} (h : descSort d = kindSort k) :
    isFuncDesc d = (match k with | .func _ => true | _ => false) := by
  cases d <;> cases k <;> first | rfl | (simp [descSort, kindSort] at h)

theorem ifuncs_export (ds : List ComponentDecl) (n : String) (d : ExternDesc) :
    ifuncs (instDecls (ds ++ [.inst (.export ⟨n, .plain0⟩ d)])) =
      ifuncs (instDecls ds) ++ (if isFuncDesc d then [n] else []) := by
  rw [instDecls_append, ifuncs_append]
  cases d <;> rfl

theorem funcNames_cons (n : String) (k : Kind) (es : Externs) :
    funcNames ((n, k) :: es) = (match k with | .func _ => [n] | _ => []) ++ funcNames es := by
  cases k <;> rfl

/-- The exports of an instance type are its items, in order. -/
theorem exportDecls_ifuncs : ∀ (es : Externs) (s s' : Scope), (exportDecls es).run s = .ok ((), s') →
    ifuncs (instDecls s'.decls) = ifuncs (instDecls s.decls) ++ funcNames es
  | [], s, s', h => by
    have : s' = s := by unfold exportDecls at h; cases h; rfl
    rw [this]; exact (List.append_nil _).symm
  | (n, k) :: es, s, s', h => by
    unfold exportDecls at h
    obtain ⟨d, s₁, h₁, h'⟩ := run_bind_ok h
    obtain ⟨_, s₂, h₂, h''⟩ := run_bind_ok h'
    obtain ⟨_, s₃, h₃, h₄⟩ := run_bind_ok h''
    have hs₂ : s₂ = { s₁ with decls := s₁.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] } := by
      cases h₂; rfl
    have e₁ : ifuncs (instDecls s₁.decls) = ifuncs (instDecls s.decls) :=
      ifuncs_tinv (Pres.externDesc k s d s₁ h₁)
    have e₃ : s₃.decls = s₂.decls := declared_decls h₃
    have hsort : descSort d = kindSort k := Ret.externDesc k s d s₁ h₁
    have ih := exportDecls_ifuncs es s₃ s' h₄
    rw [ih, e₃, hs₂, ifuncs_export, e₁, isFuncDesc_of_sort hsort, funcNames_cons, List.append_assoc]
    cases k <;> rfl

/-- Without sharing, an instance kind is one new instance type whose function exports
are the kind's. -/
theorem externDesc_inst {i : Option String} {es : Externs} {s s' : Scope} {d : ExternDesc}
    (hs : s.share = false) (h : (externDesc (.inst i es)).run s = .ok (d, s')) :
    d = .instance s.ntypes ∧ ∃ ids, s'.decls = s.decls ++ [.inst (.type (.instance ids))] ∧
      s'.ntypes = s.ntypes + 1 ∧ ifuncs ids = funcNames es := by
  unfold externDesc at h
  obtain ⟨j, s₁, h₁, h₂⟩ := run_bind_ok h
  have hd : d = .instance j ∧ s' = s₁ := by cases h₂; exact ⟨rfl, rfl⟩
  unfold shared at h₁
  obtain ⟨x, s₂, hx, h₃⟩ := run_bind_ok h₁
  obtain ⟨y, s₃, hy, h₄⟩ := run_bind_ok h₃
  have ex : x = s ∧ s₂ = s := by cases hx; exact ⟨rfl, rfl⟩
  have ey : y = s ∧ s₃ = s := by rw [ex.2] at hy; cases hy; exact ⟨rfl, rfl⟩
  rw [ex.1, ey.1, ey.2, hs] at h₄
  obtain ⟨j', s₄, h₅, h₆⟩ := run_bind_ok h₄
  obtain ⟨_, s₅, h₇, h₈⟩ := run_bind_ok h₆
  have e₈ : j = j' ∧ s₁ = s₅ := by cases h₈; exact ⟨rfl, rfl⟩
  have e₇ : s₅ = { s₄ with kcache := s₄.kcache ++ [(.inst i es, j')] } := by cases h₇; rfl
  obtain ⟨ds, s₆, h₉, h₁₀⟩ := run_bind_ok h₅
  unfold nested at h₉
  obtain ⟨z, s₇, hz, h₁₁⟩ := run_bind_ok h₉
  have ez : z = s ∧ s₇ = s := by cases hz; exact ⟨rfl, rfl⟩
  rw [ez.1, ez.2] at h₁₁
  split at h₁₁
  · show d = .instance s.ntypes ∧ ∃ ids, s'.decls = s.decls ++ [.inst (.type (.instance ids))] ∧
      s'.ntypes = s.ntypes + 1 ∧ ifuncs ids = funcNames es
    rename_i s₀ hrun
    have e₁₁ : ds = s₀.decls ∧ s₆ = s := by cases h₁₁; exact ⟨rfl, rfl⟩
    rw [e₁₁.2] at h₁₀
    have e₁₀ : j' = s.ntypes ∧
        s₄ = { s with decls := s.decls ++ [.inst (.type (.instance (instDecls ds)))], ntypes := s.ntypes + 1 } := by
      cases h₁₀; exact ⟨rfl, rfl⟩
    have hf : ifuncs (instDecls s₀.decls) = funcNames es := by
      have := exportDecls_ifuncs es _ s₀ hrun
      rw [this]; rfl
    refine ⟨?_, instDecls ds, ?_, ?_, ?_⟩
    · rw [hd.1, e₈.1, e₁₀.1]
    · rw [hd.2, e₈.2, e₇, e₁₀.2]
    · rw [hd.2, e₈.2, e₇, e₁₀.2]
    · rw [e₁₁.1]; exact hf
  · cases h₁₁

end Silmaril.Wasm.Wac.Bridge
