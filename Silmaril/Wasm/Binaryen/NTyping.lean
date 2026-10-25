module

public import Silmaril.Wasm.Binaryen.Resolve
public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Binaryen.Profile
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.V2.ToCore.Validation

@[expose] public section

/-! # Declarative typing of layer N

Binaryen's typing (`src/wasm/wasm-validator.cpp` and the `finalize` methods of
`src/wasm/wasm.cpp`, version_133) for the profile: `unreachable` is the bottom
type (`NTy.Sub`), a block's type is that of its last child or of the values
branched to it, `br_if` passes its value through, `if` without `else` has type
`none`. The computable counterpart is `refinalize` (`Binaryen/Refinalize.lean`).

This judgement exists to state Binaryen's own invariants; it never competes with
Core typing. `resolve_ok` says well-typed named modules resolve unless an index
space overflows `2 ^ 32`; `resolve_valid` says that, under the Core side
conditions `NModule.CoreReady` (type section, import signatures, profile types,
constant global initialisers, distinct export names, start signature, mutable
`global.set` targets, valid `extend`), they resolve to modules whose lowering
Core 3.0 validates. Both original statements are refuted (`resolve_ok_false`,
`resolve_valid_false`).
-/

namespace Silmaril.Wasm.Binaryen

/-- Typing environment of a function body. -/
structure NEnv where
  locals : List ValType
  globals : List (Name × ValType)
  funcs : List (Name × List ValType × List ValType)
  results : List ValType

/-- The `NTy` of a result list (single values only in the profile). -/
def resultTy : List ValType → NTy
  | [] => .none
  | [t] => .val t
  | _ => .none

/-- The type branches to a label carry, pushed when entering a named scope. -/
def pushLabel (l : Option Name) (t : NTy) (Λ : List (Name × NTy)) : List (Name × NTy) :=
  match l with
  | some n => (n, t) :: Λ
  | none => Λ

mutual
/-- `Γ; Λ ⊢ e : t`. `Λ` maps label names (innermost first) to the type of the values
branches to them carry (`none`: no value). -/
inductive HasType (Γ : NEnv) : List (Name × NTy) → NExpr → NTy → Prop where
  | sub {Λ e a b} : HasType Γ Λ e a → NTy.Sub a b → HasType Γ Λ e b
  | const {Λ} (c : Lit) : HasType Γ Λ (.const c) (.val c.ty)
  | localGet {Λ i t} : Γ.locals[i]? = some t → HasType Γ Λ (.localGet i) (.val t)
  | localSet {Λ i v t} : Γ.locals[i]? = some t → HasType Γ Λ v (.val t) →
      HasType Γ Λ (.localSet i v false) .none
  | localTee {Λ i v t} : Γ.locals[i]? = some t → HasType Γ Λ v (.val t) →
      HasType Γ Λ (.localSet i v true) (.val t)
  | globalGet {Λ g t} : Γ.globals.lookup g = some t → HasType Γ Λ (.globalGet g) (.val t)
  | globalSet {Λ g v t} : Γ.globals.lookup g = some t → HasType Γ Λ v (.val t) →
      HasType Γ Λ (.globalSet g v) .none
  | unary {Λ op e} : HasType Γ Λ e (.val op.argTy) → HasType Γ Λ (.unary op e) (.val op.resTy)
  | binary {Λ op a b} : HasType Γ Λ a (.val op.argTy) → HasType Γ Λ b (.val op.argTy) →
      HasType Γ Λ (.binary op a b) (.val op.resTy)
  | select {Λ a b c t} : HasType Γ Λ a (.val t) → HasType Γ Λ b (.val t) →
      HasType Γ Λ c (.val .i32) → HasType Γ Λ (.select a b c) (.val t)
  | drop {Λ e t} : HasType Γ Λ e (.val t) → HasType Γ Λ (.drop e) .none
  | nop {Λ} : HasType Γ Λ .nop .none
  | unreachable {Λ} : HasType Γ Λ .unreachable .unreachable
  | returnNone {Λ} : Γ.results = [] → HasType Γ Λ (.return_ none) .unreachable
  | returnSome {Λ v t} : Γ.results = [t] → HasType Γ Λ v (.val t) →
      HasType Γ Λ (.return_ (some v)) .unreachable
  | br {Λ l v vt} : Λ.lookup l = some vt → HasTypeOpt Γ Λ v vt →
      HasType Γ Λ (.br l v none) .unreachable
  | brIf {Λ l v c vt} : Λ.lookup l = some vt → HasTypeOpt Γ Λ v vt →
      HasType Γ Λ c (.val .i32) → HasType Γ Λ (.br l v (some c)) vt
  | switch {Λ ls d v c vt} : (∀ l ∈ d :: ls, Λ.lookup l = some vt) → HasTypeOpt Γ Λ v vt →
      HasType Γ Λ c (.val .i32) → HasType Γ Λ (.switch ls d v c) .unreachable
  | call {Λ f args ps rs} : Γ.funcs.lookup f = some (ps, rs) → HasTypes Γ Λ args ps →
      HasType Γ Λ (.call f args) (resultTy rs)
  | block {Λ l body ty} : HasTypeSeq Γ (pushLabel l ty Λ) body ty →
      HasType Γ Λ (.block l body ty) ty
  | loop {Λ l body ty} : HasType Γ (pushLabel l .none Λ) body ty →
      HasType Γ Λ (.loop l body ty) ty
  | ifElse {Λ c t e ty} : HasType Γ Λ c (.val .i32) → HasType Γ Λ t ty → HasType Γ Λ e ty →
      HasType Γ Λ (.if_ c t (some e) ty) ty
  | ifNoElse {Λ c t} : HasType Γ Λ c (.val .i32) → HasType Γ Λ t .none →
      HasType Γ Λ (.if_ c t none .none) .none
/-- An optional branch value of type `vt` (`none` iff no value). -/
inductive HasTypeOpt (Γ : NEnv) : List (Name × NTy) → Option NExpr → NTy → Prop where
  | absent {Λ} : HasTypeOpt Γ Λ none .none
  | present {Λ e t} : HasType Γ Λ e (.val t) → HasTypeOpt Γ Λ (some e) (.val t)
/-- Call operands of the parameter types. -/
inductive HasTypes (Γ : NEnv) : List (Name × NTy) → List NExpr → List ValType → Prop where
  | nil {Λ} : HasTypes Γ Λ [] []
  | cons {Λ e es t ts} : HasType Γ Λ e (.val t) → HasTypes Γ Λ es ts →
      HasTypes Γ Λ (e :: es) (t :: ts)
/-- A block body: every element but the last is a statement (`none`, or
`unreachable`), and the last has the block's type (`none` for an empty body). -/
inductive HasTypeSeq (Γ : NEnv) : List (Name × NTy) → List NExpr → NTy → Prop where
  | nil {Λ ty} : NTy.Sub .none ty → HasTypeSeq Γ Λ [] ty
  | last {Λ e ty} : HasType Γ Λ e ty → HasTypeSeq Γ Λ [e] ty
  | cons {Λ e e' es ty} : HasType Γ Λ e .none → HasTypeSeq Γ Λ (e' :: es) ty →
      HasTypeSeq Γ Λ (e :: e' :: es) ty
end

namespace NModule

/-- The environment of a defined function. -/
def fenv (m : NModule) (f : NFunc) : NEnv where
  locals := f.params ++ f.vars
  globals := m.globals.map fun (n, g) => (n, g.type.value)
  funcs := m.imports.map (fun (n, i) => (n, i.params, i.results)) ++
    m.funcs.map (fun (n, f) => (n, f.params, f.results))
  results := f.results

/-- **Well-typed named modules**: distinct names, every body typed at its result
type, globals initialised at their types, exports and start bound. -/
structure WellTyped (m : NModule) : Prop where
  funcNames : (m.imports.map Prod.fst ++ m.funcs.map Prod.fst).Nodup
  globalNames : (m.globals.map Prod.fst).Nodup
  bodies : ∀ p ∈ m.funcs, HasType (m.fenv p.2) [] p.2.body (resultTy p.2.results)
  globalInits : ∀ p ∈ m.globals, HasType (m.fenv ⟨⟨⟨0, by decide⟩⟩, [], [], [], .nop⟩) []
    p.2.init (.val p.2.type.value)
  exportsBound : ∀ x ∈ m.exports, match x.kind with
    | .func => x.internal ∈ m.imports.map Prod.fst ++ m.funcs.map Prod.fst
    | .global => x.internal ∈ m.globals.map Prod.fst
  startBound : ∀ s, m.start = some s → s ∈ m.imports.map Prod.fst ++ m.funcs.map Prod.fst
  /-- Signatures agree with the type section. -/
  types : ∀ p ∈ m.funcs, ∃ ft, (BModule.funcType? ⟨{ types := m.types }, []⟩ p.2.type) = some ft ∧
    ft.params = p.2.params ∧ ft.results = p.2.results

end NModule

/-! ## Resolution of well-typed modules -/

namespace ResolveOk

/-- A resolution result that fails, if at all, only by index overflow. -/
def Good {α : Type} (r : Except ResolveErr α) : Prop :=
  ∀ err, r = .error err → ∃ n, err = .indexOverflow n

theorem good_ok {α : Type} (a : α) : Good (.ok a : Except ResolveErr α) :=
  fun _ h => nomatch h

theorem good_pure {α : Type} (a : α) : Good (pure a : Except ResolveErr α) := good_ok a

theorem good_bind {α β : Type} {r : Except ResolveErr α} {f : α → Except ResolveErr β}
    (hr : Good r) (hf : ∀ a, Good (f a)) : Good (r >>= f) := by
  cases r with
  | error e =>
    intro err h
    have h' : e = err := by injection h
    exact hr err (by rw [h'])
  | ok a => exact hf a

theorem good_mapM {α β : Type} {f : α → Except ResolveErr β} :
    ∀ {l : List α}, (∀ x ∈ l, Good (f x)) → Good (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact good_pure _
  | x :: l, h => by
    rw [List.mapM_cons]
    exact good_bind (h x (by simp)) fun _ =>
      good_bind (good_mapM fun y hy => h y (by simp [hy])) fun _ => good_pure _

theorem good_toIdx {k : IndexKind} (n : Nat) : Good (toIdx n : Except ResolveErr (Idx k)) := by
  unfold toIdx
  split
  · exact good_ok _
  · intro err h
    injection h with h
    exact ⟨n, h.symm⟩

theorem findIdx_some {α : Type} [BEq α] [LawfulBEq α] {a : α} {L : List α} (h : a ∈ L) :
    ∃ n, L.findIdx? (· == a) = some n := by
  cases hf : L.findIdx? (· == a) with
  | some n => exact ⟨n, rfl⟩
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    simpa using hf a h

theorem good_labelDepth {L : List (Option Name)} {l : Name} (h : some l ∈ L) :
    Good (labelDepth L l) := by
  obtain ⟨n, hn⟩ := findIdx_some h
  unfold labelDepth
  rw [hn]
  exact good_toIdx n

theorem good_func {E : NameEnv} {f : Name} (h : f ∈ E.funcs) : Good (E.func f) := by
  obtain ⟨n, hn⟩ := findIdx_some h
  unfold NameEnv.func
  rw [hn]
  dsimp only
  split
  · exact good_ok _
  · intro err h
    injection h with h
    exact ⟨n, h.symm⟩

theorem good_global {E : NameEnv} {g : Name} (h : g ∈ E.globals) : Good (E.global g) := by
  obtain ⟨n, hn⟩ := findIdx_some h
  unfold NameEnv.global
  rw [hn]
  dsimp only
  split
  · exact good_ok _
  · intro err h
    injection h with h
    exact ⟨n, h.symm⟩

/-- Every label the typing environment binds is on the break stack. -/
def LabOk (Λ : List (Name × NTy)) (L : List (Option Name)) : Prop :=
  ∀ l τ, Λ.lookup l = some τ → some l ∈ L

theorem labOk_nil (L : List (Option Name)) : LabOk [] L := by
  intro l τ h
  simp at h

theorem labOk_push {Λ : List (Name × NTy)} {L : List (Option Name)} (hL : LabOk Λ L)
    (l : Option Name) (τ : NTy) : LabOk (pushLabel l τ Λ) (l :: L) := by
  cases l with
  | none => exact fun l' τ' h => List.mem_cons_of_mem _ (hL l' τ' h)
  | some n =>
    intro l' τ' h
    by_cases hl : l' = n
    · subst hl; exact List.mem_cons_self
    · have hb : (l' == n) = false := by simpa using hl
      simp only [pushLabel, List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (hL l' τ' h)

theorem labOk_none {Λ : List (Name × NTy)} {L : List (Option Name)} (hL : LabOk Λ L) :
    LabOk Λ (none :: L) :=
  fun l τ h => List.mem_cons_of_mem _ (hL l τ h)

section
variable (E : NameEnv) (Γ : NEnv) (hF : ∀ f x, Γ.funcs.lookup f = some x → f ∈ E.funcs)
  (hG : ∀ g x, Γ.globals.lookup g = some x → g ∈ E.globals)

include hF hG in
set_option linter.unusedSectionVars false in
mutual
theorem good_E {Λ : List (Name × NTy)} {e : NExpr} {t : NTy} (h : HasType Γ Λ e t) :
    ∀ L, LabOk Λ L → Good (resolveE E L e) :=
  match h with
  | .sub h _ => good_E h
  | .const _ => fun _ _ => good_pure _
  | .localGet _ => fun _ _ => good_bind (good_toIdx _) fun _ => good_pure _
  | .localSet _ hv => fun L hL =>
    good_bind (good_toIdx _) fun _ => good_bind (good_E hv L hL) fun _ => good_pure _
  | .localTee _ hv => fun L hL =>
    good_bind (good_toIdx _) fun _ => good_bind (good_E hv L hL) fun _ => good_pure _
  | .globalGet hg => fun _ _ => good_bind (good_global (hG _ _ hg)) fun _ => good_pure _
  | .globalSet hg hv => fun L hL =>
    good_bind (good_global (hG _ _ hg)) fun _ => good_bind (good_E hv L hL) fun _ => good_pure _
  | .unary hv => fun L hL => good_bind (good_E hv L hL) fun _ => good_pure _
  | .binary ha hb => fun L hL =>
    good_bind (good_E ha L hL) fun _ => good_bind (good_E hb L hL) fun _ => good_pure _
  | .select ha hb hc => fun L hL =>
    good_bind (good_E ha L hL) fun _ => good_bind (good_E hb L hL) fun _ =>
      good_bind (good_E hc L hL) fun _ => good_pure _
  | .drop hv => fun L hL => good_bind (good_E hv L hL) fun _ => good_pure _
  | .nop => fun _ _ => good_pure _
  | .unreachable => fun _ _ => good_pure _
  | .returnNone _ => fun _ _ => good_bind (good_pure _) fun _ => good_pure _
  | .returnSome _ hv => fun L hL => good_bind (good_E hv L hL) fun _ => good_pure _
  | .br hl hv => fun L hL =>
    good_bind (good_labelDepth (hL _ _ hl)) fun _ => good_bind (good_O hv L hL) fun _ =>
      good_bind (good_pure _) fun _ => good_pure _
  | .brIf hl hv hc => fun L hL =>
    good_bind (good_labelDepth (hL _ _ hl)) fun _ => good_bind (good_O hv L hL) fun _ =>
      good_bind (good_E hc L hL) fun _ => good_pure _
  | .switch hls hv hc => fun L hL =>
    good_bind (good_mapM fun l hl =>
        good_labelDepth (hL _ _ (hls l (List.mem_cons_of_mem _ hl))))
      fun _ => good_bind (good_labelDepth (hL _ _ (hls _ List.mem_cons_self))) fun _ =>
        good_bind (good_O hv L hL) fun _ => good_bind (good_E hc L hL) fun _ => good_pure _
  | .call hf hargs => fun L hL =>
    good_bind (good_func (hF _ _ hf)) fun _ => good_bind (good_L hargs L hL) fun _ => good_pure _
  | .block (l := l) (ty := ty) hs => fun L hL => by
    have ih := good_S hs
    cases l with
    | none => exact ih L hL
    | some n =>
      exact good_bind (ih (some n :: L) (labOk_push hL (some n) ty)) fun _ => good_pure _
  | .loop (l := l) hb => fun L hL =>
    good_bind (good_E hb (l :: L) (labOk_push hL l .none)) fun _ => good_pure _
  | .ifElse hc ht he => fun L hL =>
    good_bind (good_E hc L hL) fun _ => good_bind (good_E ht (none :: L) (labOk_none hL)) fun _ =>
      good_bind (good_E he (none :: L) (labOk_none hL)) fun _ => good_pure _
  | .ifNoElse hc ht => fun L hL =>
    good_bind (good_E hc L hL) fun _ => good_bind (good_E ht (none :: L) (labOk_none hL)) fun _ =>
      good_bind (good_pure _) fun _ => good_pure _
theorem good_O {Λ : List (Name × NTy)} {v : Option NExpr} {vt : NTy}
    (h : HasTypeOpt Γ Λ v vt) : ∀ L, LabOk Λ L → Good (resolveO E L v) :=
  match h with
  | .absent => fun _ _ => good_pure _
  | .present he => good_E he
theorem good_L {Λ : List (Name × NTy)} {args : List NExpr} {ps : List ValType}
    (h : HasTypes Γ Λ args ps) : ∀ L, LabOk Λ L → Good (resolveL E L args) :=
  match h with
  | .nil => fun _ _ => good_pure _
  | .cons he hes => fun L hL =>
    good_bind (good_E he L hL) fun _ => good_bind (good_L hes L hL) fun _ => good_pure _
theorem good_S {Λ : List (Name × NTy)} {body : List NExpr} {ty : NTy}
    (h : HasTypeSeq Γ Λ body ty) : ∀ L, LabOk Λ L → Good (resolveL E L body) :=
  match h with
  | .nil _ => fun _ _ => good_pure _
  | .last he => fun L hL =>
    good_bind (good_E he L hL) fun _ => good_bind (good_pure _) fun _ => good_pure _
  | .cons he hrest => fun L hL =>
    good_bind (good_E he L hL) fun _ => good_bind (good_S hrest L hL) fun _ => good_pure _
end
end

theorem lookup_mem_fst {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → ∃ p ∈ l, p.1 = a
  | [], h => by simp at h
  | (k, v) :: l, h => by
    by_cases hk : a = k
    · exact ⟨(k, v), List.mem_cons_self, hk.symm⟩
    · have hb : (a == k) = false := by simpa using hk
      simp only [List.lookup_cons, hb] at h
      obtain ⟨p, hp, hpa⟩ := lookup_mem_fst h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpa⟩

theorem fenv_funcs (m : NModule) (f : NFunc) :
    ∀ g x, (m.fenv f).funcs.lookup g = some x → g ∈ m.env.funcs := by
  intro g x h
  obtain ⟨p, hp, rfl⟩ := lookup_mem_fst h
  simp only [NModule.fenv, NModule.env, List.mem_append, List.mem_map] at hp ⊢
  rcases hp with ⟨⟨n, i⟩, hq, rfl⟩ | ⟨⟨n, f'⟩, hq, rfl⟩
  · exact Or.inl ⟨(n, i), hq, rfl⟩
  · exact Or.inr ⟨(n, f'), hq, rfl⟩

theorem fenv_globals (m : NModule) (f : NFunc) :
    ∀ g x, (m.fenv f).globals.lookup g = some x → g ∈ m.env.globals := by
  intro g x h
  obtain ⟨p, hp, rfl⟩ := lookup_mem_fst h
  simp only [NModule.fenv, NModule.env, List.mem_map] at hp ⊢
  obtain ⟨⟨n, gl⟩, hq, rfl⟩ := hp
  exact ⟨(n, gl), hq, rfl⟩

theorem good_resolve {m : NModule} (h : m.WellTyped) : Good m.resolve := by
  unfold NModule.resolve
  refine good_bind (good_mapM ?_) fun _ => good_bind (good_mapM ?_) fun _ =>
    good_bind (good_mapM ?_) fun _ => ?_
  · rintro ⟨n, f⟩ hx
    exact good_bind (good_E m.env (m.fenv f) (fenv_funcs m f) (fenv_globals m f)
      (h.bodies _ hx) [] (labOk_nil _)) fun _ => good_pure _
  · rintro ⟨n, g⟩ hx
    exact good_bind (good_E m.env _ (fenv_funcs m _) (fenv_globals m _)
      (h.globalInits _ hx) [] (labOk_nil _)) fun _ => good_pure _
  · intro x hx
    have hb := h.exportsBound x hx
    cases hk : x.kind with
    | func =>
      rw [hk] at hb
      exact good_bind (good_func hb) fun _ => good_pure _
    | global =>
      rw [hk] at hb
      exact good_bind (good_global hb) fun _ => good_pure _
  · cases hs : m.start with
    | none => exact good_pure _
    | some s =>
      exact good_bind (good_func (h.startBound s hs)) fun _ =>
        good_bind (good_pure _) fun _ => good_pure _

end ResolveOk

namespace Counterexample

/-- A function with `2 ^ 32 + 1` locals reading the last one. -/
def overflowFunc : NFunc :=
  ⟨⟨⟨0, by decide⟩⟩, [], [], List.replicate (2 ^ 32 + 1) .i32, .drop (.localGet (2 ^ 32))⟩

/-- A module whose only function is `overflowFunc`. -/
def overflow : NModule :=
  { types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩], funcs := [("f", overflowFunc)] }

theorem overflow_wellTyped : overflow.WellTyped := by
  refine ⟨by decide, by decide, ?_, (fun _ h => by cases h), (fun _ h => by cases h),
    (fun _ h => by cases h), ?_⟩
  · intro p hp
    rw [show overflow.funcs = [("f", overflowFunc)] from rfl, List.mem_singleton] at hp
    subst hp
    refine .drop (t := .i32) (.localGet ?_)
    show (([] : List ValType) ++ List.replicate (2 ^ 32 + 1) ValType.i32)[2 ^ 32]? =
      some ValType.i32
    rw [List.nil_append, List.getElem?_replicate]
    simp
  · intro p hp
    rw [show overflow.funcs = [("f", overflowFunc)] from rfl, List.mem_singleton] at hp
    subst hp
    exact ⟨⟨[], []⟩, rfl, rfl, rfl⟩

theorem overflow_resolve : overflow.resolve = .error (.indexOverflow (2 ^ 32)) := by rfl

/-- A module exporting one global twice under the same name. -/
def dupExport : NModule :=
  { globals := [("g", ⟨⟨.const, .i32⟩, .const (.i32 0)⟩)],
    exports := [⟨"a", .global, "g"⟩, ⟨"a", .global, "g"⟩] }

theorem dupExport_wellTyped : dupExport.WellTyped := by
  refine ⟨by decide, by decide, (fun _ h => by cases h), ?_, ?_, (fun _ h => by cases h),
    (fun _ h => by cases h)⟩
  · intro p hp
    rw [show dupExport.globals = [("g", ⟨⟨.const, .i32⟩, .const (.i32 0)⟩)] from rfl,
      List.mem_singleton] at hp
    subst hp
    exact .const (.i32 0)
  · intro x hx
    rw [show dupExport.exports = [⟨"a", .global, "g"⟩, ⟨"a", .global, "g"⟩] from rfl] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx
    decide

end Counterexample

/-- The original `resolve_ok` (`∃ b, m.resolve = .ok b`) is **false**: `WellTyped` does not
bound index spaces, and resolution rejects indices `≥ 2 ^ 32`. A function with `2 ^ 32 + 1`
locals reading the last one is well typed and fails to resolve. -/
theorem resolve_ok_false : ¬ ∀ m : NModule, m.WellTyped → ∃ b, m.resolve = .ok b := by
  intro H
  obtain ⟨b, hb⟩ := H Counterexample.overflow Counterexample.overflow_wellTyped
  rw [Counterexample.overflow_resolve] at hb
  cases hb

/-- Well-typed named modules resolve, unless an index space overflows `2 ^ 32`. -/
-- FLAG(statement-change): added the `indexOverflow` disjunct. The original conclusion
-- `∃ b, m.resolve = .ok b` is false (`resolve_ok_false`): `WellTyped` does not bound the
-- number of locals, functions, globals or nested labels, and resolution rejects indices
-- `≥ 2 ^ 32`. Every other resolution error (unbound label, function or global) is excluded.
theorem resolve_ok {m : NModule} (h : m.WellTyped) :
    (∃ b, m.resolve = .ok b) ∨ ∃ n, m.resolve = .error (.indexOverflow n) := by
  have key := ResolveOk.good_resolve h
  cases hr : m.resolve with
  | ok b => exact Or.inl ⟨b, rfl⟩
  | error err =>
    obtain ⟨n, rfl⟩ := key err hr
    exact Or.inr ⟨n, rfl⟩

/-- The original `resolve_valid` is **false**: `WellTyped` does not require distinct export
names, which Core module validation does (`Module_ok`). -/
theorem resolve_valid_false :
    ∃ (m : NModule) (b : BModule), m.WellTyped ∧ m.resolve = .ok b ∧ ¬ b.Ok := by
  refine ⟨Counterexample.dupExport, _, Counterexample.dupExport_wellTyped, rfl, ?_⟩
  rintro ⟨t, ht⟩
  cases ht
  rename_i hd
  exact absurd hd (by decide)

/-! ## Core validity of resolved bodies -/

/-- Annotations Core can write: value types of the profile. -/
def NTy.annOk : NTy → Bool
  | .val t => profileValType t
  | _ => true

/-- Unary operators valid for Core (`extend` narrower than the operand). -/
def UnOp.valid : UnOp → Bool
  | .int t op => op.valid t
  | .eqz _ => true

mutual
/-- Code-level side conditions of Core validation that `HasType` does not track:
annotations in the profile, `global.set` only of mutable globals (`mutG`), valid
unary operators. -/
def NExpr.coreOk (mutG : Name → Bool) : NExpr → Bool
  | .block _ body ty => ty.annOk && NExpr.coreOkL mutG body
  | .loop _ body ty => ty.annOk && NExpr.coreOk mutG body
  | .if_ c t e ty =>
    ty.annOk && NExpr.coreOk mutG c && NExpr.coreOk mutG t && NExpr.coreOkO mutG e
  | .br _ v c => NExpr.coreOkO mutG v && NExpr.coreOkO mutG c
  | .switch _ _ v c => NExpr.coreOkO mutG v && NExpr.coreOk mutG c
  | .call _ args => NExpr.coreOkL mutG args
  | .localSet _ v _ => NExpr.coreOk mutG v
  | .globalSet g v => mutG g && NExpr.coreOk mutG v
  | .unary op e => op.valid && NExpr.coreOk mutG e
  | .binary _ a b => NExpr.coreOk mutG a && NExpr.coreOk mutG b
  | .select a b c => NExpr.coreOk mutG a && NExpr.coreOk mutG b && NExpr.coreOk mutG c
  | .drop e => NExpr.coreOk mutG e
  | .return_ v => NExpr.coreOkO mutG v
  | .localGet _ | .globalGet _ | .const _ | .nop | .unreachable => true
/-- `coreOk` on a list. -/
def NExpr.coreOkL (mutG : Name → Bool) : List NExpr → Bool
  | [] => true
  | e :: es => NExpr.coreOk mutG e && NExpr.coreOkL mutG es
/-- `coreOk` on an optional child. -/
def NExpr.coreOkO (mutG : Name → Bool) : Option NExpr → Bool
  | none => true
  | some e => NExpr.coreOk mutG e
end

namespace NModule

/-- Whether `g` names a mutable global (the first binding wins, as in `lookup`). -/
def mutGlobal (m : NModule) (g : Name) : Bool :=
  match m.globals.lookup g with
  | some gl => gl.type.mutability == .var
  | none => false

/-- The signatures of the function index space (imports first). -/
def sigs (m : NModule) : List (Name × List ValType × List ValType) :=
  m.imports.map (fun p => (p.1, p.2.params, p.2.results)) ++
    m.funcs.map (fun p => (p.1, p.2.params, p.2.results))

/-- **Core side conditions** that `WellTyped` does not express and Core module
validation (`Module_ok`) requires, for the profile:
* the type section is a list of plain function types (one final, parent-free,
  singleton recursive group each, as `V2.FuncType.toCoreRec` writes them), and
  imports carry the signature of their type index;
* signatures, locals and globals are `i32`/`i64` (`select` without annotation
  needs numeric operands), with at most one result;
* global initialisers are constants;
* export names are distinct (`Module_ok`);
* the start function has type `[] → []`;
* code-level conditions (`NExpr.coreOk`): annotations in the profile, `global.set`
  only of mutable globals, valid `extend` operators. -/
structure CoreReady (m : NModule) : Prop where
  types : ∃ fts : List V2.FuncType, m.types = fts.map V2.FuncType.toCoreRec
  importTypes : ∀ p ∈ m.imports,
    BModule.funcType? ⟨{ types := m.types }, []⟩ p.2.type = some ⟨p.2.params, p.2.results⟩
  sigs : ∀ x ∈ m.sigs, (∀ t ∈ x.2.1 ++ x.2.2, profileValType t = true) ∧ x.2.2.length ≤ 1
  vars : ∀ p ∈ m.funcs, ∀ t ∈ p.2.vars, profileValType t = true
  globals : ∀ p ∈ m.globals, profileValType p.2.type.value = true ∧ ∃ c, p.2.init = .const c
  exportNames : (m.exports.map NExport.name).Nodup
  start : ∀ s, m.start = some s → m.sigs.lookup s = some ([], [])
  code : ∀ p ∈ m.funcs, p.2.body.coreOk m.mutGlobal = true

end NModule

namespace ResolveValid

open Validation

/-! ### Core typing combinators -/

theorem resultOk_nil (Δ : TypeCtx) : ResultOk Δ [] := by simp [ResultOk]

theorem profile_num {t : ValType} (h : profileValType t = true) :
    ∃ nt, t = .num nt := by
  cases t with
  | num n => exact ⟨n, rfl⟩
  | vec _ => simp [profileValType] at h
  | ref _ => simp [profileValType] at h

/-- The Core type an N value type is lowered at (`i32` outside the profile, where
only bottom code can produce such a value). -/
def cvt (t : ValType) : CValType := if profileValType t then liftVal t else .num (.int .i32)

theorem cvt_of_profile {t : ValType} (h : profileValType t = true) : cvt t = liftVal t := by
  simp [cvt, h]

theorem cvt_num (t : ValType) : ∃ n, cvt t = .num n := by
  unfold cvt
  split
  · rename_i h
    obtain ⟨it, rfl⟩ := profile_num h
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem tyOk_cvt (Δ : TypeCtx) (t : ValType) : TyOk Δ (cvt t) := by
  obtain ⟨n, hn⟩ := cvt_num t
  rw [hn]; exact .num n

theorem tyOk_lift (Δ : TypeCtx) {t : ValType} (h : profileValType t = true) :
    TyOk Δ (liftVal t) := by
  rw [← cvt_of_profile h]; exact tyOk_cvt Δ t

theorem resultOk_lift (Δ : TypeCtx) {ts : List ValType}
    (h : ∀ t ∈ ts, profileValType t = true) : ResultOk Δ (ts.map liftVal) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact tyOk_lift Δ (h t ht)

theorem closeVal_profile (C : Context) {t : ValType} (h : profileValType t = true) :
    C.closeVal t = liftVal t := by
  obtain ⟨it, rfl⟩ := profile_num h
  rfl

theorem itOk {C : Context} {a b : List CValType} (ha : ResultOk C.toTypeCtx a)
    (hb : ResultOk C.toTypeCtx b) : InstrTypeOk C (.plain a b) :=
  ⟨ha, hb, by simp⟩

theorem toPlain {C : Context} {is : List Instr} {a b : List CValType} {xs : List Nat}
    (h : InstrsOk C is ⟨a, xs, b⟩) (hok : InstrTypeOk C (.plain a b)) :
    InstrsOk C is (.plain a b) :=
  .sub h ⟨ResultSub.refl _ _, ResultSub.refl _ _, by simp⟩ hok

theorem seqP {C : Context} {is₁ is₂ : List Instr} {a b c : List CValType}
    (h₁ : InstrsOk C is₁ (.plain a b)) (h₂ : InstrsOk C is₂ (.plain b c)) :
    InstrsOk C (is₁ ++ is₂) (.plain a c) :=
  InstrsOk.seq (xs₁ := []) (xs₂ := []) h₁ (by simp) h₂

theorem pairP {C : Context} {is₁ is₂ : List Instr} {a b : List CValType}
    (h₁ : InstrsOk C is₁ (.plain [] a)) (h₂ : InstrsOk C is₂ (.plain [] b))
    (ha : ResultOk C.toTypeCtx a) : InstrsOk C (is₁ ++ is₂) (.plain [] (a ++ b)) := by
  have h₂' := InstrsOk.frame (ts := a) h₂ ha
  rw [List.append_nil] at h₂'
  exact seqP h₁ h₂'

theorem opP {C : Context} {args : List BExpr} {i : Instr} {a b : List CValType} {xs : List Nat}
    (h : InstrsOk C (BExpr.lowerList args) (.plain [] a)) (hi : InstrOk C i ⟨a, xs, b⟩)
    (hok : InstrTypeOk C (.plain a b)) :
    InstrsOk C (BExpr.lowerList [.op i args]) (.plain [] b) := by
  rw [BExpr.lowerList_singleton, BExpr.lower_op]
  exact seqP h (toPlain (.instr hi) hok)

/-! ### Results of resolution -/

theorem bind_ok {ε α β : Type} {r : Except ε α} {f : α → Except ε β} {b : β}
    (h : r >>= f = .ok b) : ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b := by
  cases h; rfl

theorem toIdx_ok {k : IndexKind} {n : Nat} {x : Idx k} (h : toIdx n = .ok x) :
    x.toNat = n := by
  unfold toIdx at h
  split at h
  · rename_i i hi
    cases h
    exact ((Idx.ofNat?_eq_some_iff n x).1 hi).symm
  · cases h

theorem findIdx_ok {L : List (Option Name)} {l : Name} {d : LabelIdx}
    (h : labelDepth L l = .ok d) : L.findIdx? (· == some l) = some d.toNat := by
  unfold labelDepth at h
  split at h
  · rename_i n hn
    rw [hn, toIdx_ok h]
  · cases h

theorem func_ok {E : NameEnv} {f : Name} {x : FuncIdx} (h : E.func f = .ok x) :
    E.funcs.findIdx? (· == f) = some x.toNat := by
  unfold NameEnv.func at h
  split at h
  · rename_i n hn
    split at h
    · rename_i i hi
      cases h
      rw [hn, (Idx.ofNat?_eq_some_iff n x).1 hi]
    · cases h
  · cases h

theorem global_ok {E : NameEnv} {g : Name} {x : GlobalIdx} (h : E.global g = .ok x) :
    E.globals.findIdx? (· == g) = some x.toNat := by
  unfold NameEnv.global at h
  split at h
  · rename_i n hn
    split at h
    · rename_i i hi
      cases h
      rw [hn, (Idx.ofNat?_eq_some_iff n x).1 hi]
    · cases h
  · cases h

theorem mapM_ok {α β : Type} {f : α → Except ResolveErr β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ b ∈ l', ∃ a ∈ l, f a = .ok b
  | [], l', h => by
    rw [List.mapM_nil] at h
    cases h
    simp
  | x :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases pure_ok h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨x, by simp, hb⟩
    · obtain ⟨a, ha, hfa⟩ := mapM_ok hbs c hc
      exact ⟨a, by simp [ha], hfa⟩

/-! ### The invariant of the body induction -/

/-- The Core results of an N type (`unreachable` scopes are written with the empty
block type). -/
def resTys : NTy → List CValType
  | .val t => [liftVal t]
  | _ => []

/-- What the lowered code of an expression of N type `t` is typed at. -/
def Out (C : Context) : NTy → List Instr → Prop
  | .unreachable, code => ∀ ts, ResultOk C.toTypeCtx ts → InstrsOk C code (.plain [] ts)
  | .none, code => InstrsOk C code (.plain [] [])
  | .val t, code => InstrsOk C code (.plain [] [cvt t])

theorem out_sub {C : Context} {a b : NTy} {code : List Instr} (h : Out C a code)
    (hs : NTy.Sub a b) : Out C b code := by
  by_cases ha : a = .unreachable
  · subst ha
    cases b with
    | unreachable => exact h
    | none => exact h [] (resultOk_nil _)
    | val t =>
      exact h [cvt t] (by intro x hx; simp at hx; subst hx; exact tyOk_cvt _ t)
  · have : a = b := by cases a <;> simp_all [NTy.Sub]
    subst this; exact h

theorem out_prepend {C : Context} {t : NTy} {A B : List Instr}
    (hA : InstrsOk C A (.plain [] [])) (hB : Out C t B) : Out C t (A ++ B) := by
  cases t with
  | unreachable => exact fun ts hts => seqP hA (hB ts hts)
  | none => exact seqP hA hB
  | val t => exact seqP hA hB

/-- The invariant relating the N environment, the break stack and the Core context. -/
structure BodyInv (Γ : NEnv) (E : NameEnv) (mutG : Name → Bool) (Λ : List (Name × NTy))
    (L : List (Option Name)) (D : Context) : Prop where
  locals : ∀ (i : Nat) (t : ValType), Γ.locals[i]? = some t →
    profileValType t = true ∧ D.locals[i]? = some (LocalType.mk .set (liftVal t))
  globals : ∀ (g : Name) (t : ValType), Γ.globals.lookup g = some t → profileValType t = true ∧
    ∀ k, E.global g = .ok k → ∃ mu : Mutability,
      D.globals[k.toNat]? = some (CGlobalType.mk mu (liftVal t)) ∧ (mutG g = true → mu = .var)
  funcs : ∀ (f : Name) (ps rs : List ValType), Γ.funcs.lookup f = some (ps, rs) →
    (∀ t ∈ ps ++ rs, profileValType t = true) ∧ rs.length ≤ 1 ∧
    ∀ k, E.func f = .ok k → ∃ d, D.funcs[k.toNat]? = some d ∧
      Expand d (.func (Ty.ofList (ps.map liftVal)) (Ty.ofList (rs.map liftVal)))
  ret : (∀ t ∈ Γ.results, profileValType t = true) ∧ Γ.results.length ≤ 1 ∧
    D.return_ = some (Γ.results.map liftVal)
  labels : ∀ (n : Name) (τ : NTy) (k : Nat), Λ.lookup n = some τ →
    L.findIdx? (· == some n) = some k → D.labels[k]? = some (resTys τ)
  labelsProfile : ∀ (n : Name) (t : ValType), Λ.lookup n = some (.val t) →
    profileValType t = true

theorem BodyInv.push {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {L : List (Option Name)} {D : Context} (hI : BodyInv Γ E mutG Λ L D) (l : Option Name)
    (τ : NTy) (hτ : τ.annOk = true) :
    BodyInv Γ E mutG (pushLabel l τ Λ) (l :: L) (D.withLabel (resTys τ)) where
  locals := hI.locals
  globals := hI.globals
  funcs := hI.funcs
  ret := hI.ret
  labels := by
    intro n τ' k hn hk
    cases l with
    | none =>
      rw [List.findIdx?_cons] at hk
      simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, Option.map_eq_some_iff] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      exact hI.labels n τ' k' hn hk'
    | some l =>
      rw [List.findIdx?_cons] at hk
      by_cases hl : n = l
      · subst hl
        simp only [beq_self_eq_true, eq_self, ↓reduceIte, Option.some.injEq] at hk
        subst hk
        simp only [pushLabel, List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hn
        subst hn
        rfl
      · have hb : (some l == some n) = false := by
          rw [beq_eq_false_iff_ne]
          intro h
          exact hl (Option.some.inj h).symm
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hk
        obtain ⟨k', hk', rfl⟩ := hk
        have hb' : (n == l) = false := by simpa using hl
        simp only [pushLabel, List.lookup_cons, hb'] at hn
        exact hI.labels n τ' k' hn hk'
  labelsProfile := by
    intro n t hn
    cases l with
    | none => exact hI.labelsProfile n t hn
    | some l =>
      by_cases hl : n = l
      · subst hl
        simp only [pushLabel, List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hn
        subst hn
        simpa [NTy.annOk] using hτ
      · have hb' : (n == l) = false := by simpa using hl
        simp only [pushLabel, List.lookup_cons, hb'] at hn
        exact hI.labelsProfile n t hn

theorem BodyInv.scope {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {L : List (Option Name)} {D : Context} (hI : BodyInv Γ E mutG Λ L D) (ts : List CValType) :
    BodyInv Γ E mutG Λ (none :: L) (D.withLabel ts) where
  locals := hI.locals
  globals := hI.globals
  funcs := hI.funcs
  ret := hI.ret
  labels := by
    intro n τ' k hn hk
    rw [List.findIdx?_cons] at hk
    simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, Option.map_eq_some_iff] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact hI.labels n τ' k' hn hk'
  labelsProfile := hI.labelsProfile

theorem blockTypeOk {C : Context} {τ : NTy} (hτ : τ.annOk = true) :
    BlockTypeOk C τ.blockType [] (resTys τ) := by
  cases τ with
  | none => exact .empty
  | unreachable => exact .empty
  | val t =>
    have hp : profileValType t = true := by simpa [NTy.annOk] using hτ
    have := BlockTypeOk.value (C := C) (t := t)
      (by rw [closeVal_profile C hp]; exact tyOk_lift _ hp)
    rw [closeVal_profile C hp] at this
    exact this

theorem resultOk_resTys (Δ : TypeCtx) {τ : NTy} (hτ : τ.annOk = true) :
    ResultOk Δ (resTys τ) := by
  cases τ with
  | val t =>
    have hp : profileValType t = true := by simpa [NTy.annOk] using hτ
    intro x hx
    simp only [resTys, List.mem_singleton] at hx
    subst hx
    exact tyOk_lift Δ hp
  | _ => exact resultOk_nil _

theorem resultOk_resTys_of (Δ : TypeCtx) {τ : NTy}
    (hτ : ∀ t, τ = .val t → profileValType t = true) : ResultOk Δ (resTys τ) := by
  cases τ with
  | val t => exact resultOk_resTys Δ (by simpa [NTy.annOk] using hτ t rfl)
  | _ => exact resultOk_nil _

theorem resultOk_one (Δ : TypeCtx) (n : NumType) : ResultOk Δ [.num n] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact .num n

theorem resultOk_two (Δ : TypeCtx) (n n' : NumType) : ResultOk Δ [.num n, .num n'] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact .num _

theorem resultOk_cvt (Δ : TypeCtx) (t : ValType) : ResultOk Δ [cvt t] := by
  obtain ⟨n, hn⟩ := cvt_num t
  rw [hn]; exact resultOk_one Δ n

/-- The body of a scope of type `τ`, at the scope's results. -/
theorem out_res {C : Context} {τ : NTy} {code : List Instr} (hτ : τ.annOk = true)
    (h : Out C τ code) : InstrsOk C code (.plain [] (resTys τ)) := by
  cases τ with
  | none => exact h
  | unreachable => exact h [] (resultOk_nil _)
  | val t =>
    have hp : profileValType t = true := by simpa [NTy.annOk] using hτ
    have h' : InstrsOk C code (.plain [] [cvt t]) := h
    rw [cvt_of_profile hp] at h'
    exact h'

/-- A scope of type `τ` (written with block type `τ.blockType`, then `τ.tail`), after a
prefix `P` computing its operands `a`. -/
theorem out_scope {C : Context} {τ : NTy} {i : Instr} {P : List Instr} {a : List CValType}
    (hτ : τ.annOk = true) (hP : InstrsOk C P (.plain [] a))
    (hi : InstrOk C i (.plain a (resTys τ))) :
    Out C τ (P ++ i :: BExpr.lowerList τ.tail) := by
  cases τ with
  | none => exact seqP hP (.instr hi)
  | val t =>
    have hp : profileValType t = true := by simpa [NTy.annOk] using hτ
    show InstrsOk C (P ++ [i]) (.plain [] [cvt t])
    rw [cvt_of_profile hp]
    exact seqP hP (.instr hi)
  | unreachable =>
    intro ts hts
    have e : P ++ i :: BExpr.lowerList NTy.unreachable.tail = (P ++ [i]) ++ [.unreachable] := by
      simp [NTy.tail]
    rw [e]
    exact seqP (seqP hP (.instr hi))
      (.instr (.parametric (.unreachable (itOk (resultOk_nil _) hts))))

theorem cvt_intValType (it : IntType) : cvt (intValType it) = .num (.int it) := by
  cases it <;> rfl

theorem lowerList_if (bt : BlockType) (c t e tail : List BExpr) :
    BExpr.lowerList (.if_ bt c t e :: tail) =
      BExpr.lowerList c ++
        (.if_ bt (BExpr.lowerList t) (BExpr.lowerList e) :: BExpr.lowerList tail) := by
  rw [BExpr.lowerList_cons]
  simp only [BExpr.lower, List.append_assoc, List.singleton_append]

/-! ### The body induction -/

mutual
theorem body_E {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {e : NExpr} {t : NTy} (h : HasType Γ Λ e t) :
    ∀ (L : List (Option Name)) (D : Context) (bs : List BExpr), BodyInv Γ E mutG Λ L D →
      e.coreOk mutG = true → resolveE E L e = .ok bs → Out D t (BExpr.lowerList bs) :=
  match h with
  | .sub h hs => fun L D bs hI hc hr => out_sub (body_E h L D bs hI hc hr) hs
  | .const c => fun _ D bs _ _ hr => by
    cases pure_ok hr
    cases c with
    | i32 b => exact .instr (.numeric (.intConst .i32 b))
    | i64 b => exact .instr (.numeric (.intConst .i64 b))
  | .localGet (i := i) (t := t) hi => fun _ D bs hI _ hr => by
    obtain ⟨x, hx, hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨hp, hl⟩ := hI.locals i t hi
    show InstrsOk D [.localGet x] (.plain [] [cvt t])
    rw [cvt_of_profile hp]
    exact .instr (.variable (.localGet (by rw [toIdx_ok hx]; exact hl)))
  | .localSet (i := i) (v := v) (t := t) hi hv => fun L D bs hI hc hr => by
    obtain ⟨x, hx, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨hp, hl⟩ := hI.locals i t hi
    have ih : InstrsOk D (BExpr.lowerList v') (.plain [] [cvt t]) := body_E hv L D v' hI hc hv'
    rw [cvt_of_profile hp] at ih
    show InstrsOk D (BExpr.lowerList [.op (.localSet x) v']) (.plain [] [])
    exact opP ih (.variable (.localSet (by rw [toIdx_ok hx]; exact hl)))
      (itOk (resultOk_lift _ (ts := [t]) (by simpa using hp)) (resultOk_nil _))
  | .localTee (i := i) (v := v) (t := t) hi hv => fun L D bs hI hc hr => by
    obtain ⟨x, hx, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨hp, hl⟩ := hI.locals i t hi
    have ih : InstrsOk D (BExpr.lowerList v') (.plain [] [cvt t]) := body_E hv L D v' hI hc hv'
    rw [cvt_of_profile hp] at ih
    show InstrsOk D (BExpr.lowerList [.op (.localTee x) v']) (.plain [] [cvt t])
    rw [cvt_of_profile hp]
    exact opP ih (.variable (.localTee (by rw [toIdx_ok hx]; exact hl)))
      (itOk (resultOk_lift _ (ts := [t]) (by simpa using hp))
        (resultOk_lift _ (ts := [t]) (by simpa using hp)))
  | .globalGet (g := g) (t := t) hg => fun _ D bs hI _ hr => by
    obtain ⟨hp, hk⟩ := hI.globals g t hg
    obtain ⟨k, hx, hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨mu, hd, -⟩ := hk k hx
    show InstrsOk D [.globalGet k] (.plain [] [cvt t])
    rw [cvt_of_profile hp]
    exact .instr (.variable (.globalGet hd))
  | .globalSet (g := g) (v := v) (t := t) hg hv => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨hp, hk⟩ := hI.globals g t hg
    obtain ⟨k, hx, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨mu, hd, hm⟩ := hk k hx
    have ih : InstrsOk D (BExpr.lowerList v') (.plain [] [cvt t]) :=
      body_E hv L D v' hI hc.2 hv'
    rw [cvt_of_profile hp] at ih
    rw [hm hc.1] at hd
    exact opP ih (.variable (.globalSet hd))
      (itOk (resultOk_lift _ (ts := [t]) (by simpa using hp)) (resultOk_nil _))
  | .unary (op := op) (e := e) hv => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨e', he', hr⟩ := bind_ok hr
    cases pure_ok hr
    have ih : InstrsOk D (BExpr.lowerList e') (.plain [] [cvt op.argTy]) :=
      body_E hv L D e' hI hc.2 he'
    cases op with
    | int it o =>
      have hval : o.valid it = true := hc.1
      change InstrsOk D (BExpr.lowerList e') (.plain [] [cvt (intValType it)]) at ih
      rw [cvt_intValType] at ih
      show InstrsOk D (BExpr.lowerList [.op (.intUnOp it o) e']) (.plain [] [cvt (intValType it)])
      rw [cvt_intValType]
      exact opP ih (.numeric (.intUnOp hval)) (itOk (resultOk_one _ _) (resultOk_one _ _))
    | eqz it =>
      change InstrsOk D (BExpr.lowerList e') (.plain [] [cvt (intValType it)]) at ih
      rw [cvt_intValType] at ih
      show InstrsOk D (BExpr.lowerList [.op (.intTestOp it .eqz) e'])
        (.plain [] [.num (.int .i32)])
      exact opP ih (.numeric (.intTestOp it .eqz)) (itOk (resultOk_one _ _) (resultOk_one _ _))
  | .binary (op := op) (a := a) (b := b) ha hb => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨a', ha', hr⟩ := bind_ok hr
    obtain ⟨b', hb', hr⟩ := bind_ok hr
    cases pure_ok hr
    have iha : InstrsOk D (BExpr.lowerList a') (.plain [] [cvt op.argTy]) :=
      body_E ha L D a' hI hc.1 ha'
    have ihb : InstrsOk D (BExpr.lowerList b') (.plain [] [cvt op.argTy]) :=
      body_E hb L D b' hI hc.2 hb'
    cases op with
    | int it o =>
      change InstrsOk D (BExpr.lowerList a') (.plain [] [cvt (intValType it)]) at iha
      change InstrsOk D (BExpr.lowerList b') (.plain [] [cvt (intValType it)]) at ihb
      rw [cvt_intValType] at iha ihb
      have hab := pairP iha ihb (resultOk_one _ _)
      rw [← BExpr.lowerList_append] at hab
      show InstrsOk D (BExpr.lowerList [.op (.intBinOp it o) (a' ++ b')])
        (.plain [] [cvt (intValType it)])
      rw [cvt_intValType]
      exact opP hab (.numeric (.intBinOp it o)) (itOk (resultOk_two _ _ _) (resultOk_one _ _))
    | rel it o =>
      change InstrsOk D (BExpr.lowerList a') (.plain [] [cvt (intValType it)]) at iha
      change InstrsOk D (BExpr.lowerList b') (.plain [] [cvt (intValType it)]) at ihb
      rw [cvt_intValType] at iha ihb
      have hab := pairP iha ihb (resultOk_one _ _)
      rw [← BExpr.lowerList_append] at hab
      show InstrsOk D (BExpr.lowerList [.op (.intRelOp it o) (a' ++ b')])
        (.plain [] [.num (.int .i32)])
      exact opP hab (.numeric (.intRelOp it o)) (itOk (resultOk_two _ _ _) (resultOk_one _ _))
  | .select (a := a) (b := b) (c := c) (t := t) ha hb hcnd => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨a', ha', hr⟩ := bind_ok hr
    obtain ⟨b', hb', hr⟩ := bind_ok hr
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    cases pure_ok hr
    have iha : InstrsOk D (BExpr.lowerList a') (.plain [] [cvt t]) :=
      body_E ha L D a' hI hc.1.1 ha'
    have ihb : InstrsOk D (BExpr.lowerList b') (.plain [] [cvt t]) :=
      body_E hb L D b' hI hc.1.2 hb'
    have ihc : InstrsOk D (BExpr.lowerList c') (.plain [] [.num (.int .i32)]) :=
      body_E hcnd L D c' hI hc.2 hc'
    obtain ⟨n, hn⟩ := cvt_num t
    rw [hn] at iha ihb
    have habc := pairP (pairP iha ihb (resultOk_one _ _)) ihc (resultOk_two _ _ _)
    rw [← BExpr.lowerList_append, ← BExpr.lowerList_append] at habc
    show InstrsOk D (BExpr.lowerList [.op (.select none) (a' ++ b' ++ c')]) (.plain [] [cvt t])
    rw [hn]
    refine opP habc (.parametric (.selectImpl (.num n) .num trivial)) (itOk ?_ (resultOk_one _ _))
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
      List.nil_append] at hx
    rcases hx with rfl | rfl | rfl <;> exact .num _
  | .drop (e := e) (t := t) hv => fun L D bs hI hc hr => by
    obtain ⟨e', he', hr⟩ := bind_ok hr
    cases pure_ok hr
    have ih : InstrsOk D (BExpr.lowerList e') (.plain [] [cvt t]) := body_E hv L D e' hI hc he'
    exact opP ih (.parametric (.drop (tyOk_cvt _ t))) (itOk (resultOk_cvt _ t) (resultOk_nil _))
  | .nop => fun _ D bs _ _ hr => by
    cases pure_ok hr
    exact .instr (.parametric .nop)
  | .unreachable => fun _ D bs _ _ hr => by
    cases pure_ok hr
    intro ts hts
    exact .instr (.parametric (.unreachable (itOk (resultOk_nil _) hts)))
  | .returnNone hr0 => fun _ D bs hI _ hr => by
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    cases pure_ok hr
    cases hv'
    intro ts hts
    have hret := hI.ret.2.2
    rw [hr0] at hret
    exact .instr (.return_ (t₁ := []) hret (itOk (resultOk_nil _) hts))
  | .returnSome (v := v) (t := t) hr0 hv => fun L D bs hI hc hr => by
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    cases pure_ok hr
    have hp : profileValType t = true := hI.ret.1 t (by simp [hr0])
    have ih : InstrsOk D (BExpr.lowerList v') (.plain [] [cvt t]) := body_E hv L D v' hI hc hv'
    rw [cvt_of_profile hp] at ih
    have hret := hI.ret.2.2
    rw [hr0] at hret
    intro ts hts
    exact opP ih (.return_ (t₁ := []) hret (itOk (resultOk_nil _) hts))
      (itOk (resultOk_lift _ (ts := [t]) (by simpa using hp)) hts)
  | .br (l := l) (v := v) (vt := vt) hl hv => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨d, hd, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    cases pure_ok hr
    cases hc'
    have hlab := hI.labels l vt d.toNat hl (findIdx_ok hd)
    have hprof : ∀ t, vt = .val t → profileValType t = true :=
      fun t ht => hI.labelsProfile l t (ht ▸ hl)
    have ih := body_O hv L D v' hI hc.1 hv' hprof
    intro ts hts
    show InstrsOk D (BExpr.lowerList [.op (.br d) (v' ++ [])]) (.plain [] ts)
    rw [List.append_nil]
    exact opP ih (.br (t₁ := []) hlab (itOk (resultOk_nil _) hts))
      (itOk (resultOk_resTys_of _ hprof) hts)
  | .brIf (l := l) (v := v) (c := c) (vt := vt) hl hv hcnd => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, NExpr.coreOkO, Bool.and_eq_true] at hc
    obtain ⟨d, hd, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    cases pure_ok hr
    have hlab := hI.labels l vt d.toNat hl (findIdx_ok hd)
    have hprof : ∀ t, vt = .val t → profileValType t = true :=
      fun t ht => hI.labelsProfile l t (ht ▸ hl)
    have ihv := body_O hv L D v' hI hc.1 hv' hprof
    have ihc : InstrsOk D (BExpr.lowerList c') (.plain [] [.num (.int .i32)]) :=
      body_E hcnd L D c' hI hc.2 hc'
    have hops := pairP ihv ihc (resultOk_resTys_of _ hprof)
    rw [← BExpr.lowerList_append] at hops
    have key : InstrsOk D (BExpr.lowerList [.op (.brIf d) (v' ++ c')]) (.plain [] (resTys vt)) :=
      opP hops (.brIf hlab)
        (itOk (ResultOk.append (resultOk_resTys_of _ hprof) (resultOk_one _ _))
          (resultOk_resTys_of _ hprof))
    cases vt with
    | none => exact key
    | unreachable => cases hv
    | val t =>
      show InstrsOk D (BExpr.lowerList [.op (.brIf d) (v' ++ c')]) (.plain [] [cvt t])
      rw [cvt_of_profile (hprof t rfl)]
      exact key
  | .switch (ls := ls) (d := d) (v := v) (c := c) (vt := vt) hls hv hcnd =>
    fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨ds, hds, hr⟩ := bind_ok hr
    obtain ⟨dd, hdd, hr⟩ := bind_ok hr
    obtain ⟨v', hv', hr⟩ := bind_ok hr
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    cases pure_ok hr
    have hprof : ∀ t, vt = .val t → profileValType t = true :=
      fun t ht => hI.labelsProfile d t (ht ▸ hls d List.mem_cons_self)
    have ihv := body_O hv L D v' hI hc.1 hv' hprof
    have ihc : InstrsOk D (BExpr.lowerList c') (.plain [] [.num (.int .i32)]) :=
      body_E hcnd L D c' hI hc.2 hc'
    have hops := pairP ihv ihc (resultOk_resTys_of _ hprof)
    rw [← BExpr.lowerList_append] at hops
    intro ts hts
    have hin : ResultOk D.toTypeCtx (resTys vt ++ [.num (.int .i32)]) :=
      ResultOk.append (resultOk_resTys_of _ hprof) (resultOk_one _ _)
    refine opP hops (.brTable (t₁ := []) (ts := resTys vt) ?_ ?_ (itOk hin hts)) (itOk hin hts)
    · intro x hx
      obtain ⟨n, hn, hxn⟩ := mapM_ok hds x hx
      exact ⟨_, hI.labels n vt x.toNat (hls n (List.mem_cons_of_mem _ hn)) (findIdx_ok hxn),
        ResultSub.refl _ _⟩
    · exact ⟨_, hI.labels d vt dd.toNat (hls d List.mem_cons_self) (findIdx_ok hdd),
        ResultSub.refl _ _⟩
  | .call (f := f) (args := args) (ps := ps) (rs := rs) hf hargs => fun L D bs hI hc hr => by
    obtain ⟨hp, hlen, hk⟩ := hI.funcs f ps rs hf
    obtain ⟨k, hfi, hr⟩ := bind_ok hr
    obtain ⟨as, has, hr⟩ := bind_ok hr
    cases pure_ok hr
    obtain ⟨dfn, hdk, hex⟩ := hk k hfi
    have ih := body_L hargs L D as hI hc has (fun t ht => hp t (List.mem_append_left _ ht))
    have hcall : InstrOk D (.call k) (.plain (ps.map liftVal) (rs.map liftVal)) := by
      have := InstrOk.call hdk hex
      simpa [Ty.toList_ofList] using this
    have hcode := opP ih hcall
      (itOk (resultOk_lift _ (fun t ht => hp t (List.mem_append_left _ ht)))
        (resultOk_lift _ (fun t ht => hp t (List.mem_append_right _ ht))))
    rcases rs with _ | ⟨t, _ | ⟨t', rs'⟩⟩
    · exact hcode
    · show InstrsOk D (BExpr.lowerList [.op (.call k) as]) (.plain [] [cvt t])
      rw [cvt_of_profile (hp t (by simp))]
      exact hcode
    · simp at hlen
  | .block (l := l) (body := body) (ty := ty) hs => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    have ih := body_S (E := E) (mutG := mutG) hs
    cases l with
    | none => exact ih L D bs hI hc.2 hr
    | some n =>
      obtain ⟨b, hb, hr⟩ := bind_ok hr
      cases pure_ok hr
      have hbody := ih (some n :: L) (D.withLabel (resTys ty)) b (hI.push (some n) ty hc.1) hc.2 hb
      exact out_scope (P := []) hc.1 .nil (.block (blockTypeOk hc.1) (out_res hc.1 hbody))
  | .loop (l := l) (body := body) (ty := ty) hb => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨b, hb', hr⟩ := bind_ok hr
    cases pure_ok hr
    have hbody := body_E hb (l :: L) (D.withLabel (resTys .none)) b (hI.push l .none rfl) hc.2 hb'
    exact out_scope (P := []) hc.1 .nil (.loop (blockTypeOk hc.1) (out_res hc.1 hbody))
  | .ifElse (c := c) (t := t) (e := e) (ty := ty) hcnd ht he => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, NExpr.coreOkO, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hann, hcc⟩, hct⟩, hce⟩ := hc
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    obtain ⟨t', ht', hr⟩ := bind_ok hr
    obtain ⟨e', he', hr⟩ := bind_ok hr
    cases pure_ok hr
    have ihc : InstrsOk D (BExpr.lowerList c') (.plain [] [.num (.int .i32)]) :=
      body_E hcnd L D c' hI hcc hc'
    have iht := body_E ht (none :: L) (D.withLabel (resTys ty)) t' (hI.scope _) hct ht'
    have ihe := body_E he (none :: L) (D.withLabel (resTys ty)) e' (hI.scope _) hce he'
    have hif : InstrOk D (.if_ ty.blockType (BExpr.lowerList t') (BExpr.lowerList e'))
        (.plain [.num (.int .i32)] (resTys ty)) :=
      .if_ (t₁ := []) (blockTypeOk hann) (out_res hann iht) (out_res hann ihe)
    rw [lowerList_if]
    exact out_scope hann ihc hif
  | .ifNoElse (c := c) (t := t) hcnd ht => fun L D bs hI hc hr => by
    simp only [NExpr.coreOk, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨_, hcc⟩, hct⟩, _⟩ := hc
    obtain ⟨c', hc', hr⟩ := bind_ok hr
    obtain ⟨t', ht', hr⟩ := bind_ok hr
    obtain ⟨e', he', hr⟩ := bind_ok hr
    cases pure_ok hr
    cases he'
    have ihc : InstrsOk D (BExpr.lowerList c') (.plain [] [.num (.int .i32)]) :=
      body_E hcnd L D c' hI hcc hc'
    have iht := body_E ht (none :: L) (D.withLabel (resTys .none)) t' (hI.scope _) hct ht'
    have hif : InstrOk D (.if_ NTy.none.blockType (BExpr.lowerList t') (BExpr.lowerList []))
        (.plain [.num (.int .i32)] (resTys .none)) :=
      .if_ (t₁ := []) (xs₂ := []) (blockTypeOk rfl) (out_res rfl iht) .nil
    rw [lowerList_if]
    exact out_scope (τ := .none) rfl ihc hif
theorem body_O {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {v : Option NExpr} {vt : NTy} (h : HasTypeOpt Γ Λ v vt) :
    ∀ (L : List (Option Name)) (D : Context) (bs : List BExpr), BodyInv Γ E mutG Λ L D →
      NExpr.coreOkO mutG v = true → resolveO E L v = .ok bs →
      (∀ t, vt = .val t → profileValType t = true) →
      InstrsOk D (BExpr.lowerList bs) (.plain [] (resTys vt)) :=
  match h with
  | .absent => fun _ _ bs _ _ hr _ => by
    cases pure_ok hr
    exact .nil
  | .present (t := t) he => fun L D bs hI hc hr hp => by
    have ih : InstrsOk D (BExpr.lowerList bs) (.plain [] [cvt t]) := body_E he L D bs hI hc hr
    rw [cvt_of_profile (hp t rfl)] at ih
    exact ih
theorem body_L {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {args : List NExpr} {ps : List ValType} (h : HasTypes Γ Λ args ps) :
    ∀ (L : List (Option Name)) (D : Context) (bs : List BExpr), BodyInv Γ E mutG Λ L D →
      NExpr.coreOkL mutG args = true → resolveL E L args = .ok bs →
      (∀ t ∈ ps, profileValType t = true) →
      InstrsOk D (BExpr.lowerList bs) (.plain [] (ps.map liftVal)) :=
  match h with
  | .nil => fun _ _ bs _ _ hr _ => by
    cases pure_ok hr
    exact .nil
  | .cons (t := t) he hes => fun L D bs hI hc hr hp => by
    simp only [NExpr.coreOkL, Bool.and_eq_true] at hc
    obtain ⟨a, ha, hr⟩ := bind_ok hr
    obtain ⟨b, hb, hr⟩ := bind_ok hr
    cases pure_ok hr
    have ih : InstrsOk D (BExpr.lowerList a) (.plain [] [cvt t]) := body_E he L D a hI hc.1 ha
    rw [cvt_of_profile (hp t (by simp))] at ih
    have ihs := body_L hes L D b hI hc.2 hb (fun t' ht' => hp t' (by simp [ht']))
    rw [BExpr.lowerList_append]
    exact pairP ih ihs (resultOk_lift _ (ts := [t]) (by simpa using hp t (by simp)))
theorem body_S {Γ : NEnv} {E : NameEnv} {mutG : Name → Bool} {Λ : List (Name × NTy)}
    {body : List NExpr} {ty : NTy} (h : HasTypeSeq Γ Λ body ty) :
    ∀ (L : List (Option Name)) (D : Context) (bs : List BExpr), BodyInv Γ E mutG Λ L D →
      NExpr.coreOkL mutG body = true → resolveL E L body = .ok bs →
      Out D ty (BExpr.lowerList bs) :=
  match h with
  | .nil hs => fun _ _ bs _ _ hr => by
    cases pure_ok hr
    have : ty = .none := by cases ty <;> simp_all [NTy.Sub]
    subst this
    exact .nil
  | .last he => fun L D bs hI hc hr => by
    simp only [NExpr.coreOkL, Bool.and_eq_true] at hc
    obtain ⟨a, ha, hr⟩ := bind_ok hr
    obtain ⟨b, hb, hr⟩ := bind_ok hr
    cases pure_ok hr
    cases hb
    rw [List.append_nil]
    exact body_E he L D a hI hc.1 ha
  | .cons (e := e) (e' := e') (es := es) he hrest => fun L D bs hI hc hr => by
    have hc : NExpr.coreOk mutG e = true ∧ NExpr.coreOkL mutG (e' :: es) = true := by
      rw [← Bool.and_eq_true]; exact hc
    obtain ⟨a, ha, hr⟩ := bind_ok hr
    obtain ⟨b, hb, hr⟩ := bind_ok hr
    cases pure_ok hr
    rw [BExpr.lowerList_append]
    exact out_prepend (body_E he L D a hI hc.1 ha) (body_S hrest L D b hI hc.2 hb)
end

/-! ### Module-level assembly -/

theorem lookup_map_snd {α β : Type} (f : α → β) (g : Name) :
    ∀ l : List (Name × α), (l.map (fun q => (q.1, f q.2))).lookup g = (l.lookup g).map f
  | [] => rfl
  | (k, v) :: l => by
    by_cases hk : g = k
    · subst hk; simp
    · have hb : (g == k) = false := by simpa using hk
      simp only [List.map_cons, List.lookup_cons, hb]
      exact lookup_map_snd f g l

theorem findIdx_lookup {α : Type} (g : Name) :
    ∀ (l : List (Name × α)) (n : Nat), (l.map Prod.fst).findIdx? (· == g) = some n →
      ∃ p, l[n]? = some p ∧ l.lookup g = some p.2
  | [], n, h => by simp at h
  | (k, v) :: l, n, h => by
    rw [List.map_cons, List.findIdx?_cons] at h
    by_cases hk : k = g
    · subst hk
      simp only [beq_self_eq_true, eq_self, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨(k, v), rfl, by simp⟩
    · have hb : (k == g) = false := by simpa using hk
      simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨n', hn', rfl⟩ := h
      obtain ⟨p, hp, hl⟩ := findIdx_lookup g l n' hn'
      have hb' : (g == k) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hk h.symm
      exact ⟨p, by simpa using hp, by simp only [List.lookup_cons, hb']; exact hl⟩

theorem lookup_mem {α : Type} (g : Name) {b : α} :
    ∀ {l : List (Name × α)}, l.lookup g = some b → (g, b) ∈ l
  | [], h => by simp at h
  | (k, v) :: l, h => by
    by_cases hk : g = k
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (g == k) = false := by simpa using hk
      simp only [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (lookup_mem g h)

theorem mapM_forall₂ {α β : Type} {f : α → Except ResolveErr β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    rw [List.mapM_nil] at h
    cases h
    exact .nil
  | x :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases pure_ok h
    exact .cons hb (mapM_forall₂ hbs)

theorem exists_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := exists_forall₂ (l := l) (fun x hx => h x (by simp [hx]))
    exact ⟨b :: l', .cons hb hl'⟩

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    ∀ {l : List α}, (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_map f g (fun x hx => h x (by simp [hx])))

theorem forall₂_map_of {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    (f : β → γ) (g : α → δ) :
    ∀ {l : List α} {l' : List β}, (∀ a ∈ l, ∀ b, R a b → S (f b) (g a)) →
      List.Forall₂ R l l' → List.Forall₂ S (l'.map f) (l.map g)
  | [], [], _, .nil => .nil
  | a :: l, b :: l', h, .cons hab hl =>
    .cons (h a (by simp) b hab) (forall₂_map_of f g (fun x hx => h x (by simp [hx])) hl)

theorem forall₂_map_eq {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b => g b = f a) l l' → l'.map g = l.map f
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by simp [h, forall₂_map_eq f g hl]

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, _, h => by simp at h
  | a :: l, b :: l', .cons hab hl, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨y, hy, hr⟩ := forall₂_mem hl x hx
      exact ⟨y, by simp [hy], hr⟩

theorem hasType_const {Γ : NEnv} {Λ : List (Name × NTy)} {e : NExpr} {t : NTy}
    (h : HasType Γ Λ e t) : ∀ c, e = .const c → t = .val c.ty :=
  match h with
  | .sub h hs => fun c he => by
    have := hasType_const h c he
    subst this
    cases t <;> simp_all [NTy.Sub]
  | .const _ => fun _ he => by cases he; rfl
  | .localGet _ => fun _ he => nomatch he
  | .localSet _ _ => fun _ he => nomatch he
  | .localTee _ _ => fun _ he => nomatch he
  | .globalGet _ => fun _ he => nomatch he
  | .globalSet _ _ => fun _ he => nomatch he
  | .unary _ => fun _ he => nomatch he
  | .binary _ _ => fun _ he => nomatch he
  | .select _ _ _ => fun _ he => nomatch he
  | .drop _ => fun _ he => nomatch he
  | .nop => fun _ he => nomatch he
  | .unreachable => fun _ he => nomatch he
  | .returnNone _ => fun _ he => nomatch he
  | .returnSome _ _ => fun _ he => nomatch he
  | .br _ _ => fun _ he => nomatch he
  | .brIf _ _ _ => fun _ he => nomatch he
  | .switch _ _ _ => fun _ he => nomatch he
  | .call _ _ => fun _ he => nomatch he
  | .block _ => fun _ he => nomatch he
  | .loop _ => fun _ he => nomatch he
  | .ifElse _ _ _ => fun _ he => nomatch he
  | .ifNoElse _ _ => fun _ he => nomatch he

theorem typeDefs_toCoreRec (fts : List V2.FuncType) :
    (fts.map V2.FuncType.toCoreRec).flatMap RecType.types =
      fts.map (fun ft => (⟨true, [], .func ft.toCore⟩ : SubType)) := by
  induction fts with
  | nil => rfl
  | cons ft fts ih =>
    rw [List.map_cons, List.flatMap_cons, ih]
    rfl

theorem funcType_types {fts : List V2.FuncType} {x : TypeIdx} {ft : FuncType}
    (h : BModule.funcType? ⟨{ types := fts.map V2.FuncType.toCoreRec }, []⟩ x = some ft) :
    ∃ v, fts[x.toNat]? = some v ∧ ft = v.toCore := by
  unfold BModule.funcType? at h
  simp only [Module.typeDefinitions, typeDefs_toCoreRec, List.getElem?_map] at h
  cases hv : fts[x.toNat]? with
  | none => simp [hv] at h
  | some v =>
    simp only [hv, Option.map_some, Option.some.injEq] at h
    exact ⟨v, rfl, h.symm⟩

theorem expand_dt (v : V2.FuncType) :
    Expand v.toDefType (.func (Ty.ofList (v.toCore.params.map liftVal))
      (Ty.ofList (v.toCore.results.map liftVal))) := by
  have := V2.Validation.expand_toDefType v
  simpa [V2.FuncType.toCore, V2.ResultType.toCore, List.map_map, Function.comp_def] using this

/-- The default `DefType` (never used at a valid index). -/
def dDefault : DefType := .defn (.group .nil) 0

/-- The Core module context of a resolved module, from its type section. -/
structure Setup (m : NModule) where
  fts : List V2.FuncType
  hfts : m.types = fts.map V2.FuncType.toCoreRec

namespace Setup

variable {m : NModule} (S : Setup m)

def dts : List DefType := S.fts.map V2.FuncType.toDefType

def dAt (x : TypeIdx) : DefType := S.dts.getD x.toNat dDefault

def funcDts : List DefType :=
  m.imports.map (fun p => S.dAt p.2.type) ++ m.funcs.map (fun p => S.dAt p.2.type)

theorem dAt_eq {x : TypeIdx} {ft : FuncType}
    (h : BModule.funcType? ⟨{ types := m.types }, []⟩ x = some ft) :
    S.dts[x.toNat]? = some (S.dAt x) ∧ (∀ Δ, TyOk Δ (S.dAt x)) ∧
      Expand (S.dAt x) (.func (Ty.ofList (ft.params.map liftVal))
        (Ty.ofList (ft.results.map liftVal))) := by
  rw [S.hfts] at h
  obtain ⟨v, hv, rfl⟩ := funcType_types h
  have hd : S.dts[x.toNat]? = some v.toDefType := by simp [dts, hv]
  have he : S.dAt x = v.toDefType := by simp [dAt, List.getD_eq_getElem?_getD, hd]
  rw [he]
  exact ⟨hd, fun Δ => V2.Validation.tyOk_toDefType Δ v, expand_dt v⟩

/-- Every function index resolves to a defined type of its signature. -/
theorem func_entry (hw : m.WellTyped) (hc : m.CoreReady) {f : Name} {k : FuncIdx}
    (hk : m.env.func f = .ok k) :
    ∃ ps rs, m.sigs.lookup f = some (ps, rs) ∧ ∃ d, S.funcDts[k.toNat]? = some d ∧
      Expand d (.func (Ty.ofList (ps.map liftVal)) (Ty.ofList (rs.map liftVal))) := by
  let U : List (Name × (List ValType × List ValType) × TypeIdx) :=
    m.imports.map (fun p => (p.1, (p.2.params, p.2.results), p.2.type)) ++
      m.funcs.map (fun p => (p.1, (p.2.params, p.2.results), p.2.type))
  have hU1 : m.env.funcs = U.map Prod.fst := by
    simp [U, NModule.env, List.map_map, Function.comp_def]
  have hU2 : m.sigs = U.map (fun q => (q.1, q.2.1)) := by
    simp [U, NModule.sigs, List.map_map, Function.comp_def]
  have hU3 : S.funcDts = U.map (fun q => S.dAt q.2.2) := by
    simp [U, funcDts, List.map_map, Function.comp_def]
  have hU4 : ∀ q ∈ U,
      BModule.funcType? ⟨{ types := m.types }, []⟩ q.2.2 = some ⟨q.2.1.1, q.2.1.2⟩ := by
    intro q hq
    simp only [U, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact hc.importTypes p hp
    · obtain ⟨ft, hft, hps, hrs⟩ := hw.types p hp
      rw [hft]
      cases ft
      simp_all
  have hfi := func_ok hk
  rw [hU1] at hfi
  obtain ⟨q, hq, hl⟩ := findIdx_lookup f U k.toNat hfi
  have hqU : q ∈ U := List.mem_of_getElem? hq
  refine ⟨q.2.1.1, q.2.1.2, ?_, S.dAt q.2.2, ?_, ?_⟩
  · rw [hU2, lookup_map_snd (fun x : (List ValType × List ValType) × TypeIdx => x.1) f U, hl]
    rfl
  · rw [hU3, List.getElem?_map, hq]; rfl
  · exact (S.dAt_eq (hU4 q hqU)).2.2

theorem funcDts_length (hw : m.WellTyped) (hc : m.CoreReady) {f : Name} {k : FuncIdx}
    (hk : m.env.func f = .ok k) : ∃ d, S.funcDts[k.toNat]? = some d := by
  obtain ⟨_, _, _, d, hd, _⟩ := S.func_entry hw hc hk
  exact ⟨d, hd⟩

end Setup

/-- The Core global types of a module's globals. -/
def gtsOf (m : NModule) : List CGlobalType :=
  m.globals.map (fun p => ⟨p.2.type.mutability, liftVal p.2.type.value⟩)

/-- Every global name resolves to the global at its index. -/
theorem global_entry {m : NModule} {g : Name} {k : GlobalIdx} (hk : m.env.global g = .ok k) :
    ∃ p, m.globals[k.toNat]? = some p ∧ m.globals.lookup g = some p.2 := by
  have hfi := global_ok hk
  exact findIdx_lookup g m.globals k.toNat hfi

theorem fenv_funcs_eq (m : NModule) (F : NFunc) : (m.fenv F).funcs = m.sigs := by
  simp only [NModule.fenv, NModule.sigs]

theorem fenv_globals_eq (m : NModule) (F : NFunc) :
    (m.fenv F).globals = m.globals.map (fun q => (q.1, q.2.type.value)) := by
  simp only [NModule.fenv]

/-- The body invariant at the entry of a function body. -/
theorem bodyInv_entry {m : NModule} (S : Setup m) (hw : m.WellTyped) (hc : m.CoreReady)
    (F : NFunc) (hF : (F.params ++ F.results ++ F.vars).all profileValType = true)
    (hlen : F.results.length ≤ 1) (C : Context)
    (hCg : C.globals = gtsOf m) (hCf : C.funcs = S.funcDts) :
    BodyInv (m.fenv F) m.env m.mutGlobal [] []
      (C.funcBody (F.params.map liftVal) (F.results.map liftVal)
        (F.vars.map fun t => ⟨.set, liftVal t⟩)) where
  locals := by
    intro i t hi
    have ht : t ∈ F.params ++ F.vars := List.mem_of_getElem? hi
    have hp : profileValType t = true := by
      simp only [List.all_eq_true] at hF
      exact hF t (by simp only [List.mem_append] at ht ⊢; tauto)
    refine ⟨hp, ?_⟩
    have e : (F.params.map liftVal).map (fun t => (⟨.set, t⟩ : LocalType)) ++
        F.vars.map (fun t => (⟨.set, liftVal t⟩ : LocalType)) =
        (F.params ++ F.vars).map (fun t => (⟨.set, liftVal t⟩ : LocalType)) := by
      simp [List.map_map, Function.comp_def]
    show ((F.params.map liftVal).map (fun t => (⟨.set, t⟩ : LocalType)) ++
      F.vars.map (fun t => (⟨.set, liftVal t⟩ : LocalType)))[i]? = _
    rw [e, List.getElem?_map]
    have hi' : (F.params ++ F.vars)[i]? = some t := hi
    rw [hi']
    rfl
  globals := by
    intro g t hg
    rw [fenv_globals_eq, lookup_map_snd (fun x : NGlobal => x.type.value) g m.globals] at hg
    obtain ⟨gl, hgl, rfl⟩ := Option.map_eq_some_iff.1 hg
    refine ⟨(hc.globals _ (lookup_mem g hgl)).1, fun k hk => ?_⟩
    obtain ⟨p, hp, hpl⟩ := global_entry hk
    rw [hpl] at hgl
    cases hgl
    refine ⟨p.2.type.mutability, ?_, ?_⟩
    · show C.globals[k.toNat]? = _
      rw [hCg]
      simp [gtsOf, hp]
    · intro hm
      simp only [NModule.mutGlobal, hpl, beq_iff_eq] at hm
      exact hm
  funcs := by
    intro f ps rs hf
    rw [fenv_funcs_eq] at hf
    have hmem := lookup_mem f hf
    obtain ⟨hp, hl⟩ := hc.sigs _ hmem
    refine ⟨hp, hl, fun k hk => ?_⟩
    obtain ⟨ps', rs', hl', d, hd, hex⟩ := S.func_entry hw hc hk
    rw [hf] at hl'
    cases hl'
    exact ⟨d, by show C.funcs[k.toNat]? = _; rw [hCf]; exact hd, hex⟩
  ret := by
    refine ⟨fun t ht => ?_, hlen, rfl⟩
    simp only [List.all_eq_true] at hF
    exact hF t (by simp only [List.mem_append]; exact Or.inl (Or.inr ht))
  labels := by intro n τ k hn; simp at hn
  labelsProfile := by intro n t hn; simp at hn

theorem out_results {C : Context} {rs : List ValType} {code : List Instr}
    (hp : ∀ t ∈ rs, profileValType t = true) (hlen : rs.length ≤ 1)
    (h : Out C (resultTy rs) code) : InstrsOk C code (.plain [] (rs.map liftVal)) := by
  rcases rs with _ | ⟨t, _ | ⟨t', rs'⟩⟩
  · exact h
  · have h' : InstrsOk C code (.plain [] [cvt t]) := h
    rw [cvt_of_profile (hp t (by simp))] at h'
    exact h'
  · simp at hlen

theorem funcs_externs {α : Type} (l : List α) (f : α → DefType) :
    CExternType.funcs (l.map fun p => CExternType.func (f p)) = l.map f := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [CExternType.funcs, ih]

theorem globals_externs {α : Type} (l : List α) (f : α → DefType) :
    CExternType.globals (l.map fun p => CExternType.func (f p)) = [] := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [CExternType.globals, ih]

theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l l' → List.Forall₂ S l l'
  | [], [], _, .nil => .nil
  | a :: l, b :: l', h, .cons hab hl =>
    .cons (h a (by simp) b hab) (forall₂_imp_mem (fun x hx => h x (by simp [hx])) hl)

theorem forall₂_self_map {α β : Type} {R : α → β → Prop} (f : α → β) :
    ∀ {l : List α}, (∀ a ∈ l, R a (f a)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_self_map f (fun x hx => h x (by simp [hx])))

/-- A resolved global of the profile: a constant of its type. -/
def GRel (p : Name × NGlobal) (g' : Global) : Prop :=
  ∃ c : Lit, g'.type = p.2.type ∧ g'.init = [c.instr] ∧ p.2.type.value = c.ty ∧
    profileValType p.2.type.value = true

theorem globalsOk_aux : ∀ {gs : List (Name × NGlobal)} {gs' : List Global} (C : Context),
    List.Forall₂ GRel gs gs' →
    GlobalsOk C gs' (gs.map fun p => ⟨p.2.type.mutability, liftVal p.2.type.value⟩)
  | [], [], _, .nil => .nil
  | p :: gs, g' :: gs', C, .cons ⟨c, h1, h2, h3, h4⟩ hrest => by
    refine .cons ⟨?_, ?_, ?_, ?_⟩ (globalsOk_aux _ hrest)
    · simp only [Context.closeGlobalType, h1, closeVal_profile C h4]
    · exact tyOk_lift _ h4
    · show InstrsOk C g'.init (.plain [] [liftVal p.2.type.value])
      rw [h2, h3]
      cases c with
      | i32 b => exact .instr (.numeric (.intConst .i32 b))
      | i64 b => exact .instr (.numeric (.intConst .i64 b))
    · intro i hi
      rw [h2] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      cases c with
      | i32 b => exact .intConst .i32 b
      | i64 b => exact .intConst .i64 b

theorem valid {m : NModule} {b : BModule} (hw : m.WellTyped) (hc : m.CoreReady)
    (hr : m.resolve = .ok b) : b.Ok := by
  obtain ⟨fts, hfts⟩ := hc.types
  let S : Setup m := ⟨fts, hfts⟩
  unfold NModule.resolve at hr
  obtain ⟨funcs', hF, hr⟩ := bind_ok hr
  obtain ⟨globals', hG, hr⟩ := bind_ok hr
  obtain ⟨exports', hX, hr⟩ := bind_ok hr
  have hFs := mapM_forall₂ hF
  have hGs := mapM_forall₂ hG
  have hXs := mapM_forall₂ hX
  have hbase : ∃ start' : Option FuncIdx,
      (∀ k, start' = some k → ∃ s, m.start = some s ∧ m.env.func s = .ok k) ∧
      b.base.start = start' ∧ b.base.types = m.types ∧
      b.base.imports = m.imports.map (fun p => ⟨p.2.module, p.2.base, .func p.2.type⟩) ∧
      b.base.globals = globals' ∧ b.base.exports = exports' ∧ b.funcs = funcs' ∧
      b.base.tags = [] ∧ b.base.memories = [] ∧ b.base.tables = [] ∧ b.base.data = [] ∧
      b.base.elems = [] := by
    cases hs : m.start with
    | none =>
      rw [hs] at hr
      have hb := pure_ok hr
      subst hb
      refine ⟨none, by simp, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      apply List.map_congr_left
      rintro ⟨n, i⟩ _
      rfl
    | some s =>
      rw [hs] at hr
      obtain ⟨k, hk, hr⟩ := bind_ok hr
      obtain ⟨st, hst, hr⟩ := bind_ok hr
      cases pure_ok hst
      have hb := pure_ok hr
      subst hb
      refine ⟨some k, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro k' hk'
        cases hk'
        exact ⟨s, rfl, hk⟩
      · apply List.map_congr_left
        rintro ⟨n, i⟩ _
        rfl
  obtain ⟨start', hst, hS, hT, hI, hGl, hEx, hFn, htg, hmem, htab, hdat, hel⟩ := hbase
  let xtI : List CExternType := m.imports.map fun p => CExternType.func (S.dAt p.2.type)
  let fdts : List DefType := m.funcs.map fun p => S.dAt p.2.type
  let C' : Context :=
    { types := S.dts, globals := CExternType.globals xtI,
      funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs b.lower }
  let C : Context := { C' with
    tags := CExternType.tags xtI ++ [], globals := C'.globals ++ gtsOf m,
    mems := CExternType.mems xtI ++ b.lower.memories,
    tables := CExternType.tables xtI ++ [],
    datas := b.lower.data.map (fun _ => ()), elems := [] }
  have hCg : C.globals = gtsOf m := by
    show CExternType.globals xtI ++ gtsOf m = gtsOf m
    rw [globals_externs]; rfl
  have hCf : C.funcs = S.funcDts := by
    show CExternType.funcs xtI ++ fdts = S.funcDts
    rw [funcs_externs]; rfl
  -- exports
  have hxt : ∃ xtE, List.Forall₂ (ExportOk C) b.lower.exports xtE := by
    apply exists_forall₂
    intro e he
    have he' : e ∈ exports' := by
      have : b.lower.exports = exports' := hEx
      rw [← this]; exact he
    obtain ⟨x, -, hxe⟩ := forall₂_mem hXs e he'
    cases hk : x.kind with
    | func =>
      simp only [hk] at hxe
      obtain ⟨k, hk', hxe⟩ := bind_ok hxe
      cases pure_ok hxe
      obtain ⟨d, hd⟩ := S.funcDts_length hw hc hk'
      exact ⟨.func d, .func (by rw [hCf]; exact hd)⟩
    | global =>
      simp only [hk] at hxe
      obtain ⟨k, hk', hxe⟩ := bind_ok hxe
      cases pure_ok hxe
      obtain ⟨p, hp, -⟩ := global_entry hk'
      exact ⟨.global ⟨p.2.type.mutability, liftVal p.2.type.value⟩,
        .global (by rw [hCg]; simp [gtsOf, hp])⟩
  obtain ⟨xtE, hxtE⟩ := hxt
  have hnames : exports'.map Export.name = m.exports.map NExport.name := by
    refine forall₂_map_eq NExport.name Export.name (forall₂_imp_mem ?_ hXs)
    intro x _ e hxe
    cases hk : x.kind with
    | func =>
      simp only [hk] at hxe
      obtain ⟨k, -, hxe⟩ := bind_ok hxe
      cases pure_ok hxe
      rfl
    | global =>
      simp only [hk] at hxe
      obtain ⟨k, -, hxe⟩ := bind_ok hxe
      cases pure_ok hxe
      rfl
  refine ⟨⟨xtI, xtE⟩, ModuleOk.mk (dts := S.dts) (xtI := xtI) (jts := []) (gts := gtsOf m)
    (tts := []) (fdts := fdts) (rts := []) (C' := C') (C := C) ?_ ?_ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ hxtE ?_⟩
  · -- types
    show TypesOk {} b.base.types S.dts
    rw [hT, hfts]
    exact V2.Validation.typesOk_map fts {}
  · -- imports
    show List.Forall₂ _ b.base.imports xtI
    rw [hI]
    refine forall₂_map_map _ _ ?_
    rintro ⟨n, i⟩ hp
    obtain ⟨hd, hty, hex⟩ := S.dAt_eq (hc.importTypes (n, i) hp)
    refine ⟨?_, .func (hty _) hex⟩
    show (Context.type? { types := S.dts } i.type).map CExternType.func = _
    simp only [Context.type?, hd, Option.map_some]
  · -- tags
    show List.Forall₂ _ b.base.tags []
    rw [htg]; exact .nil
  · -- globals
    show GlobalsOk C' b.base.globals (gtsOf m)
    rw [hGl]
    refine globalsOk_aux C' (forall₂_imp_mem ?_ hGs)
    rintro ⟨n, g⟩ hp g' hg'
    obtain ⟨hprof, c, hcst⟩ := hc.globals (n, g) hp
    obtain ⟨init', hinit, hg'⟩ := bind_ok hg'
    cases pure_ok hg'
    have hinit' : resolveE m.env [] (.const c) = .ok init' := by rw [← hcst]; exact hinit
    cases pure_ok hinit'
    have hty := hasType_const (hw.globalInits (n, g) hp) c hcst
    exact ⟨c, rfl, rfl, by injection hty, hprof⟩
  · -- memories
    intro mt hmt
    have : b.lower.memories = [] := hmem
    rw [this] at hmt
    simp at hmt
  · -- tables
    show List.Forall₂ _ b.base.tables []
    rw [htab]; exact .nil
  · -- functions
    show List.Forall₂ (FuncOk C) (b.funcs.map (Declaration.Func.mapBody BExpr.lowerList)) fdts
    rw [hFn]
    refine forall₂_map_of _ _ ?_ hFs
    rintro ⟨n, F⟩ hp f' hf'
    obtain ⟨body', hbody', hf'⟩ := bind_ok hf'
    cases pure_ok hf'
    obtain ⟨ft, hft, hps, hrs⟩ := hw.types (n, F) hp
    obtain ⟨hd, -, hex⟩ := S.dAt_eq hft
    rw [hps, hrs] at hex
    have hsig : (n, F.params, F.results) ∈ m.sigs := by
      simp only [NModule.sigs, List.mem_append, List.mem_map]
      exact Or.inr ⟨(n, F), hp, rfl⟩
    obtain ⟨hpr, hlen⟩ := hc.sigs _ hsig
    have hvars := hc.vars (n, F) hp
    have hall : (F.params ++ F.results ++ F.vars).all profileValType = true := by
      simp only [List.all_eq_true, List.mem_append]
      rintro t ((ht | ht) | ht)
      · exact hpr t (List.mem_append_left _ ht)
      · exact hpr t (List.mem_append_right _ ht)
      · exact hvars t ht
    refine FuncOk.mk (ps := Ty.ofList (F.params.map liftVal))
      (rs := Ty.ofList (F.results.map liftVal))
      (lts := F.vars.map fun t => ⟨.set, liftVal t⟩) hd hex ?_ ?_
    · refine forall₂_self_map _ ?_
      intro t ht
      have hpt := hvars t ht
      have h1 := LocalOk.set (C := C) (t := t)
        (by rw [closeVal_profile C hpt]; exact tyOk_lift _ hpt)
        (by rw [closeVal_profile C hpt]; obtain ⟨it, rfl⟩ := profile_num hpt; trivial)
      rw [closeVal_profile C hpt] at h1
      exact h1
    · show InstrsOk _ (BExpr.lowerList body') _
      simp only [Ty.toList_ofList]
      exact out_results (fun t ht => hpr t (List.mem_append_right _ ht)) hlen
        (body_E (hw.bodies (n, F) hp) [] _ body'
          (bodyInv_entry S hw hc F hall hlen C hCg hCf) (hc.code (n, F) hp) hbody')
  · -- data
    intro d hd
    have : b.lower.data = [] := hdat
    rw [this] at hd
    simp at hd
  · -- elems
    show List.Forall₂ _ b.base.elems []
    rw [hel]; exact .nil
  · -- start
    intro x hx
    have hx' : start' = some x := by rw [← hS]; exact hx
    obtain ⟨s, hs, hk⟩ := hst x hx'
    obtain ⟨ps, rs, hl, d, hd, hex⟩ := S.func_entry hw hc hk
    rw [hc.start s hs] at hl
    cases hl
    exact ⟨d, by rw [hCf]; exact hd, hex⟩
  · -- distinct export names
    show (b.base.exports.map Export.name).Nodup
    rw [hEx, hnames]
    exact hc.exportNames

end ResolveValid

/-- Well-typed named modules resolve to Core-valid modules (under the Core side
conditions `CoreReady`). -/
-- FLAG(statement-change): added the hypothesis `hc : m.CoreReady`. Without it the statement is
-- false (`resolve_valid_false`: duplicate export names); `WellTyped` also omits the type
-- section, import signatures, mutability of `global.set` targets, constant global
-- initialisers, the start signature, `extend` validity and the profile restrictions that
-- Core validation (`Module_ok`, untyped `select`) requires; `CoreReady` states exactly those.
theorem resolve_valid {m : NModule} {b : BModule} (h : m.WellTyped) (hc : m.CoreReady)
    (hr : m.resolve = .ok b) : b.Ok :=
  ResolveValid.valid h hc hr

end Silmaril.Wasm.Binaryen
