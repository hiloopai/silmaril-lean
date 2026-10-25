module

public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Computable checker for function definitions (`Local_ok`, `Func_ok`)

Parametrised over a type-validity oracle `tyOk` and an expression checker `exprOk`.
-/

namespace Silmaril.Wasm.Validation

section
variable (tyOk : TypeCtx → {k : TKind} → Ty k → Bool)

/-- Checker for `Local_ok`. -/
def localCheck? (C : Context) (t : ValType) : Option LocalType :=
  if tyOk C.toTypeCtx (C.closeVal t) then
    if Defaultable (C.closeVal t) then some ⟨.set, C.closeVal t⟩
    else some ⟨.unset, C.closeVal t⟩
  else none

/-- Checker for a list of locals. -/
def localsCheck? (C : Context) : List ValType → Option (List LocalType)
  | [] => some []
  | t :: ts => do
      let lt ← localCheck? tyOk C t
      let lts ← localsCheck? C ts
      pure (lt :: lts)

variable {tyOk}

theorem localCheck?_sound (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
    {C : Context} {t : ValType} {lt : LocalType} (h : localCheck? tyOk C t = some lt) :
    LocalOk C t lt := by
  unfold localCheck? at h
  split at h
  · rename_i hty
    split at h
    · cases h; exact .set (htyOk _ _ hty) ‹_›
    · cases h; exact .unset (htyOk _ _ hty) ‹_›
  · cases h

theorem localCheck?_complete (htyOk' : ∀ Δ {k} (t : Ty k), TyOk Δ t → tyOk Δ t = true)
    {C : Context} {t : ValType} {lt : LocalType} (h : LocalOk C t lt) :
    localCheck? tyOk C t = some lt := by
  cases h with
  | set h hd => simp [localCheck?, htyOk' _ _ h, hd]
  | unset h hd => simp [localCheck?, htyOk' _ _ h, hd]

theorem localsCheck?_sound (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
    {C : Context} : ∀ {ts : List ValType} {lts : List LocalType},
    localsCheck? tyOk C ts = some lts → List.Forall₂ (LocalOk C) ts lts
  | [], lts, h => by cases h; exact .nil
  | t :: ts, lts, h => by
      simp only [localsCheck?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨lt, h1, lts', h2, rfl⟩ := h
      exact .cons (localCheck?_sound htyOk h1) (localsCheck?_sound htyOk h2)

theorem localsCheck?_complete (htyOk' : ∀ Δ {k} (t : Ty k), TyOk Δ t → tyOk Δ t = true)
    {C : Context} {ts : List ValType} {lts : List LocalType}
    (h : List.Forall₂ (LocalOk C) ts lts) : localsCheck? tyOk C ts = some lts := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [localsCheck?, localCheck?_complete htyOk' h, ih]

end

section
variable (tyOk : TypeCtx → {k : TKind} → Ty k → Bool)
  (exprOk : Context → Expr → List CValType → Bool)

/-- Checker for `Func_ok` against a given defined type. -/
def funcCheck (C : Context) (f : Func) (d : DefType) : Bool :=
  if C.type? f.type = some d then
    match d.expand? with
    | some (.func ps rs) =>
      match localsCheck? tyOk C f.locals with
      | some lts => exprOk (C.funcBody ps.toList rs.toList lts) f.body rs.toList
      | none => false
    | _ => false
  else false

/-- Option form: the defined type is looked up from `C.type? f.type`. -/
def funcCheck? (C : Context) (f : Func) : Option DefType :=
  match C.type? f.type with
  | some d => if funcCheck tyOk exprOk C f d then some d else none
  | none => none

variable {tyOk exprOk}

theorem funcCheck_sound (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
    (hexpr : ∀ C e ts, exprOk C e ts = true → ExprOk C e ts)
    {C : Context} {f : Func} {d : DefType} (h : funcCheck tyOk exprOk C f d = true) :
    FuncOk C f d := by
  unfold funcCheck at h
  split at h
  · rename_i hd
    split at h
    · rename_i ps rs hx
      split at h
      · rename_i lts hl
        exact .mk hd (Expand.iff.mpr hx) (localsCheck?_sound htyOk hl) (hexpr _ _ _ h)
      · cases h
    · cases h
  · cases h

theorem funcCheck?_sound (htyOk : ∀ Δ {k} (t : Ty k), tyOk Δ t = true → TyOk Δ t)
    (hexpr : ∀ C e ts, exprOk C e ts = true → ExprOk C e ts)
    {C : Context} {f : Func} {d : DefType} (h : funcCheck? tyOk exprOk C f = some d) :
    FuncOk C f d := by
  unfold funcCheck? at h
  split at h
  · split at h
    · cases h; exact funcCheck_sound htyOk hexpr ‹_›
    · cases h
  · cases h

end

end Silmaril.Wasm.Validation
