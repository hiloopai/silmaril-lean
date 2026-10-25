module

public import Silmaril.Data.ByteArray
public import Silmaril.Wasm.Types

/-! # Shared source declarations

These records contain source syntax, not runtime closures or allocated instances.
The expression parameter lets profiles share declarations while retaining their
own instruction languages and validation judgments.
-/

@[expose] public section

namespace Silmaril.Wasm.Declaration

/-- A defined function refers to a module type; parameters belong to that type,
whereas `locals` contains only the additional local declarations. -/
structure Func (ValueType Expr : Type) where
  type : TypeIdx
  locals : List ValueType
  body : Expr
  deriving Repr

/-- A global's initializer is source code, not an already evaluated value. -/
structure Global (GlobalType Expr : Type) where
  type : GlobalType
  init : Expr
  deriving Repr

/-- An active element segment in the scalar profiles. -/
structure ActiveElem (Expr : Type) where
  table : TableIdx
  offset : Expr
  init : List FuncIdx
  deriving Repr

/-- An active data segment. The bytes use Lean's standard byte array. -/
structure ActiveData (Expr : Type) where
  memory : MemIdx
  offset : Expr
  bytes : ByteArray
  deriving Repr

namespace Func

variable {V E F G : Type}

def mapBody (f : E → F) (d : Func V E) : Func V F :=
  ⟨d.type, d.locals, f d.body⟩

@[simp] theorem mapBody_id (d : Func V E) : d.mapBody id = d := rfl
@[simp] theorem mapBody_comp (f : E → F) (g : F → G) (d : Func V E) :
    (d.mapBody f).mapBody g = d.mapBody (g ∘ f) := rfl

theorem mapBody_injective {f : E → F} (hf : Function.Injective f) :
    Function.Injective (mapBody (V := V) f) := by
  rintro ⟨t, ls, e⟩ ⟨t', ls', e'⟩ h
  simp only [mapBody, mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  exact congrArg (mk t ls) (hf h)

end Func

namespace Global

variable {T E F G : Type}

def mapInit (f : E → F) (d : Global T E) : Global T F := ⟨d.type, f d.init⟩

@[simp] theorem mapInit_id (d : Global T E) : d.mapInit id = d := rfl
@[simp] theorem mapInit_comp (f : E → F) (g : F → G) (d : Global T E) :
    (d.mapInit f).mapInit g = d.mapInit (g ∘ f) := rfl

theorem mapInit_injective {f : E → F} (hf : Function.Injective f) :
    Function.Injective (mapInit (T := T) f) := by
  rintro ⟨t, e⟩ ⟨t', e'⟩ h
  simp only [mapInit, mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact congrArg (mk t) (hf h)

end Global
end Silmaril.Wasm.Declaration
