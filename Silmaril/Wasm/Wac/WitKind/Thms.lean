module

public import Silmaril.Wasm.Wac.WitKind.Defs
public import Silmaril.Wasm.Wac.ElabTyped.Thms

/-!
# WAC: WIT packages give WIT-shaped kinds

* `ofInterface_wit`, `ofWorldItem_wit`: interfaces and world items of resolved WIT
  packages are WIT-shaped;
* `envWit_of_worlds`: a registry whose packages are components targeting WIT worlds
  satisfies `EnvWit`, so `elabDoc_typed` applies to it unconditionally:
  `elabDoc_typed_wit`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

namespace WitKind

theorem wit_of_flat {k : Kind} (h : k.flat = true) : k.wit = true := by
  cases k with
  | inst _ _ => simp [Kind.flat] at h
  | _ => exact h

theorem ofTypeDef_flat (d : Wit.Binary.TypeDef) : (ofTypeDef d).flat = true := by
  unfold ofTypeDef; split <;> rfl

theorem ofBody_flat (i : Wit.Binary.Interface) : ∀ p ∈ ofBody i, p.2.flat = true := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · obtain ⟨d, _, rfl⟩ := List.mem_map.1 h
    exact ofTypeDef_flat d
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 h
    rfl

theorem ofInterface_wit (id : Option String) (i : Wit.Binary.Interface) : (ofInterface id i).wit = true :=
  List.all_eq_true.2 (ofBody_flat i)

theorem ofWorldItem_wit (env : Wit.Binary.Env) (it : Wit.Binary.WorldItem) : (ofWorldItem env it).2.wit = true := by
  cases it with
  | ifaceRef i _ _ => exact ofInterface_wit _ _
  | ifaceInline n body => exact ofInterface_wit _ _
  | func f => rfl
  | type d => exact wit_of_flat (ofTypeDef_flat d)

/-- The imports of a component targeting a WIT world are WIT-shaped. -/
theorem worldPackage_wit (env : Wit.Binary.Env) (w : Wit.Binary.World) :
    Implicit.WitEx (worldPackage env w).imports := fun p hp => by
  obtain ⟨it, _, rfl⟩ := List.mem_map.1 hp
  exact ofWorldItem_wit env it

/-- A registry of components targeting WIT worlds. -/
def worldEnv (env : Wit.Binary.Env) (ws : List (String × Wit.Binary.World)) : PkgEnv :=
  ws.map fun (k, w) => (k, worldPackage env w)

theorem mem_of_lookup_pkg {l : PkgEnv} {x : String} {pk : PkgType} (h : l.lookup x = some pk) :
    (x, pk) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨y, v⟩ := p
    by_cases hx : x = y
    · subst hx
      have e : v = pk := by simpa [List.lookup] using h
      simp [e]
    · have h' : l.lookup x = some pk := by simpa [List.lookup, beq_false_of_ne hx] using h
      exact List.mem_cons_of_mem _ (ih h')

theorem envWit_of_worlds (env : Wit.Binary.Env) (ws : List (String × Wit.Binary.World)) :
    EnvWit (worldEnv env ws) := by
  intro key pk h
  obtain ⟨⟨k, w⟩, _, e⟩ := List.mem_map.1 (mem_of_lookup_pkg h)
  simp only [Prod.mk.injEq] at e
  rw [← e.2]
  exact worldPackage_wit env w

end WitKind

/-- **Compositions of components targeting WIT worlds elaborate to fully explicit,
well-typed graphs.** -/
theorem elabDoc_typed_wit {env : Wit.Binary.Env} {ws : List (String × Wit.Binary.World)}
    {d : Syntax.Document} {g : CGraph} (h : elabDoc (WitKind.worldEnv env ws) d = .ok g) :
    g.Complete ∧ g.Typed :=
  elabDoc_typed (WitKind.envWit_of_worlds env ws) h

end Silmaril.Wasm.Wac
