module

public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Defs

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Raw.Wasm.Component.Types.Subtype
public import Silmaril.Raw.Wasm.Component.ABI.Predicates

/-!
# Executable subtype checker (wasmparser `SubtypeCx`)

An executable transcription of wasmparser 0.259.0's `SubtypeCx`
(`src/validator/component_types.rs`, `impl SubtypeCx`, lines 3394-4249: `component_entity_type`,
`component_type`, `component_instance_type`, `component_func_type`, `module_type`,
`component_any_type_id`, `open_instance_type`, `component_val_type`, `component_defined_type`,
`primitive_val_type`; wasmparser 0.259.0 is the version pinned by wasmtime a7b4f29,
`Cargo.toml` line 372) on the index-free types of `Types/Basic.lean`, with soundness
`Entity.sub?_sound : Entity.sub? xsub? a b = .ok () → Entity.Sub XSub a b` against the relation
of `Types/Subtype.lean`, given a sound core extern checker `xsub?`. The error strings and the
order of the checks were transcribed from that source; contexts are prepended with a newline,
as by wasmparser's `with_context`/`add_context` (`src/error.rs`).

* `valSub?` / `funcSub?`: exact equality (decided with the structural `DecidableEq` of
  `ABI/Predicates.lean`); on failure the message is computed by `ValType.diff` /
  `FuncType.diff`, which walk the two types in wasmparser's order with its wording
  (`expected primitive `u32` found primitive `u8``, `expected N fields, found M`,
  `type mismatch in record field `x``, `expected fixed-length 4, found size 3`,
  `expected parameter named `y`, found `x``, `type mismatch in function parameter `x``,
  `resource types are not the same`, `expected record, found list`, ...). As upstream, list,
  option and fixed-length-list elements get no context line, `error-context` is a primitive,
  the async message names the *actual* side first (`expected {a} function, found {b}
  function`), and the result messages are the upstream ones (`expected a result, found none`
  when the actual type has a result and the expected one has none, and conversely).
* `moduleSub?` (`module_type`): per entry, `missing expected import `m::n`` or
  `type mismatch in import `m::n``; then `missing expected export `n`` or
  `type mismatch in export `n`` (lookup and check interleaved, as upstream).
* `instanceSub?` (`component_instance_type`): first every expected export is looked up
  (`missing expected export `n``), then the pairs are checked in order
  (`type mismatch in instance export `n``).
* `openInstanceType?` (`open_instance_type`): infers the `Remapping` of the binders of the
  expected side by matching `type (resource α)` entries (possibly nested in instance exports)
  by name against the actual side (`inferRemapping`, first match wins; a binder whose path
  cannot be followed stays unmapped, as upstream's `continue 'outer`), then looks up every
  expected entry (`missing import named `n`` / `missing export named `n``), then checks the
  pairs after substitution (`type mismatch for import `n`` / `type mismatch for export `n``).
* `componentSub?` (`component_type`): `openInstanceType?` of `B.imports` against `A`'s
  imports, then of `A`'s renamed exports against `B`'s exports; after each step the inferred
  renaming is checked against the range constraint of the relation (`checkTargets`).
* `typeDefSub?` (`component_any_type_id`), `Entity.sub?` (`component_entity_type`):
  `expected func, found instance`, `expected resource, found defined type`,
  `expected instance, found func type`, ... (the found side of `component_any_type_id` uses
  `defined type`/`func type`/`instance type`/`component type`/`resource`).

Deviations: wasmparser follows explicit resource *paths* recorded at validation time; the
index-free types carry no paths, so the checker infers them from the `type (resource _)`
entries by name. The type-level `resource types are not the same ({:?} vs. {:?})` message of
`component_any_type_id` is emitted without its debug suffix of internal resource ids (they have
no index-free counterpart); the value-level message has no suffix upstream either. The
`typeidx`-naming-a-primitive distinction of `component_val_type` does not exist in index-free
types (a primitive is always reported by name). The recursion is bounded by fuel
`a.depth + b.depth + 1` (the nesting depth, invariant under renaming); exhausting it yields the
error `type nesting exceeds the checker's fuel`, which is believed unreachable but not proved
(no completeness theorem is claimed). The messages are checked only by the kernel tests below;
there is no differential test against wasmparser. `checkTargets` is an addition:
an inferred target that is a binder nested in either type is rejected with
``resource remapped to a nested binder``, since `ComponentType.Sub` requires every target to be
a `ComponentType.RenameTarget`. This fires when binders are reused, and whenever an import- or
export-position instance type on the actual side is **not hoisted** (non-empty `defined`).
Such types are legitimate (wasmparser hoists them in `prepare_instance_import` /
`prepare_instance_export` and then accepts), so on them the checker, like the relation, is
incomplete w.r.t. wasmparser (`exNested_checker` in `Subtype/Trans.lean`); on hoisted
types (the form `WIT/Encode.lean` emits) the check is not known to reject anything wasmparser
accepts.

The tests also contain `componentTrans_unscoped_false`: without the freshness premise
`Entity.FreshTriple`, component-type subtyping is not transitive.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Types

universe u v

variable {R : Type u} {X : Type v}

/-! ## Generic helpers -/

theorem natStr_examples :
    natStr 0 = "0" ∧ natStr 7 = "7" ∧ natStr 10 = "10" ∧ natStr 4096 = "4096" := by
  decide +kernel

/-! ## Value and function types -/

section Diff

variable [DecidableEq R]

end Diff

/-! ## Core module types -/

/-! ## Instances, remappings and components -/

section Structural

variable [DecidableEq R]

/-! ## Soundness -/

variable {chk : Entity R X → Entity R X → Except String Unit} {XSub : X → X → Prop}

end Structural

/-! ## Tests

`R := Nat`, `X := Unit` with the trivial core extern checker. -/

/-- An instance type with an extra export is a subtype. -/
theorem instance_extra_export_sub :
    Entity.sub? unitSub?
      (.instance { defined := [], exports := [("f", .func exFuncX), ("g", .value (.prim .bool))] }
        : Entity Nat Unit)
      (.instance { defined := [], exports := [("f", .func exFuncX)] }) = .ok () := by
  decide +kernel

/-- ... and not conversely. -/
theorem instance_missing_export_not_sub :
    Entity.sub? unitSub?
      (.instance { defined := [], exports := [("f", .func exFuncX)] } : Entity Nat Unit)
      (.instance { defined := [], exports := [("f", .func exFuncX), ("g", .value (.prim .bool))] })
      = .error "missing expected export `g`" := by
  decide +kernel

/-- A function with a different parameter name is not a subtype. -/
theorem func_param_name_not_sub :
    Entity.sub? unitSub? (.func exFuncX : Entity Nat Unit) (.func exFuncY) =
      .error "expected parameter named `y`, found `x`" := by
  decide +kernel

theorem func_param_type_not_sub :
    Entity.sub? unitSub? (.func exFuncX : Entity Nat Unit)
      (.func { params := [("x", .prim .u8)], result := some (.prim .u32) }) =
      .error "type mismatch in function parameter `x`\n\
        expected primitive `u8` found primitive `u32`" := by
  decide +kernel

theorem sort_mismatch_not_sub :
    Entity.sub? unitSub? (.func exFuncX : Entity Nat Unit)
      (.instance { defined := [], exports := [] }) = .error "expected instance, found func" := by
  decide +kernel

theorem component_import_contravariant :
    Entity.sub? unitSub? (.component exCompA) (.component exCompB) = .ok () := by
  decide +kernel

theorem component_import_contravariant_converse :
    Entity.sub? unitSub? (.component exCompB) (.component exCompA) =
      .error "type mismatch for import `i`\nmissing expected export `g`" := by
  decide +kernel

theorem component_resource_remap :
    Entity.sub? unitSub? (.component exResA) (.component exResB) = .ok () := by
  decide +kernel

/-- Two distinct resources are not subtypes. -/
theorem resource_not_same :
    Entity.sub? unitSub? (.type (.resource 0) : Entity Nat Unit) (.type (.resource 1)) =
      .error "resource types are not the same" := by
  decide +kernel

/-- The relational statements follow from the checker. -/
theorem component_import_contravariant_rel :
    Entity.Sub (fun (_ _ : Unit) => True) (.component exCompA) (.component exCompB) :=
  Entity.sub?_sound (fun _ _ _ => trivial) component_import_contravariant

theorem component_resource_remap_rel :
    Entity.Sub (fun (_ _ : Unit) => True) (.component exResA) (.component exResB) :=
  Entity.sub?_sound (fun _ _ _ => trivial) component_resource_remap

/-- wasmparser looks up every expected export before checking any pair: with `f` mismatching
and `g` missing, the missing `g` is reported. -/
theorem instance_missing_before_mismatch :
    Entity.sub? unitSub?
      (.instance { defined := [], exports := [("f", .func exFuncY)] } : Entity Nat Unit)
      (.instance { defined := [], exports := [("f", .func exFuncX), ("g", .func exFuncX)] })
      = .error "missing expected export `g`" := by
  decide +kernel

/-- The same two-pass order in `open_instance_type`, for component imports. -/
theorem component_missing_before_mismatch :
    Entity.sub? unitSub? (.component exCompFuncImport) (.component exCompA) =
      .error "missing import named `j`" := by
  decide +kernel

theorem component_import_mismatch :
    Entity.sub? unitSub? (.component { exCompFuncImport with imports := [("i", .func exFuncX)] })
      (.component exCompA) = .error "type mismatch for import `i`\nexpected func, found instance"
      := by
  decide +kernel

theorem instance_export_mismatch :
    Entity.sub? unitSub?
      (.instance { defined := [], exports := [("f", .func exFuncY)] } : Entity Nat Unit)
      (.instance { defined := [], exports := [("f", .func exFuncX)] })
      = .error "type mismatch in instance export `f`\n\
        expected parameter named `x`, found `y`" := by
  decide +kernel

/-- Upstream names the actual side's flag first. -/
theorem func_async_not_sub :
    Entity.sub? unitSub? (.func { exFuncX with async_ := true } : Entity Nat Unit)
      (.func exFuncX) = .error "expected async function, found sync function" := by
  decide +kernel

theorem func_result_not_sub :
    Entity.sub? unitSub? (.func exFuncX : Entity Nat Unit) (.func { exFuncX with result := none })
      = .error "expected a result, found none" ∧
    Entity.sub? unitSub? (.func { exFuncX with result := none } : Entity Nat Unit) (.func exFuncX)
      = .error "expected no result, found one" := by
  decide +kernel

theorem val_messages :
    Entity.sub? unitSub? (.value (.list (.prim .u8)) : Entity Nat Unit)
        (.value (.list (.prim .u32))) = .error "expected primitive `u32` found primitive `u8`" ∧
    Entity.sub? unitSub? (.value (.fixedList (.prim .u8) 3) : Entity Nat Unit)
        (.value (.fixedList (.prim .u8) 4)) = .error "expected fixed-length 4, found size 3" ∧
    Entity.sub? unitSub? (.value (.fixedList (.prim .u8) 3) : Entity Nat Unit)
        (.value (.list (.prim .u8))) = .error "expected list, found list" ∧
    Entity.sub? unitSub? (.value (.list (.prim .u8)) : Entity Nat Unit)
        (.value (.fixedList (.prim .u8) 3)) = .error "expected fixed-length list, found list" ∧
    Entity.sub? unitSub? (.value .errorContext : Entity Nat Unit) (.value (.prim .u32))
        = .error "expected primitive `u32` found primitive `error-context`" := by
  decide +kernel

theorem typeDef_found_desc :
    Entity.sub? unitSub? (.type (.func exFuncX) : Entity Nat Unit)
      (.type (.instance { defined := [], exports := [] }))
      = .error "expected instance, found func type" ∧
    Entity.sub? unitSub? (.type (.val (.prim .u8)) : Entity Nat Unit) (.type (.resource 0))
      = .error "expected resource, found defined type" := by
  decide +kernel

/-! ### Transitivity needs freshness

`A` mentions `own 1` free, `B` ∀-binds `1` (and re-exposes it as import `r`), and `C` supplies
resource `2` for it. Both `A <: B` and `B <: C` hold (by the checker), but `A <: C` does not:
`A`'s renaming must fix `1` (it has no binders), so `C`'s import `f : func() -> own 2` cannot
match `A`'s `func() -> own 1`. The triple violates `Entity.FreshTriple` for every context (`1`
is free in `A`, hence in `Γ`, and bound in `B`, hence not in `Γ`). -/

theorem exTrans_ab :
    ComponentType.Sub (fun (_ _ : Unit) => True) exTransA exTransB := by
  have h : Entity.Sub (fun (_ _ : Unit) => True) (.component exTransA) (.component exTransB) :=
    Entity.sub?_sound (xsub? := unitSub?) (fun _ _ _ => trivial) (by decide +kernel)
  cases h with | component h => exact h

theorem exTrans_bc :
    ComponentType.Sub (fun (_ _ : Unit) => True) exTransB exTransC := by
  have h : Entity.Sub (fun (_ _ : Unit) => True) (.component exTransB) (.component exTransC) :=
    Entity.sub?_sound (xsub? := unitSub?) (fun _ _ _ => trivial) (by decide +kernel)
  cases h with | component h => exact h

theorem exTrans_not_ac :
    ¬ ComponentType.Sub (fun (_ _ : Unit) => True) exTransA exTransC := by
  rintro ⟨f, g, hf, _, hi, hg, _, he⟩
  have hf1 : f 1 = 1 := hf 1 (by decide)
  have e : Entity.map f (.func (exFuncOwn 1) : Entity Nat Unit) = .func (exFuncOwn 1) := by
    simp only [Entity.map, exFuncOwn, WIT.FuncType.mapResource, WIT.ValType.mapResourceOption,
      WIT.ValType.mapResourceFields, WIT.ValType.mapResource, hf1]
  have hm : ("f", Entity.map f (.func (exFuncOwn 1))) ∈ Entity.mapList f exTransA.imports :=
    Entity.mem_mapList f (by simp only [exTransA, List.mem_cons, List.not_mem_nil, or_false])
  rw [e] at hm
  obtain ⟨a, ha, hs⟩ := hi.get hm
  simp only [exTransC, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨h, _⟩ | ⟨_, rfl⟩
  · exact absurd h (by decide)
  · cases hs

/-- Without the freshness premise of `ComponentTrans`, component-type subtyping is not
transitive. -/
theorem componentTrans_unscoped_false :
    ¬ ∀ a b c : ComponentType Nat Unit, ComponentType.Sub (fun _ _ => True) a b →
      ComponentType.Sub (fun _ _ => True) b c → ComponentType.Sub (fun _ _ => True) a c :=
  fun h => exTrans_not_ac (h _ _ _ exTrans_ab exTrans_bc)

/-- ... and the counterexample is excluded by `Entity.FreshTriple` in every context. -/
theorem exTrans_not_freshTriple (Γ : List Nat) :
    ¬ Entity.FreshTriple Γ (.component exTransA : Entity Nat Unit) (.component exTransB)
      (.component exTransC) := by
  rintro ⟨sa, _, _, _, hΓ⟩
  exact hΓ 1 (by decide +kernel) (sa 1 (by decide +kernel))

end Silmaril.Wasm.Component.Types
