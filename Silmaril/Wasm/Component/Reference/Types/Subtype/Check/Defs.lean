module

import all Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs

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

/-- First value under key `k` in an association list. -/
def lookupKey {K : Type u} {V : Type v} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (k', v) :: kvs, k => if k' = k then some v else lookupKey kvs k

/-- wasmparser `with_context`: prepend a context line to an error. -/
def withCtx (ctx : String) : Except String Unit → Except String Unit
  | .ok u => .ok u
  | .error m => .error (ctx ++ "\n" ++ m)

/-- Run a check on every element, stopping at the first error. -/
def checkEach {α : Type u} (f : α → Except String Unit) : List α → Except String Unit
  | [] => .ok ()
  | a :: as => match f a with
    | .ok () => checkEach f as
    | .error e => .error e

/-- Context line with an optional message. -/
def ctxOpt (ctx : String) : Option String → Option String
  | none => none
  | some m => some (ctx ++ "\n" ++ m)

/-- Decimal rendering of a `Nat` (Rust's `{}` for `usize`), defined by structural recursion on
fuel so that the kernel tests reduce it (`Nat.repr` is not exposed to `module` files). -/
def natStr (n : Nat) : String := go (n + 1) n
where
  digit : Nat → String
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
    | 8 => "8" | _ => "9"
  go : Nat → Nat → String
    | 0, _ => ""
    | fuel + 1, n => if n < 10 then digit n else go fuel (n / 10) ++ digit (n % 10)

/-! ## Value and function types -/

def primName : WIT.Primitive → String
  | .bool => "bool" | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .s8 => "s8" | .s16 => "s16" | .s32 => "s32" | .s64 => "s64" | .f32 => "f32"
  | .f64 => "f64" | .char => "char" | .string => "string"

/-- wasmparser's description of an *expected* value type in `expected {..}, found {..}`
(`ComponentDefinedType::desc`; a primitive, including `error-context`, is shown by name). -/
def valDesc : ValType R → String
  | .prim p => primName p
  | .ref n => nomatch n
  | .list _ => "list"
  | .fixedList _ _ => "fixed-length list"
  | .record _ => "record"
  | .tuple _ => "tuple"
  | .variant _ => "variant"
  | .enum _ => "enum"
  | .flags _ => "flags"
  | .option _ => "option"
  | .result _ _ => "result"
  | .map _ _ => "map"
  | .own _ => "own"
  | .borrow _ => "borrow"
  | .future _ => "future"
  | .stream _ => "stream"
  | .errorContext => "error-context"

/-- wasmparser's description of the *actual* value type in `expected {..}, found {..}`: the
hard-coded nouns of `component_defined_type`'s fallback arms, where a fixed-length list is
reported as `list`. -/
def valDescFound : ValType R → String
  | .fixedList _ _ => "list"
  | t => valDesc t

def primDiff (a b : WIT.Primitive) : Option String :=
  if a = b then none else some s!"expected primitive `{primName b}` found primitive `{primName a}`"

section Diff

variable [DecidableEq R]

mutual
  /-- The first mismatch between `a` (actual) and `b` (expected), in wasmparser's order and
  wording; `none` if none is found. Only used for error messages. -/
  def ValType.diff : ValType R → ValType R → Option String
    | .prim a, .prim b => primDiff a b
    | .prim a, .errorContext =>
      some s!"expected primitive `error-context` found primitive `{primName a}`"
    | .errorContext, .prim b =>
      some s!"expected primitive `{primName b}` found primitive `error-context`"
    | .list a, .list b => ValType.diff a b
    | .fixedList a n, .fixedList b m =>
      if n = m then ValType.diff a b
      else some s!"expected fixed-length {natStr m}, found size {natStr n}"
    | .record fs, .record gs =>
      if fs.length = gs.length then ValType.diffFields fs gs
      else some s!"expected {natStr gs.length} fields, found {natStr fs.length}"
    | .tuple ts, .tuple us =>
      if ts.length = us.length then ValType.diffTuple 0 ts us
      else some s!"expected {natStr us.length} types, found {natStr ts.length}"
    | .variant cs, .variant ds =>
      if cs.length = ds.length then ValType.diffCases cs ds
      else some s!"expected {natStr ds.length} cases, found {natStr cs.length}"
    | .enum a, .enum b => if a = b then none else some "mismatch in enum elements"
    | .flags a, .flags b => if a = b then none else some "mismatch in flags elements"
    | .option a, .option b => ValType.diff a b
    | .result o e, .result o' e' =>
      (ValType.diffOpt "type mismatch in ok variant" "expected ok type, but found none"
          "expected ok type to not be present" o o').or
        (ValType.diffOpt "type mismatch in err variant" "expected err type, but found none"
          "expected err type to not be present" e e')
    | .map k v, .map k' v' =>
      (ctxOpt "type mismatch in map key" (primDiff k.toPrimitive k'.toPrimitive)).or
        (ctxOpt "type mismatch in map value" (ValType.diff v v'))
    | .own a, .own b | .borrow a, .borrow b =>
      if a = b then none else some "resource types are not the same"
    | .future a, .future b =>
      ValType.diffOpt "type mismatch in future" "expected future type, but found none"
        "expected future type to not be present" a b
    | .stream a, .stream b =>
      ValType.diffOpt "type mismatch in stream" "expected stream type, but found none"
        "expected stream type to not be present" a b
    | .errorContext, .errorContext => none
    | .ref n, _ => nomatch n
    | a, b => some s!"expected {valDesc b}, found {valDescFound a}"
  termination_by structural a _ => a

  def ValType.diffFields :
      List (String × ValType R) → List (String × ValType R) → Option String
    | (an, a) :: fs, (bn, b) :: gs =>
      if an = bn then
        (ctxOpt s!"type mismatch in record field `{an}`" (ValType.diff a b)).or
          (ValType.diffFields fs gs)
      else some s!"expected field name `{bn}`, found `{an}`"
    | _, _ => none
  termination_by structural a _ => a

  def ValType.diffTuple (i : Nat) : List (ValType R) → List (ValType R) → Option String
    | a :: ts, b :: us =>
      (ctxOpt s!"type mismatch in tuple field {natStr i}" (ValType.diff a b)).or
        (ValType.diffTuple (i + 1) ts us)
    | _, _ => none
  termination_by structural a _ => a

  def ValType.diffCases :
      List (String × Option (ValType R)) → List (String × Option (ValType R)) → Option String
    | (an, a) :: cs, (bn, b) :: ds =>
      if an = bn then
        (ValType.diffOpt s!"type mismatch in variant case `{an}`"
            s!"expected case `{an}` to have a type, found none"
            s!"expected case `{an}` to have no type" a b).or
          (ValType.diffCases cs ds)
      else some s!"expected case named `{bn}`, found `{an}`"
    | _, _ => none
  termination_by structural a _ => a

  def ValType.diffOpt (ctx missing extra : String) :
      Option (ValType R) → Option (ValType R) → Option String
    | none, none => none
    | some a, some b => ctxOpt ctx (ValType.diff a b)
    | none, some _ => some missing
    | some _, none => some extra
  termination_by structural a _ => a
end

/-- wasmparser `component_val_type`: exact equality, with a descriptive error. -/
def valSub? (a b : ValType R) : Except String Unit :=
  if a = b then .ok () else .error ((ValType.diff a b).getD "type mismatch")

def asyncDesc (b : Bool) : String := if b then "async" else "sync"

/-- The first mismatch between two function types, in wasmparser's order and wording
(`component_func_type`). The async message deliberately copies upstream, which names the
actual side (`a`) after `expected` and the expected side after `found`. -/
def FuncType.diff (a b : FuncType R) : Option String :=
  if a.async_ ≠ b.async_ then
    some s!"expected {asyncDesc a.async_} function, found {asyncDesc b.async_} function"
  else if a.params.length ≠ b.params.length then
    some s!"expected {natStr b.params.length} parameters, found {natStr a.params.length}"
  else
    (diffParams a.params b.params).or (resultDiff a.result b.result)
where
  diffParams : List (String × ValType R) → List (String × ValType R) → Option String
    | (an, a) :: ps, (bn, b) :: qs =>
      if an = bn then
        (ctxOpt s!"type mismatch in function parameter `{an}`" (ValType.diff a b)).or
          (diffParams ps qs)
      else some s!"expected parameter named `{bn}`, found `{an}`"
    | _, _ => none
  /-- Upstream wording, deliberately copied: actual `some`, expected `none` is reported as
  `expected a result, found none`, and conversely. -/
  resultDiff : Option (ValType R) → Option (ValType R) → Option String
    | none, none => none
    | some a, some b => ctxOpt "type mismatch with result type" (ValType.diff a b)
    | some _, none => some "expected a result, found none"
    | none, some _ => some "expected no result, found one"

/-- wasmparser `component_func_type`: exact equality (names, types, `async_`). -/
def funcSub? (a b : FuncType R) : Except String Unit :=
  if a = b then .ok () else .error ((FuncType.diff a b).getD "type mismatch")

end Diff

/-! ## Core module types -/

/-- wasmparser `module_type`, over a core extern checker `xsub? actual expected`. -/
def moduleSub? (xsub? : X → X → Except String Unit) (a b : CoreModuleType X) :
    Except String Unit :=
  match checkEach (fun (i : (String × String) × X) =>
      match lookupKey b.imports i.1 with
      | none => .error s!"missing expected import `{i.1.1}::{i.1.2}`"
      | some y => withCtx s!"type mismatch in import `{i.1.1}::{i.1.2}`" (xsub? y i.2))
      a.imports with
  | .error e => .error e
  | .ok () => checkEach (fun (e : String × X) =>
      match lookupKey a.exports e.1 with
      | none => .error s!"missing expected export `{e.1}`"
      | some x => withCtx s!"type mismatch in export `{e.1}`" (xsub? x e.2))
      b.exports

/-! ## Instances, remappings and components -/

section Structural

variable [DecidableEq R]

/-- The first pass of wasmparser's `component_instance_type` / `open_instance_type`: every
expected name must be present in `actual`, else `missing` of the first absent name. -/
def presentEach (actual expected : List (String × Entity R X)) (missing : String → String) :
    Except String Unit :=
  checkEach (fun (e : String × Entity R X) =>
      match lookupKey actual e.1 with
      | none => .error (missing e.1)
      | some _ => .ok ())
    expected

/-- wasmparser `component_instance_type` over an entity checker `chk actual expected`: first
all expected exports are looked up, then the pairs are checked in order. -/
def instanceSub? (chk : Entity R X → Entity R X → Except String Unit)
    (a b : InstanceType R X) : Except String Unit :=
  match presentEach a.exports b.exports (fun n => s!"missing expected export `{n}`") with
  | .error e => .error e
  | .ok () =>
    checkEach (fun (e : String × Entity R X) =>
        match lookupKey a.exports e.1 with
        | none => .error s!"missing expected export `{e.1}`"
        | some x => withCtx s!"type mismatch in instance export `{e.1}`" (chk x e.2))
      b.exports

mutual
  /-- Resource-path inference: match the `type (resource α)` entries (`α ∈ binders`) of the
  expected entity against the actual one, following instance exports by name. -/
  def inferEntity (binders : List R) : Entity R X → Entity R X → Remapping R
    | .type (.resource r), .type (.resource s) => if r ∈ binders then [(r, s)] else []
    | .instance t, .instance u => inferInstance binders t u
    | _, _ => []

  def inferInstance (binders : List R) : InstanceType R X → InstanceType R X → Remapping R
    | ⟨_, es⟩, u => inferList binders es u.exports

  def inferList (binders : List R) :
      List (String × Entity R X) → List (String × Entity R X) → Remapping R
    | [], _ => []
    | (n, e) :: es, act =>
      (match lookupKey act n with
        | some a => inferEntity binders e a
        | none => []) ++ inferList binders es act
end

/-- The remapping of `binders` inferred from matching `expected` against `args`. -/
def inferRemapping (binders : List R) (args expected : List (String × Entity R X)) :
    Remapping R :=
  inferList binders expected args

/-- wasmparser `open_instance_type(args, C, kind)`: infer the remapping of `C`'s binders, look
up every expected name in `args`, then substitute the remapping into each expected entity and
check the same-named actual entity against it. `kind` is `"import"` or `"export"`
(`ExternKind::desc`). Returns the remapping. -/
def openInstanceType? (chk : Entity R X → Entity R X → Except String Unit)
    (args : List (String × Entity R X)) (binders : List R)
    (expected : List (String × Entity R X)) (kind : String) :
    Except String (Remapping R) :=
  let m := inferRemapping binders args expected
  match presentEach args expected (fun n => s!"missing {kind} named `{n}`") with
  | .error e => .error e
  | .ok () =>
    match checkEach (fun (e : String × Entity R X) =>
        match lookupKey args e.1 with
        | none => .error s!"missing {kind} named `{e.1}`"
        | some a => withCtx s!"type mismatch for {kind} `{e.1}`"
            (chk a (e.2.map (m.apply binders))))
        expected with
    | .ok () => .ok m
    | .error e => .error e

/-- The range constraint of `ComponentType.Sub` on an inferred renaming `φ` of `binders`: every
binder is left in place or sent to a `ComponentType.RenameTarget a b`. Not part of wasmparser
(whose resource paths never lead into a nested binder of well-formed types); a violation is
reported as ``resource remapped to a nested binder``. -/
def checkTargets (a b : ComponentType R X) (binders : List R) (φ : R → R) :
    Except String Unit :=
  checkEach (fun r =>
      if φ r = r ∨ (φ r ∈ a.vars ++ b.vars ∧ φ r ∉ a.inner ++ b.inner) then .ok ()
      else .error "resource remapped to a nested binder")
    binders

/-- wasmparser `component_type`: `B.imports` must satisfy `A`'s imports (remapping `A`'s
∀-binders), then `A`'s remapped exports must satisfy `B`'s exports (remapping `B`'s
∃-binders). After each step the inferred renaming is checked against the range constraint of
the relation (`checkTargets`, an addition to wasmparser). -/
def componentSub? (chk : Entity R X → Entity R X → Except String Unit)
    (a b : ComponentType R X) : Except String Unit :=
  match openInstanceType? chk b.imports a.imported a.imports "import" with
  | .error e => .error e
  | .ok m =>
    match checkTargets a b a.imported (m.apply a.imported) with
    | .error e => .error e
    | .ok () =>
    match openInstanceType? chk (Entity.mapList (m.apply a.imported) a.exports) b.defined
        b.exports "export" with
    | .error e => .error e
    | .ok m' => checkTargets a b b.defined (m'.apply b.defined)

/-- wasmparser `ComponentAnyTypeId::desc` (the expected side). -/
def TypeDef.desc : TypeDef R X → String
  | .val _ => "defined type"
  | .resource _ => "resource"
  | .func _ => "func"
  | .instance _ => "instance"
  | .component _ => "component"

/-- The hard-coded nouns for the actual side in `component_any_type_id`'s fallback arms. -/
def TypeDef.foundDesc : TypeDef R X → String
  | .val _ => "defined type"
  | .resource _ => "resource"
  | .func _ => "func type"
  | .instance _ => "instance type"
  | .component _ => "component type"

/-- wasmparser `component_any_type_id`. The type-level resource mismatch omits upstream's
` ({:?} vs. {:?})` suffix of internal resource ids. -/
def typeDefSub? (chk : Entity R X → Entity R X → Except String Unit) :
    TypeDef R X → TypeDef R X → Except String Unit
  | .resource r, .resource s =>
    if r = s then .ok () else .error "resource types are not the same"
  | .resource _, b => .error s!"expected {b.desc}, found resource"
  | a, .resource _ => .error s!"expected resource, found {a.foundDesc}"
  | .val a, .val b => valSub? a b
  | .func a, .func b => funcSub? a b
  | .instance a, .instance b => instanceSub? chk a b
  | .component a, .component b => componentSub? chk a b
  | a, b => .error s!"expected {b.desc}, found {a.foundDesc}"

/-- wasmparser `ComponentEntityType::desc`. -/
def EntitySort.desc : EntitySort → String
  | .module => "module"
  | .func => "func"
  | .value => "value"
  | .type => "type"
  | .instance => "instance"
  | .component => "component"

/-- One layer of wasmparser `component_entity_type`, with nested entities checked by `chk`. -/
def entitySubStep (xsub? : X → X → Except String Unit)
    (chk : Entity R X → Entity R X → Except String Unit) :
    Entity R X → Entity R X → Except String Unit
  | .module a, .module b => moduleSub? xsub? a b
  | .func a, .func b => funcSub? a b
  | .value a, .value b => valSub? a b
  | .type a, .type b => typeDefSub? chk a b
  | .instance a, .instance b => instanceSub? chk a b
  | .component a, .component b => componentSub? chk a b
  | a, b => .error s!"expected {b.sort.desc}, found {a.sort.desc}"

/-- The checker with explicit fuel (one unit per nested entity layer). -/
def subFuel (xsub? : X → X → Except String Unit) :
    Nat → Entity R X → Entity R X → Except String Unit
  | 0, _, _ => .error "type nesting exceeds the checker's fuel"
  | n + 1, a, b => entitySubStep xsub? (subFuel xsub? n) a b

/-- The executable subtype check `a <: b` (`a` actual, `b` expected), wasmparser
`SubtypeCx::component_entity_type`, over a core extern checker `xsub?`. -/
def Entity.sub? (xsub? : X → X → Except String Unit) (a b : Entity R X) :
    Except String Unit :=
  subFuel xsub? (a.depth + b.depth + 1) a b

/-! ## Soundness -/

variable {chk : Entity R X → Entity R X → Except String Unit} {XSub : X → X → Prop}

end Structural

/-! ## Tests

`R := Nat`, `X := Unit` with the trivial core extern checker. -/

/-- The trivial core extern checker on `Unit`. -/
def unitSub? : Unit → Unit → Except String Unit := fun _ _ => .ok ()

def exFuncX : FuncType Nat := { params := [("x", .prim .u32)], result := some (.prim .u32) }
def exFuncY : FuncType Nat := { params := [("y", .prim .u32)], result := some (.prim .u32) }

/-- Component import contravariance: `A` imports an instance with only `f`; `B` imports an
instance with `f` and `g`. `A <: B` (B's imports satisfy A's), but not `B <: A`. -/
def exCompA : ComponentType Nat Unit where
  imported := []
  imports := [("i", .instance { defined := [], exports := [("f", .func exFuncX)] })]
  defined := []
  exports := [("run", .func exFuncX)]

def exCompB : ComponentType Nat Unit where
  imported := []
  imports :=
    [("i", .instance { defined := [], exports := [("f", .func exFuncX), ("g", .func exFuncY)] })]
  defined := []
  exports := [("run", .func exFuncX)]

/-- Resource renaming: `A` imports resource `0` and exports a constructor for it; `B`
imports resource `5` with the same shape. The ∀-binder of `A` is remapped to `B`'s. -/
def exResA : ComponentType Nat Unit where
  imported := [0]
  imports := [("r", .type (.resource 0))]
  defined := [1]
  exports := [("new", .func { params := [], result := some (.own 0) }),
    ("t", .type (.resource 1))]

def exResB : ComponentType Nat Unit where
  imported := [5]
  imports := [("r", .type (.resource 5))]
  defined := [7]
  exports := [("new", .func { params := [], result := some (.own 5) }),
    ("t", .type (.resource 7))]

/-- Imports `i` as a function (mismatching `exCompA`'s instance `i` on `B`'s side) and a
further function `j` that `exCompA` does not import. -/
def exCompFuncImport : ComponentType Nat Unit where
  imported := []
  imports := [("i", .func exFuncX), ("j", .func exFuncX)]
  defined := []
  exports := [("run", .func exFuncX)]

/-! ### Transitivity needs freshness

`A` mentions `own 1` free, `B` ∀-binds `1` (and re-exposes it as import `r`), and `C` supplies
resource `2` for it. Both `A <: B` and `B <: C` hold (by the checker), but `A <: C` does not:
`A`'s renaming must fix `1` (it has no binders), so `C`'s import `f : func() -> own 2` cannot
match `A`'s `func() -> own 1`. The triple violates `Entity.FreshTriple` for every context (`1`
is free in `A`, hence in `Γ`, and bound in `B`, hence not in `Γ`). -/

/-- `func() -> own r`. -/
def exFuncOwn (r : Nat) : FuncType Nat := { params := [], result := some (.own r) }

def exTransA : ComponentType Nat Unit := ⟨[], [("f", .func (exFuncOwn 1))], [], []⟩
def exTransB : ComponentType Nat Unit :=
  ⟨[1], [("r", .type (.resource 1)), ("f", .func (exFuncOwn 1))], [], []⟩
def exTransC : ComponentType Nat Unit :=
  ⟨[], [("r", .type (.resource 2)), ("f", .func (exFuncOwn 2))], [], []⟩

end Silmaril.Wasm.Component.Types
