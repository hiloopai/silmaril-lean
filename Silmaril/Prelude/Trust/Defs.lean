module

public import Lean
public meta import Lake.Toml

/-! # Trust: native decision procedures, allow-sets and the scope policy

A theorem whose proof runs compiled code is not checked by the kernel alone. Lean records each
such run as its own axiom: `Lean.Meta.nativeEqTrue` compiles a closed `Bool` term `e`, runs it,
and on `true` adds `axiom d._native.<tactic>.ax_i_j : e = true`. That axiom is how plain
`decide +native` works in this toolchain (there is no `Lean.ofReduceBool`). Its truth rests on the
Lean compiler, the runtime, and every `@[extern]`, `@[implemented_by]` and `@[csimp]` the
compiled code reaches. That trust is narrower than "anything goes" but it is **not**
kernel-only, and nothing here claims otherwise.

This module makes that trust explicit, named and bounded:

* A **native procedure** (`native_decider`, `Silmaril.Prelude.Trust.Elab`) is a named closed
  `Bool`-valued function. Only registered procedures run natively, and only through
  `edge_decide`. The registration records whether a **kernel fallback** (the kernel evaluating
  the same term, as `decide +kernel` does) is feasible. A procedure without one fails closed
  when native use is not allowed.
* A **trust set** (`trust_set`) is a named set of procedure or axiom names, built from members,
  other sets and `all`.
* The **scope policy** (`[native]` in `policy.toml`, loaded and pinned by `trust_policy`) gives
  each module prefix four sets. `max` bounds the native procedures the scope may run; `default`
  is what it runs in the default profile (cut down to `max`); `deps` lists the native
  procedures it accepts through imported theorems; `axioms` lists its other allowed axioms. A
  scope inherits each key it does not set from its parent, and a child's `max`, `deps` and
  `axioms` must each lie within its parent's: no scope can grant more than its parent.
* The **profile** is the option `silmaril.trust.profile`: `default` uses each scope's `default`,
  `local` its `max`, `paranoid` nothing (kernel fallbacks or failure). Any other value names a
  trust set, intersected with the scope's `max`. The statement proved never depends on the
  profile; only the proof term does. The **ceiling** `silmaril.trust.ceiling` (default `local`,
  that is no extra bound) is set only by the build: what runs natively is allowed by both.
  Builds with different profiles use different build directories (`scripts/trust-profile.sh`),
  because the options are part of every module's trace.
* Every `edge_decide` records a **use** (declaration, module, procedure, native or kernel,
  axiom). `#trust_uses` prints them as JSON lines, and `trust_audit` checks the axioms of
  declarations against the policy, separating a declaration's own native runs from those it
  inherits.
-/

public meta section

namespace Silmaril.Trust

open Lean

register_option silmaril.trust.profile : String := {
  defValue := "default"
  descr := "Trust profile for `edge_decide`: `default`, `local`, `paranoid` or a trust set name."
}

register_option silmaril.trust.ceiling : String := {
  defValue := "local"
  descr := "The build's bound on `silmaril.trust.profile` (set by scripts/trust-profile.sh only)."
}

/-- A registered native decision procedure. -/
structure Procedure where
  /-- Its name in policies, e.g. `bytes.sameBytes`. -/
  name : Name
  /-- The closed `Bool`-valued function constant it runs. -/
  fn : Name
  /-- Whether the kernel can feasibly evaluate the same term (a fallback exists). -/
  kernel : Bool
  /-- One-line description, including what is trusted beyond the kernel. -/
  doc : String
  /-- The module that registered it. -/
  module : Name
  /-- The data format it checks (`elf`, `json`, `cbor`, `sexpr`, `wat`, …), if it is a format
  checker (`Silmaril.KBytes.FormatChecker`). -/
  format : Option Name := none
  /-- The theorem turning `fn … = true` into the fact it decides, if registered. -/
  sound : Option Name := none
  /-- A separate implementation for native runs and the theorem `@native = @fn` that transfers
  its result (the paired backend: `fn` is what the kernel and the statement see). -/
  native : Option (Name × Name) := none
  deriving Inhabited, Repr

/-- The version of the JSON lines `#trust_uses` and `trust_audit` print
(docs/trust.md, "Provenance schema"). -/
def schemaVersion : String := "silmaril.trust.v1"

/-- A named set of procedure (or axiom) names. -/
structure TrustSet where
  name : Name
  /-- Every name. -/
  all : Bool := false
  members : Array Name := #[]
  /-- Sets whose members are included. -/
  includes : Array Name := #[]
  deriving Inhabited, Repr

/-- One scope of the policy: a module prefix and its sets (`none` inherits from the parent). -/
structure Scope where
  /-- Module name prefix (`Silmaril` for the root). -/
  module : Name
  max : Option Name := none
  /-- The TOML key `default`. -/
  dflt : Option Name := none
  deps : Option Name := none
  axiomSet : Option Name := none
  deriving Inhabited, Repr

/-- The loaded policy: scopes, the file it came from and its hash pin. -/
structure Policy where
  scopes : Array Scope := #[]
  /-- Named axiom sets from the file (`standard`), as trust sets. -/
  sets : Array TrustSet := #[]
  file : String := ""
  hash : UInt64 := 0
  deriving Inhabited, Repr

/-- How an `edge_decide` was discharged. -/
inductive Mode where
  | native
  | kernel
  deriving Inhabited, Repr, BEq

/-- A use of a procedure, recorded for provenance. -/
structure Use where
  decl : Name
  module : Name
  proc : Name
  mode : Mode
  profile : String
  /-- The axiom added by a native run. -/
  ax : Option Name := none
  deriving Inhabited, Repr, BEq

initialize procExt : SimplePersistentEnvExtension Procedure (NameMap Procedure) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m p => m.insert p.name p
    addImportedFn := fun mods => mods.foldl (fun m ps => ps.foldl (fun m p => m.insert p.name p) m) {}
  }

initialize setExt : SimplePersistentEnvExtension TrustSet (NameMap TrustSet) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m s => m.insert s.name s
    addImportedFn := fun mods => mods.foldl (fun m ss => ss.foldl (fun m s => m.insert s.name s) m) {}
  }

initialize policyExt : SimplePersistentEnvExtension Policy (Option Policy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ p => some p
    addImportedFn := fun mods => mods.foldl (fun acc ps => ps.foldl (fun _ p => some p) acc) none
  }

/-- Uses are recorded while theorems elaborate in parallel, so the extension is `sync` and
replays the entries of each branch into the module. -/
initialize useExt : SimplePersistentEnvExtension Use (Array Use) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s u => s.push u
    addImportedFn := fun _ => #[]
    asyncMode := .sync
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (fun s u => s.contains u) (·.push ·)
  }

/-- Every entry of a simple extension: imported modules in order, then the current module. -/
def allEntries {α σ : Type} [Inhabited α] [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
    (env : Environment) : Array α := Id.run do
  let mut out := #[]
  for modIdx in [0:env.header.modules.size] do
    out := out ++ ext.getModuleEntries env modIdx
  return out ++ (ext.getEntries env).reverse.toArray

/-! ## Sets -/

/-- A resolved set: every name, or the listed ones. -/
inductive Members where
  | all
  | some (names : NameSet)
  deriving Inhabited

namespace Members

def contains : Members → Name → Bool
  | all, _ => true
  | some s, n => s.contains n

def inter : Members → Members → Members
  | all, m | m, all => m
  | some a, some b => some (a.foldl (fun acc n => if b.contains n then acc.insert n else acc) {})

def union : Members → Members → Members
  | all, _ | _, all => all
  | some a, some b => some (a.foldl (·.insert ·) b)

def subset : Members → Members → Bool
  | _, all => true
  | all, some _ => false
  | some a, some b => a.toList.all b.contains

def toList : Members → List Name
  | all => [`all]
  | some s => s.toList

end Members

/-- The sets the environment knows: declared with `trust_set`, or loaded from the policy file. -/
def findSet? (env : Environment) (n : Name) : Option TrustSet :=
  match (setExt.getState env).find? n with
  | some s => some s
  | none => ((policyExt.getState env).map (·.sets)).bind (·.find? (·.name == n))

/-- Resolve a set name (`all` and `none` are built in); `fuel` bounds include chains. -/
def resolve (env : Environment) (n : Name) (fuel : Nat := 64) : Except String Members := do
  if n == `all then return .all
  if n == `none then return .some {}
  match fuel with
  | 0 => throw s!"trust set {n}: includes nest too deeply (a cycle?)"
  | fuel + 1 =>
    let some s := findSet? env n | throw s!"unknown trust set {n}"
    if s.all then return .all
    let mut acc : Members := .some (s.members.foldl (·.insert ·) {})
    for i in s.includes do
      acc := acc.union (← resolve env i fuel)
    return acc

/-! ## Scopes -/

/-- The scopes that apply to `mod`, outermost first. -/
def chain (p : Policy) (mod : Name) : Array Scope :=
  let hits := p.scopes.filter fun s => s.module.isPrefixOf mod
  hits.qsort fun a b => a.module.getNumParts < b.module.getNumParts

/-- The effective sets of a module: `max`, `default`, `deps` and `axioms`, inherited and bounded. -/
structure Effective where
  max : Members
  /-- The TOML key `default`. -/
  dflt : Members
  deps : Members
  axiomSet : Members
  /-- The scopes that set each value, for messages. -/
  trace : List String
  deriving Inhabited

/-- The effective sets of `mod` under the policy `p` (sets resolved in `env`). -/
def effectiveIn (env : Environment) (p : Policy) (mod : Name) : Except String Effective := do
  let none' : Members := .some {}
  let mut eff : Effective :=
    { max := none', dflt := none', deps := none', axiomSet := none', trace := [] }
  let mut first := true
  for s in chain p mod do
    let max ← match s.max with
      | some n => resolve env n
      | none => pure eff.max
    unless first || max.subset eff.max do
      throw s!"policy scope {s.module}: max exceeds its parent's max"
    let dflt ← match s.dflt with
      | some n => resolve env n
      | none => pure eff.dflt
    let deps ← match s.deps with
      | some n => resolve env n
      | none => pure eff.deps
    let axiomSet ← match s.axiomSet with
      | some n => resolve env n
      | none => pure eff.axiomSet
    -- No silent escalation: what a scope accepts through dependencies, and the axioms it
    -- allows, stay within its parent's, as `max` does.
    unless first || deps.subset eff.deps do
      throw s!"policy scope {s.module}: deps exceeds its parent's deps"
    unless first || axiomSet.subset eff.axiomSet do
      throw s!"policy scope {s.module}: axioms exceeds its parent's axioms"
    eff := { max, dflt := dflt.inter max, deps, axiomSet, trace := eff.trace ++ [s.module.toString] }
    first := false
  return eff

def effective (env : Environment) (mod : Name) : Except String Effective := do
  let some p := policyExt.getState env
    | throw "no trust policy is loaded: import Silmaril.Prelude.Trust.Policy"
  effectiveIn env p mod

/-- The native procedures `mod` may run in `profile`. -/
def allowedIn (env : Environment) (mod : Name) (profile : String) : Except String Members := do
  let eff ← effective env mod
  match profile with
  | "paranoid" => return .some {}
  | "local" => return eff.max
  | "default" => return eff.dflt
  | other => return (← resolve env other.toName).inter eff.max

/-- The native procedures `mod` may run in `profile` under the build's `ceiling`. A source file
may lower its profile (`set_option silmaril.trust.profile "paranoid" in …`) or pick any profile,
but never beyond the ceiling the build sets. -/
def allowed (env : Environment) (mod : Name) (profile ceiling : String) :
    Except String Members := do
  return (← allowedIn env mod profile).inter (← allowedIn env mod ceiling)

/-! ## The policy file -/

/-- FNV-1a, 64 bits, of the file's bytes: a pin against stale builds, not a security hash. -/
def fnv1a64 (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b.data do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  return h

/-- Hex digits of a 64-bit pin. -/
def hex64 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- Parse `[native]` scopes and the `standard` axiom list of `policy.toml`. -/
def parsePolicy (file : String) (bytes : ByteArray) : IO Policy := do
  let some text := String.fromUTF8? bytes | throw (IO.userError s!"{file}: not UTF-8")
  let ictx := Parser.mkInputContext text file
  let table ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error log =>
      let msgs ← log.toList.mapM (·.toString)
      throw (IO.userError s!"{file}: {String.intercalate "\n" msgs}")
  let strs (v : Lake.Toml.Value) : Array String := match v with
    | .array _ xs => xs.filterMap fun | .string _ s => some s | _ => none
    | _ => #[]
  let mut sets : Array TrustSet := #[]
  if let some v := table.find? `standard then
    sets := sets.push { name := `standard, members := (strs v).map (·.toName) }
  let mut scopes : Array Scope := #[]
  if let some (.table _ native) := table.find? `native then
    if let some (.array _ ss) := native.find? `scope then
      for s in ss do
        let .table _ t := s | throw (IO.userError s!"{file}: [[native.scope]] must be tables")
        let str (k : Name) : Option Name := match t.find? k with
          | some (.string _ s) => some s.toName
          | _ => none
        let some m := str `module | throw (IO.userError s!"{file}: a [[native.scope]] needs `module`")
        scopes := scopes.push
          { module := m, max := str `max, dflt := str `default, deps := str `deps,
            axiomSet := str `axioms }
  return { scopes, sets, file, hash := fnv1a64 bytes }

/-! ## Native-axiom provenance -/

/-- The procedure behind a native axiom `d._native.edge.<proc>.ax_i_j`, and `d`. Axioms from
plain `decide +native` or `bv_decide` (`d._native.<tactic>.ax_i_j`) come back as
`(d, <tactic>)` with `edge` absent. -/
def nativeAxiom? (n : Name) : Option (Name × Name × Bool) :=
  let parts := n.components
  match parts.findIdx? (· == `_native) with
  | none => none
  | some i =>
    let owner := (parts.take i).foldl (· ++ ·) .anonymous
    let owner := (privateToUserName? owner).getD owner
    let mid := (parts.drop (i + 1)).dropLast
    match mid with
    | `edge :: proc => some (owner, proc.foldl (· ++ ·) .anonymous, true)
    | tac => some (owner, tac.foldl (· ++ ·) .anonymous, false)

end Silmaril.Trust
