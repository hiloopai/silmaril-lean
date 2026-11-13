module

public import Silmaril.Wasm.Tools.Gen.Core.Defs
public import Silmaril.Wasm.Wit.Valid.Defs
public import Silmaril.Wasm.Wit.Text.Print.Defs
public import Silmaril.Wasm.Tools.Gen.Wit.Defs

/-!
# `wasm-tools wit-smith`: a seeded generator of WIT packages

`rawDoc cfg seed` reads a seed (`Silmaril.Wasm.Tools.Gen.Cmd.Seed`, the `arbitrary` crate's
reading) as choices and builds a WIT document (`Silmaril.Wasm.Wit.Document`, wasm-wit's
syntax) of one package:

* interfaces with type definitions (records, variants, enums, flags, aliases, resources with a
  constructor, methods and static functions), functions, and `use`s of the types of earlier
  interfaces;
* worlds importing and exporting interfaces of the package and functions, and (with
  `--world-include`) including earlier worlds;
* types built from the primitive types, earlier type definitions, owned handles (`borrow`
  only as a top-level parameter), `list`, `option`, `result`, `tuple`, and with the flags
  `future`, `stream` (never of `char`), `error-context` and fixed-length lists; functions are
  `async` with `--async`.

Names are kebab-case words made unique by indices (`i0`, `t0x1`, `f3`, …), so every name a
scope binds is distinct and no keyword is used. Types refer only to earlier definitions, so
the type graph is acyclic.

The construction aims at validity in wasm-wit's sense (`Silmaril.Wasm.Wit.Valid`) and at the
printer's fragment (`Text.printable`), using only the features the flags allow; it is not
trusted for them: `Thms.witLang` is the language with that validity, decided by `Wit.check`
(`check_iff`), and `Thms.witSmith` the checked generator (an instance of the generic API,
`Generator.guarded`), whose fallback is the document `package wit-smith:fallback; world w {}`.
`accepts` also checks the features (`featOk`, at the point `feat cfg` of the WIT feature
lattice of `Silmaril.Wasm.Tools.Gen.Wit`), so `wit-smith` is an instance of that API's `witLang`
(`Thms.witGenU`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WitSmith

open Silmaril.Wasm.Wit

/-- `wit_smith::Config` (upstream's defaults). -/
structure Config where
  maxPackages : Nat := 10
  maxTypeSize : Nat := 100
  maxInterfaceItems : Nat := 10
  maxWorldItems : Nat := 10
  maxPkgItems : Nat := 10
  maxTypeParts : Nat := 10
  maxFilesPerPackage : Nat := 10
  maxResourceItems : Nat := 10
  async : Bool := false
  futures : Bool := false
  streams : Bool := false
  errorContext : Bool := false
  fixedLengthLists : Bool := false
  worldInclude : Bool := false
  deriving Repr, Inhabited

/-- `--arbitrary-config`: the configuration drawn from the seed, in the ranges of
`impl Arbitrary for wit_smith::Config` (`world_include` stays off, as upstream). -/
def arbitraryConfig : G Config := do
  let maxPackages ← G.range 1 20
  let maxFilesPerPackage ← G.range 1 10
  let maxTypeSize ← G.range 0 1000
  let maxInterfaceItems ← G.range 0 20
  let maxWorldItems ← G.range 0 10
  let maxPkgItems ← G.range 1 10
  let maxTypeParts ← G.range 1 10
  let maxResourceItems ← G.range 0 10
  let async ← G.bool
  let futures ← G.bool
  let streams ← G.bool
  let errorContext ← G.bool
  let fixedLengthLists ← G.bool
  return { maxPackages, maxTypeSize, maxInterfaceItems, maxWorldItems, maxPkgItems,
           maxTypeParts, maxFilesPerPackage, maxResourceItems, async, futures, streams,
           errorContext, fixedLengthLists }

/-- The primitive types. -/
def prims : List Ty :=
  [.bool, .s8, .s16, .s32, .s64, .u8, .u16, .u32, .u64, .f32, .f64, .char, .string]

/-- A type definition in scope: its name and whether it is a resource. -/
abbrev Scope := List (Name × Bool)

/-- What `genTy` may build. -/
inductive TK where
  | prim | named | own | list | option | result | tuple | future | stream | errCtx | fixed
  deriving DecidableEq, Repr, Inhabited

/-- The kinds applicable in `sc` under `cfg`. -/
def tks (cfg : Config) (sc : Scope) : List TK :=
  [TK.prim, .list, .option, .result, .tuple] ++
  (if sc.any (!·.2) then [.named] else []) ++
  (if sc.any (·.2) then [.own] else []) ++
  (if cfg.futures then [.future] else []) ++
  (if cfg.streams then [.stream] else []) ++
  (if cfg.errorContext then [.errCtx] else []) ++
  (if cfg.fixedLengthLists then [.fixed] else [])

/-- Does a type mention `char` outside nested `stream`s? (`stream<char>` is refused by
wasmparser; upstream rejects such seeds.) -/
def Ty.isChar : Ty → Bool
  | .char => true
  | _ => false

mutual
/-- A type of size at most `fuel` (leaves at `0`): handles to resources in scope only owned. -/
def genTy (cfg : Config) (sc : Scope) : Nat → G Ty
  | 0 => G.pick .u32 prims
  | fuel + 1 => do
    match ← G.pick .prim (tks cfg sc) with
    | .prim => G.pick .u32 prims
    | .named => return .named (← G.pick "" ((sc.filter (!·.2)).map (·.1)))
    | .own => return .own (← G.pick "" ((sc.filter (·.2)).map (·.1)))
    | .list => return .list (← genTy cfg sc fuel)
    | .option => return .option (← genTy cfg sc fuel)
    | .result =>
      let a ← genOpt cfg sc fuel
      let b ← genOpt cfg sc fuel
      return .result a b
    | .tuple =>
      let n ← G.range 1 (max 1 (min cfg.maxTypeParts 4))
      return .tuple (← genTys cfg sc fuel n)
    | .future => return .future (← genOpt cfg sc fuel)
    | .stream =>
      let t ← genOpt cfg sc fuel
      return .stream (if t.any Ty.isChar then some .u8 else t)
    | .errCtx => return .errorContext
    | .fixed => return .fixedList (← genTy cfg sc fuel) (← G.range 1 8)
termination_by fuel => (fuel, 0)

/-- An optional type. -/
def genOpt (cfg : Config) (sc : Scope) (fuel : Nat) : G (Option Ty) := do
  if ← G.bool then return some (← genTy cfg sc fuel) else return none
termination_by (fuel, 1)

/-- `n` types. -/
def genTys (cfg : Config) (sc : Scope) (fuel : Nat) : Nat → G (List Ty)
  | 0 => return []
  | n + 1 => return (← genTy cfg sc fuel) :: (← genTys cfg sc fuel n)
termination_by n => (fuel, n + 1)
end

/-- The type depth: `max-type-size` bounds the size, so the depth is small. -/
def depthOf (cfg : Config) : Nat := min 3 cfg.maxTypeSize

/-- `n` results of `g`, indexed. -/
def many {α : Type} (g : Nat → G α) (n : Nat) : G (List α) := G.many' g n
where
  /-- In index order. -/
  G.many' (g : Nat → G α) : Nat → G (List α)
    | 0 => return []
    | n + 1 => return (← G.many' g n) ++ [← g n]

/-- A function type: parameters `p0 …` (a `borrow` of a resource in scope allowed at the top
of a parameter), an optional result. -/
def genFunc (cfg : Config) (sc : Scope) : G Silmaril.Wasm.Wit.Func := do
  let np ← G.choose (min cfg.maxTypeParts 4 + 1)
  let params ← many (fun j => do
    let t ← if sc.any (·.2) && (← G.choose 4) == 0 then
        pure (Ty.borrow (← G.pick "" ((sc.filter (·.2)).map (·.1))))
      else genTy cfg sc (depthOf cfg)
    return (s!"p{j}", t)) np
  let result ← if ← G.bool then pure (some (← genTy cfg sc (depthOf cfg))) else pure none
  let async ← if cfg.async then G.bool else pure false
  return { params, result, async }

/-- A non-empty list of `k ≥ 1` labels `{pre}{j}`. -/
def labels (pre : String) (k : Nat) : List String := (List.range k).map (s!"{pre}{·}")

/-- A type definition named `n`. -/
def genTypeDef (cfg : Config) (sc : Scope) (n : Name) : G (TypeDef × Bool) := do
  let parts ← G.range 1 (max 1 cfg.maxTypeParts)
  let d := depthOf cfg
  match ← G.choose 6 with
  | 0 => return (⟨n, .record (← (labels "a" parts).mapM fun l => do
      return ({ name := l, ty := ← genTy cfg sc d } : Field)), {}, []⟩, false)
  | 1 => return (⟨n, .variant (← (labels "c" parts).mapM fun l => do
      return ({ name := l, ty := ← genOpt cfg sc d } : Case)), {}, []⟩, false)
  | 2 => return (⟨n, .enum ((labels "e" parts).map fun l => { name := l }), {}, []⟩, false)
  | 3 => return (⟨n, .flags ((labels "g" (min parts 32)).map fun l => { name := l }), {}, []⟩,
      false)
  | 4 => return (⟨n, .alias (← genTy cfg sc d), {}, []⟩, false)
  | _ =>
    -- a resource: an optional constructor, methods and statics (`sc` already has it)
    let sc' := sc ++ [(n, true)]
    let k ← G.choose (cfg.maxResourceItems + 1)
    let ctor ← G.bool
    let fs ← many (fun j => do
      let f ← genFunc cfg sc'
      if ← G.bool then return ({ kind := .method s!"m{j}", func := f } : ResourceFunc)
      else return ({ kind := .static s!"m{j}", func := f } : ResourceFunc)) k
    let c : List ResourceFunc := if ctor then
      [{ kind := .ctor, func := { params := [("p0", .u32)] } }] else []
    return (⟨n, .resource (c ++ fs), {}, []⟩, true)

/-- An interface `i{k}`: `use`s of earlier interfaces' types, type definitions `t{k}x{j}` and
functions `f{k}x{j}`. -/
def genIface (cfg : Config) (earlier : List (Name × Scope)) (k : Nat) : G (Interface × Scope) := do
  let n ← G.choose (cfg.maxInterfaceItems + 1)
  -- uses: some types of one earlier interface
  let (uses, sc0) ← if earlier.isEmpty || (← G.bool) then pure ([], []) else do
    let (iname, isc) ← G.pick ("", []) earlier
    if isc.isEmpty then pure ([], [])
    else
      let (tn, res) ← G.pick ("", false) isc
      pure ([IfaceItem.use ⟨.local iname, [{ name := tn }], []⟩], [(tn, res)])
  let rec go : Nat → Scope → List IfaceItem → G (List IfaceItem × Scope)
    | 0, sc, acc => return (acc, sc)
    | j + 1, sc, acc => do
      let idx := n - (j + 1)
      if ← G.bool then
        let tn := s!"t{k}x{idx}"
        let (td, res) ← genTypeDef cfg sc tn
        go j (sc ++ [(tn, res)]) (acc ++ [.type td])
      else
        let f ← genFunc cfg sc
        go j sc (acc ++ [.func { name := s!"f{k}x{idx}", func := f }])
  let (items, sc) ← go n sc0 []
  return (⟨s!"i{k}", uses ++ items, {}, []⟩, sc.drop sc0.length)

/-- A world `w{k}`: imports and exports of distinct interfaces, functions `g{k}x{j}`, and with
`--world-include` an `include` of an earlier world. -/
def genWorld (cfg : Config) (ifaces : List Name) (earlierWorlds : List Name) (k : Nat) :
    G World := do
  let n ← G.choose (cfg.maxWorldItems + 1)
  let rec go : Nat → List Name → List WorldItem → G (List WorldItem)
    | 0, _, acc => return acc
    | j + 1, avail, acc => do
      let idx := n - (j + 1)
      match ← G.choose 4 with
      | 0 | 1 =>
        if avail.isEmpty then go j avail acc else
          let i ← G.pick "" avail
          let e : WorldExtern := { ext := .path (.local i) }
          let it := if (← G.bool) then WorldItem.import e else .export e
          go j (avail.filter (· != i)) (acc ++ [it])
      | _ =>
        let f ← genFunc cfg []
        let e : WorldExtern := { ext := .func s!"g{k}x{idx}" f }
        let it := if (← G.bool) then WorldItem.import e else .export e
        go j avail (acc ++ [it])
  let items ← go n ifaces []
  let incl ← if cfg.worldInclude && !earlierWorlds.isEmpty && (← G.bool) then do
      pure [WorldItem.include ⟨.local (← G.pick "" earlierWorlds), [], []⟩]
    else pure []
  return ⟨s!"w{k}", incl ++ items, {}, []⟩

/-- **The raw generator**: one package `ns{a}:pkg{b}` (with an optional version) of
interfaces and worlds (at least one world). -/
def genDoc (cfg : Config) : G Document := do
  let a ← G.choose 10
  let b ← G.choose 10
  let version ← if ← G.bool then
      pure (some ({ major := ← G.choose 10, minor := ← G.choose 10, patch := ← G.choose 10 } :
        Version))
    else pure none
  let nItems ← G.range 1 (max 1 cfg.maxPkgItems)
  let nIfaces ← G.choose nItems
  let rec ifs : Nat → List (Name × Scope) → List Interface → G (List Interface)
    | 0, _, acc => return acc
    | j + 1, earlier, acc => do
      let (i, sc) ← genIface cfg earlier (nIfaces - (j + 1))
      ifs j (earlier ++ [(i.name, sc.filter (!·.2))]) (acc ++ [i])
  let ifaces ← ifs nIfaces [] []
  let nWorlds := max 1 (nItems - nIfaces)
  let rec ws : Nat → List Name → List World → G (List World)
    | 0, _, acc => return acc
    | j + 1, earlier, acc => do
      let w ← genWorld cfg (ifaces.map (·.name)) earlier (nWorlds - (j + 1))
      ws j (earlier ++ [w.name]) (acc ++ [w])
  let worlds ← ws nWorlds [] []
  return { main := { name := { ns := s!"ns{a}", name := s!"pkg{b}", version },
                     items := ifaces.map .iface ++ worlds.map .world } }

/-- The raw document of a seed (`--arbitrary-config`: the configuration first). -/
def rawDoc (cfg : Config) (arbitrary : Bool) (seed : ByteArray) : Document :=
  G.run' (do
    let c ← if arbitrary then arbitraryConfig else pure cfg
    genDoc c) seed

/-- The fallback: `package wit-smith:fallback; world w { }`. -/
def fallback : Document :=
  { main := { name := { ns := "wit-smith", name := "fallback" },
              items := [.world ⟨"w", [], {}, []⟩] } }

/-- Is the document valid in wasm-wit's sense and printable? -/
def checkDoc (d : Document) : Bool := Wit.check d.packages && Text.printable d

/-- The point of the WIT feature lattice of `Silmaril.Wasm.Tools.Gen.Wit` (the API instance) that
a configuration selects: its five feature flags, or every flag with `--arbitrary-config` (the
drawn configuration may turn any of them on). -/
def feat (cfg : Config) (arbitrary : Bool) : Silmaril.Wasm.Tools.Gen.Wit.WitFeat :=
  if arbitrary then .all
  else ⟨cfg.async, cfg.futures, cfg.streams, cfg.errorContext, cfg.fixedLengthLists⟩

/-- Does the document use only the features of the configuration
(`Silmaril.Wasm.Tools.Gen.Wit.universeInF`)? -/
def featOk (cfg : Config) (arbitrary : Bool) (d : Document) : Bool :=
  Silmaril.Wasm.Tools.Gen.Wit.universeInF (feat cfg arbitrary) d.packages

/-- The check `wit-smith` applies: `checkDoc` and `featOk`. -/
def accepts (cfg : Config) (arbitrary : Bool) (d : Document) : Bool :=
  checkDoc d && featOk cfg arbitrary d

/-- **`wasm-tools wit-smith`'s document**: the raw one when `accepts` holds of it, else the
fallback. -/
def witSmith (cfg : Config) (arbitrary : Bool) (seed : ByteArray) : Document :=
  if accepts cfg arbitrary (rawDoc cfg arbitrary seed) then rawDoc cfg arbitrary seed else fallback

end Silmaril.Wasm.Tools.Gen.Cmd.WitSmith
