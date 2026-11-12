module

public import Silmaril.Wasm.JcoTool.Layout.Defs
public import Silmaril.Wasm.Component.RefValid.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs
public import Silmaril.Wasm.Perf.ValidateComp.Defs

/-!
# The layout reading of `wasm-jco`'s outputs, on the reference component syntax

`Silmaril.Wasm.JcoTool.Layout` reads a parsed output (`XComp`, sections of Silmaril's binary AST) by
index spaces it fills itself. This module gives the same reading on the **reference syntax of
the Component Model** (`Silmaril.Wasm.Component.Reference.CompAst`, silmaril's
`Syntax.Component`, which the reference instantiation, validation and machine are defined on),
and links the two:

* **`toRef rd x`**: the parsed output as a reference component, section by section, each
  section becoming its definitions in order (`rd` reads the core modules: bytes as they are,
  or silmaril's verified decoder for a `Core3Component`). The translation is partial: it fails
  on core module types, on a top-level `canon` section that is not `XSec.canons`, on aliases of core functions that are not core-instance exports, on
  core-instance export aliases of component sorts, on exports of core functions or core
  instances, and on core value types that the reference does not represent there (resource
  representations other than `i32`/`i64`); `wasm-jco`'s outputs have none of these. Custom
  sections are dropped (the reference does not represent them).
* **`readRef names c`**: the reading of a reference component. Its index spaces are filled
  definition by definition **by the reference's own index-space rule** (`Definition.sort`,
  `Builder.lean`, transcribing `Explainer.md` §Index Spaces at component-model `a25fc0b`): each
  definition appends to the space of `d.sort`, so the `i`-th core function is the `i`-th
  definition of sort `core func`, and the size of each space is `Component.nextIndex`. The
  resolution (exports to their lifts, the main module's core imports through the inline
  instances, the shim and the fixup, resources with their destructors) is `Layout.read`'s,
  over reference definitions.

`LayoutRef.Thms`: `read_toRef` (`Layout.read names x = readRef names c` whenever
`toRef rd x = some c`), `spacesRef_size` (the spaces are the reference's: their sizes are
`Component.nextIndex`), and `ToolV.newFullR_correct`: the output of `wasm-jco new`, read as a
reference component, has the layout the world describes.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRef

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Sort_ Syntax.CoreSort Syntax.SortIdx
  Syntax.Component)
open Silmaril.Wasm.JcoTool.Layout (FnRef ResRef CoreR LiftR ExpR Reading lookupS)

namespace B
export Silmaril.Wasm.Component.Binary (CoreSort ItemSort CoreSortIdx SortIdx ExternName NameForm
  Attribute CoreInstanceExpr InstanceExpr Alias AliasTarget CoreValType CoreFuncType CoreType
  PrimValType ValType DefValType FuncType ValueBound TypeBound ExternDesc DefType InstanceDecl
  ComponentDecl CanonOpt Canon Import Export Section Ast)
end B

/-! ## The translation to the reference syntax -/

def coreSortTo : B.CoreSort → Syntax.CoreSort
  | .func => .func | .table => .table | .memory => .memory | .global => .global
  | .tag => .tag | .type => .type | .module => .module_ | .instance => .instance_

def sortTo : B.ItemSort → Syntax.Sort_
  | .core s => .core (coreSortTo s)
  | .func => .func | .value => .value | .type => .type | .component => .component
  | .instance => .instance_

def sortIdxTo (si : B.SortIdx) : Syntax.SortIdx Syntax.Sort_ := ⟨sortTo si.sort, si.idx⟩

def coreSortIdxTo (si : B.CoreSortIdx) : Syntax.SortIdx Syntax.CoreSort :=
  ⟨coreSortTo si.sort, si.idx⟩

def attrTo : B.Attribute → Silmaril.Wasm.Component.Syntax.Attribute
  | .implements n => .implements n
  | .versionSuffix s => .versionSuffix s
  | .externalId i => .externalId i

def nameTo (n : B.ExternName) : Silmaril.Wasm.Component.Syntax.ExternName :=
  ⟨n.name, match n.form with
    | .attrs as => as.map attrTo
    | _ => []⟩

def primTo : B.PrimValType → Silmaril.Wasm.Component.Syntax.Prim
  | .bool => .bool | .s8 => .s8 | .u8 => .u8 | .s16 => .s16 | .u16 => .u16 | .s32 => .s32
  | .u32 => .u32 | .s64 => .s64 | .u64 => .u64 | .f32 => .f32 | .f64 => .f64 | .char => .char
  | .string => .string | .errorContext => .errorContext

def vtTo : B.ValType → Silmaril.Wasm.Component.Syntax.VT
  | .prim p => .prim (primTo p)
  | .idx i => .idx i

def defValTo : B.DefValType → Silmaril.Wasm.Component.Syntax.DefValType
  | .prim p => .prim (primTo p)
  | .record fs => .record (fs.map fun (n, t) => (n, vtTo t))
  | .variant cs => .variant (cs.map fun (n, t) => (n, t.map vtTo))
  | .list t => .list (vtTo t)
  | .tuple ts => .tuple (ts.map vtTo)
  | .flags ls => .flags ls
  | .enum ls => .enum ls
  | .option t => .option (vtTo t)
  | .result a b => .result (a.map vtTo) (b.map vtTo)
  | .own i => .own i
  | .borrow i => .borrow i
  | .fixedList t n => .fixedList (vtTo t) n
  | .stream t => .stream (t.map vtTo)
  | .future t => .future (t.map vtTo)
  | .map k v => .map (vtTo k) (vtTo v)

def funcTypeTo (f : B.FuncType) : Silmaril.Wasm.Component.Syntax.FuncType :=
  ⟨f.async, f.params.map fun (n, t) => (n, vtTo t), f.result.map vtTo⟩

def descTo : B.ExternDesc → Silmaril.Wasm.Component.Syntax.ExternDesc
  | .coreModule i => .coreModule i
  | .func i => .func i
  | .value (.eq i) => .value (.eq i)
  | .value (.type t) => .value (.type (vtTo t))
  | .type (.eq i) => .type (.eq i)
  | .type .subResource => .type .subResource
  | .component i => .component i
  | .instance i => .instance_ i

def coreValTo : B.CoreValType → Silmaril.Wasm.ValType
  | .i32 => .num (.int .i32)
  | .i64 => .num (.int .i64)
  | .f32 => .num (.float .f32)
  | .f64 => .num (.float .f64)
  | .v128 => .vec .v128
  | .funcref => .ref ⟨true, .abstract .func⟩
  | .externref => .ref ⟨true, .abstract .extern⟩

/-- A core type: a function type is a one-element recursion group; module types are not
translated. -/
def coreTypeTo : B.CoreType → Option Silmaril.Wasm.Component.Syntax.CoreTypeDef
  | .func t => some (.rec_ ⟨[⟨true, [], .func ⟨t.params.map coreValTo, t.results.map coreValTo⟩⟩]⟩)
  | .module _ => none

def addrTo : B.CoreValType → Option Silmaril.Wasm.AddrType
  | .i32 => some .i32
  | .i64 => some .i64
  | _ => none

/-- An alias; `none` for the combinations the binary reading of `Layout` does not count the
way the reference does (core functions that are not core-instance exports, core-instance
exports of component sorts). -/
def aliasTo (a : B.Alias) : Option Silmaril.Wasm.Component.Syntax.Alias :=
  match a.sort, a.target with
  | .core s, .coreExport i n => some (.coreExport i n (coreSortTo s))
  | .core .func, _ => none
  | _, .coreExport _ _ => none
  | s, .export i n => some (.export_ i n (sortTo s))
  | s, .outer c i => some (.outer c i (sortTo s))

mutual
def defTypeTo : B.DefType → Option Silmaril.Wasm.Component.Syntax.DefType
  | .val d => some (.val (defValTo d))
  | .func f => some (.func (funcTypeTo f))
  | .component ds => (compDeclsTo ds).map .component
  | .instance ds => (instDeclsTo ds).map .instance_
  | .resource rep d => (addrTo rep).map fun a => .resource a d
def instDeclTo : B.InstanceDecl → Option Silmaril.Wasm.Component.Syntax.InstanceDecl
  | .coreType t => (coreTypeTo t).map .coreType
  | .type t => (defTypeTo t).map .type
  | .alias a => (aliasTo a).map .alias
  | .export n d => some (.export_ (nameTo n) (descTo d))
def instDeclsTo : List B.InstanceDecl → Option (List Silmaril.Wasm.Component.Syntax.InstanceDecl)
  | [] => some []
  | d :: ds => do pure ((← instDeclTo d) :: (← instDeclsTo ds))
def compDeclTo : B.ComponentDecl → Option Silmaril.Wasm.Component.Syntax.ComponentDecl
  | .import n d => some (.import_ (nameTo n) (descTo d))
  | .inst d => (instDeclTo d).map .decl
def compDeclsTo : List B.ComponentDecl → Option (List Silmaril.Wasm.Component.Syntax.ComponentDecl)
  | [] => some []
  | d :: ds => do pure ((← compDeclTo d) :: (← compDeclsTo ds))
end

def optTo : B.CanonOpt → Silmaril.Wasm.Component.Syntax.CanonOpt
  | .utf8 => .encoding .utf8
  | .utf16 => .encoding .utf16
  | .latin1utf16 => .encoding .latin1Utf16
  | .memory i => .memory i
  | .realloc i => .realloc i
  | .postReturn i => .postReturn i
  | .async => .async_
  | .callback i => .callback i

def optsTo (os : List B.CanonOpt) : List Silmaril.Wasm.Component.Syntax.CanonOpt := os.map optTo

/-- An async built-in. The reference drops the `cancellable` immediates of `thread.yield` and
`waitable-set.wait`/`poll` and gives `context.get`/`set` their `i32` type. -/
def builtinTo : Builtin → Silmaril.Wasm.Component.Syntax.Builtin
  | .taskReturn r o => .taskReturn (r.map vtTo) (optsTo o)
  | .taskCancel => .taskCancel
  | .backpressureInc => .backpressureInc
  | .backpressureDec => .backpressureDec
  | .contextGet i => .contextGet .i32 i
  | .contextSet i => .contextSet .i32 i
  | .threadYield _ => .threadYield
  | .subtaskDrop => .subtaskDrop
  | .subtaskCancel a => .subtaskCancel a
  | .streamNew t => .streamNew t
  | .streamRead t o => .streamRead t (optsTo o)
  | .streamWrite t o => .streamWrite t (optsTo o)
  | .streamCancelRead t a => .streamCancelRead t a
  | .streamCancelWrite t a => .streamCancelWrite t a
  | .streamDropReadable t => .streamDropReadable t
  | .streamDropWritable t => .streamDropWritable t
  | .futureNew t => .futureNew t
  | .futureRead t o => .futureRead t (optsTo o)
  | .futureWrite t o => .futureWrite t (optsTo o)
  | .futureCancelRead t a => .futureCancelRead t a
  | .futureCancelWrite t a => .futureCancelWrite t a
  | .futureDropReadable t => .futureDropReadable t
  | .futureDropWritable t => .futureDropWritable t
  | .waitableSetNew => .waitableSetNew
  | .waitableSetWait _ m => .waitableSetWait m
  | .waitableSetPoll _ m => .waitableSetPoll m
  | .waitableSetDrop => .waitableSetDrop
  | .waitableJoin => .waitableJoin
  | .errorContextNew o => .errorContextNew (optsTo o)
  | .errorContextDebugMessage o => .errorContextDebugMessage (optsTo o)
  | .errorContextDrop => .errorContextDrop

def canonTo : B.Canon → Silmaril.Wasm.Component.Syntax.Canon
  | .lift f o t => .lift f (optsTo o) t
  | .lower f o => .lower f (optsTo o)
  | .resourceNew t => .builtin (.resourceNew t)
  | .resourceDrop t => .builtin (.resourceDrop t)
  | .resourceRep t => .builtin (.resourceRep t)

def xcanonTo : XCanon → Silmaril.Wasm.Component.Syntax.Canon
  | .canon c => canonTo c
  | .builtin b => .builtin (builtinTo b)

def coreInstTo : B.CoreInstanceExpr → Silmaril.Wasm.Component.Syntax.CoreInstanceExpr
  | .instantiate m args => .instantiate m args
  | .exports es => .exports (es.map fun (n, si) => (n, coreSortIdxTo si))

def instTo : B.InstanceExpr → Silmaril.Wasm.Component.Syntax.InstanceExpr
  | .instantiate c args => .instantiate c (args.map fun (n, si) => (n, sortIdxTo si))
  | .exports es => .exports (es.map fun (n, si) => (nameTo n, sortIdxTo si))

/-- An export; `none` for exports of core functions and core instances (which the reference
counts in their index spaces and the binary reading does not). -/
def exportTo {M : Type} (e : B.Export) : Option (Syntax.Definition M) :=
  match e.item.sort with
  | .core .func | .core .instance => none
  | _ => some (.export_ (nameTo e.name) (sortIdxTo e.item) (e.desc.map descTo))

section
variable {M : Type} (rd : ByteArray → Option M)

mutual
/-- A section of Silmaril's binary AST as reference definitions. -/
def secTo : B.Section → Option (List (Syntax.Definition M))
  | .custom _ _ => some []
  | .coreModule b => (rd b).map fun m => [.coreModule m]
  | .coreInstances xs => some (xs.map fun x => .coreInstance (coreInstTo x))
  | .coreTypes xs => (xs.mapM coreTypeTo).map (·.map .coreType)
  | .component c => (astTo c).map fun ds => [.component ds]
  | .instances xs => some (xs.map fun x => .instance_ (instTo x))
  | .aliases xs => (xs.mapM aliasTo).map (·.map .alias)
  | .types xs => (xs.mapM defTypeTo).map (·.map .type)
  | .canons xs => some (xs.map fun c => .canon (canonTo c))
  | .start s => some [.start s.func s.args s.results]
  | .imports xs => some (xs.map fun i => .import_ (nameTo i.name) (descTo i.desc))
  | .exports xs => xs.mapM exportTo
  | .values xs => some (xs.map fun v => .value (vtTo v.type) v.bytes.data.toList)
def secsTo : List B.Section → Option (List (Syntax.Definition M))
  | [] => some []
  | s :: ss => do pure ((← secTo s) ++ (← secsTo ss))
def astTo : B.Ast → Option (List (Syntax.Definition M))
  | .mk ss => secsTo ss
end

/-- A section of a parsed output (`xparse` reads every top-level `canon` section as
`XSec.canons`; a `.sec (.canons _)` is not one of its results and is not translated). -/
def xsecTo : XSec → Option (List (Syntax.Definition M))
  | .sec (.canons _) => none
  | .sec s => secTo rd s
  | .canons xs => some (xs.map fun c => .canon (xcanonTo c))

/-- **A parsed output as a reference component.** -/
def toRef (x : XComp) : Option (Syntax.Component M) :=
  (x.sections.mapM (xsecTo rd)).map List.flatten

end

/-! ## Index spaces of a reference component -/

/-- A core function. -/
inductive CF where
  | lower (f : Nat) (opts : List Silmaril.Wasm.Component.Syntax.CanonOpt)
  | builtin (b : Silmaril.Wasm.Component.Syntax.Builtin)
  | alias (inst : Nat) (name : String)
  | other
  deriving Inhabited

/-- A core instance. -/
inductive CI where
  | inst (m : Nat) (args : List (String × Nat))
  | exps (es : List (String × Syntax.SortIdx Syntax.CoreSort))
  | other
  deriving Inhabited

/-- A function. -/
inductive FF where
  | imp (name : String)
  | alias (inst : Nat) (name : String)
  | lift (cf : Nat) (opts : List Silmaril.Wasm.Component.Syntax.CanonOpt)
  | other
  deriving Inhabited

/-- An instance. -/
inductive II where
  | imp (name : String)
  | inst (comp : Nat) (args : List (String × Syntax.SortIdx Syntax.Sort_))
  | other
  deriving Inhabited

/-- A type. -/
inductive TT where
  | alias (inst : Nat) (name : String)
  | resource (dtor : Option Nat)
  | other
  deriving Inhabited

/-- The five index spaces the reading uses, and the exports. -/
structure RS where
  cf : Array CF := #[]
  ci : Array CI := #[]
  ff : Array FF := #[]
  ii : Array II := #[]
  tt : Array TT := #[]
  exports : Array (String × Syntax.SortIdx Syntax.Sort_) := #[]

section
variable {M : Type}

def cfOf : Syntax.Definition M → CF
  | .canon (.lower f o) => .lower f o
  | .canon (.builtin b) => .builtin b
  | .alias (.coreExport i n _) => .alias i n
  | _ => .other

def ciOf : Syntax.Definition M → CI
  | .coreInstance (.instantiate m a) => .inst m a
  | .coreInstance (.exports es) => .exps es
  | _ => .other

def ffOf : Syntax.Definition M → FF
  | .import_ n _ => .imp n.name
  | .alias (.export_ i n _) => .alias i n
  | .canon (.lift cf o _) => .lift cf o
  | _ => .other

def iiOf : Syntax.Definition M → II
  | .import_ n _ => .imp n.name
  | .instance_ (.instantiate c a) => .inst c a
  | _ => .other

def ttOf : Syntax.Definition M → TT
  | .alias (.export_ i n _) => .alias i n
  | .type (.resource _ d) => .resource d
  | _ => .other

/-- Record an export. -/
def addExport (r : RS) : Syntax.Definition M → RS
  | .export_ n si _ => { r with exports := r.exports.push (n.name, si) }
  | _ => r

/-- **One definition, by the reference's index-space rule**: it appends to the space of its
`Definition.sort` (the spaces of other sorts are not kept). -/
def def1 (r : RS) (d : Syntax.Definition M) : RS :=
  let r := addExport r d
  match d.sort with
  | .core .func => { r with cf := r.cf.push (cfOf d) }
  | .core .instance_ => { r with ci := r.ci.push (ciOf d) }
  | .func => { r with ff := r.ff.push (ffOf d) }
  | .instance_ => { r with ii := r.ii.push (iiOf d) }
  | .type => { r with tt := r.tt.push (ttOf d) }
  | _ => r

/-- The index spaces of a reference component. -/
def spacesRef (c : Syntax.Component M) : RS := c.foldl def1 {}

end

/-! ## The reading -/

/-- The kind of a built-in, as `Layout.bkind` names it. -/
def bkind : Silmaril.Wasm.Component.Syntax.Builtin → String
  | .taskReturn _ _ => "task.return"
  | .taskCancel => "task.cancel"
  | .backpressureInc => "backpressure.inc"
  | .backpressureDec => "backpressure.dec"
  | .contextGet _ i => s!"context.get {i}"
  | .contextSet _ i => s!"context.set {i}"
  | .threadYield => "thread.yield"
  | .subtaskDrop => "subtask.drop"
  | .subtaskCancel _ => "subtask.cancel"
  | .streamNew _ => "stream.new"
  | .streamRead _ o => if o.contains .async_ then "stream.read async" else "stream.read"
  | .streamWrite _ o => if o.contains .async_ then "stream.write async" else "stream.write"
  | .streamCancelRead _ a => if a then "stream.cancel-read async" else "stream.cancel-read"
  | .streamCancelWrite _ a => if a then "stream.cancel-write async" else "stream.cancel-write"
  | .streamDropReadable _ => "stream.drop-readable"
  | .streamDropWritable _ => "stream.drop-writable"
  | .futureNew _ => "future.new"
  | .futureRead _ o => if o.contains .async_ then "future.read async" else "future.read"
  | .futureWrite _ o => if o.contains .async_ then "future.write async" else "future.write"
  | .futureCancelRead _ a => if a then "future.cancel-read async" else "future.cancel-read"
  | .futureCancelWrite _ a => if a then "future.cancel-write async" else "future.cancel-write"
  | .futureDropReadable _ => "future.drop-readable"
  | .futureDropWritable _ => "future.drop-writable"
  | .waitableSetNew => "waitable-set.new"
  | .waitableSetWait _ => "waitable-set.wait"
  | .waitableSetPoll _ => "waitable-set.poll"
  | .waitableSetDrop => "waitable-set.drop"
  | .waitableJoin => "waitable.join"
  | .errorContextNew _ => "error-context.new"
  | .errorContextDebugMessage _ => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop"
  | .resourceNew _ => "resource.new"
  | .resourceDrop _ => "resource.drop"
  | .resourceRep _ => "resource.rep"
  | .streamForward _ => "stream.forward"
  | .futureForward _ => "future.forward"
  | .threadIndex => "thread.index"
  | .threadNewIndirect _ _ => "thread.new-indirect"
  | .threadResumeLater => "thread.resume-later"
  | .threadSuspend => "thread.suspend"
  | .threadSuspendThenResume => "thread.suspend-then-resume"
  | .threadYieldThenResume => "thread.yield-then-resume"
  | .threadSuspendThenPromote => "thread.suspend-then-promote"
  | .threadYieldThenPromote => "thread.yield-then-promote"

section
variable (r : RS)

/-- The main instance: the instance of core module `0`. -/
def mainInst : Option Nat := (r.ci.toList.zipIdx.find? fun (c, _) => match c with
  | .inst 0 _ => true
  | _ => false).map (·.2)

def fnRef (f : Nat) : Option FnRef :=
  match r.ff[f]? with
  | some (.imp n) => some (.world n)
  | some (.alias i n) => match r.ii[i]? with
    | some (.imp k) => some (.iface k n)
    | _ => none
  | _ => none

/-- The exported interface whose shim component takes type `t` as `import-type-n`. -/
def exportedRes (t : Nat) : Option ResRef :=
  r.exports.toList.findSome? fun (k, si) => match si.sort, r.ii[si.idx]? with
    | .instance_, some (.inst _ args) => args.findSome? fun (an, ai) =>
        if ai.sort == .type && ai.idx == t then
          (an.dropPrefix? "import-type-").map fun s => .exported k s.toString
        else none
    | _, _ => none

def resRef (t : Nat) : Option ResRef :=
  match r.tt[t]? with
  | some (.alias i n) => match r.ii[i]? with
    | some (.imp k) => some (.imported k n)
    | _ => none
  | some (.resource _) => exportedRes r t
  | _ => none

/-- What defines core function `i`. -/
def coreR : Nat → Nat → Option CoreR
  | 0, _ => none
  | fuel + 1, i =>
    match r.cf[i]? with
    | some (.lower f opts) => (fnRef r f).map fun fr => .lower fr (opts.contains .async_)
    | some (.builtin (.resourceNew t)) => (resRef r t).map .resNew
    | some (.builtin (.resourceRep t)) => (resRef r t).map .resRep
    | some (.builtin (.resourceDrop t)) => (resRef r t).map .resDrop
    | some (.builtin b) => some (.builtin (bkind b))
    | some (.alias inst n) => match r.ci[inst]? with
      | some (.inst 0 _) => some (.mainExport n)
      | some (.inst _ []) =>
        r.ci.toList.findSome? fun c => match c with
          | .inst _ args =>
            if lookupS "shim" args == some inst then
              match (lookupS "actual" args).bind (r.ci[·]?) with
              | some (.exps es) => match lookupS n es with
                | some si => if si.sort == .func then coreR fuel si.idx else none
                | none => none
              | _ => none
            else none
          | _ => none
      | _ => none
    | some .other => none
    | none => none

def mainName (i : Nat) : Option String :=
  match r.cf[i]?, mainInst r with
  | some (.alias inst n), some m => if inst == m then some n else none
  | _, _ => none

def liftR (f : Nat) : Option LiftR :=
  match r.ff[f]? with
  | some (.lift cf opts) => do
    let core ← mainName r cf
    let cb ← match opts.findSome? (fun | .callback c => some c | _ => none) with
      | some c => (mainName r c).map some
      | none => pure none
    let pr ← match opts.findSome? (fun | .postReturn c => some c | _ => none) with
      | some c => (mainName r c).map some
      | none => pure none
    pure ⟨core, opts.contains .async_, cb, pr⟩
  | _ => none

def expR (si : Syntax.SortIdx Syntax.Sort_) : Option ExpR :=
  match si.sort with
  | .func => (liftR r si.idx).map .func
  | .instance_ => match r.ii[si.idx]? with
    | some (.inst _ args) =>
      let fs := args.filter fun (a : String × Syntax.SortIdx Syntax.Sort_) => a.2.sort == .func
      (fs.mapM fun (a : String × Syntax.SortIdx Syntax.Sort_) => (liftR r a.2.idx).map ((a.1, ·))).map .iface
    | _ => none
  | _ => none

/-- The arguments of core instance `m`, if it is an instantiation. -/
def argsAt (m : Nat) : Option (List (String × Nat)) :=
  match r.ci[m]? with
  | some (.inst _ args) => some args
  | _ => none

/-- The exports of core instance `i`, if it is an inline instance. -/
def expsAt (i : Nat) : Option (List (String × Syntax.SortIdx Syntax.CoreSort)) :=
  match r.ci[i]? with
  | some (.exps es) => some es
  | _ => none

/-- A core import `(mn, n)` of the main module, through the main instance's arguments. -/
def importR (args : List (String × Nat)) (p : String × String) :
    Option ((String × String) × CoreR) := do
  let inst ← lookupS p.1 args
  let es ← expsAt r inst
  let si ← lookupS p.2 es
  let c ← coreR r 4 si.idx
  pure (p, c)

/-- An export with its reading. -/
def exportR (e : String × Syntax.SortIdx Syntax.Sort_) : Option (String × ExpR) := do
  pure (e.1, ← expR r e.2)

/-- The resource definitions: type index and destructor. -/
def resources : List (Nat × Option Nat) :=
  r.tt.toList.zipIdx.filterMap fun (t, i) => match t with
    | .resource d => some (i, d)
    | _ => none

/-- A resource definition with its destructor resolved. -/
def dtorR (p : Nat × Option Nat) : Option (ResRef × Option CoreR) := do
  let rr ← resRef r p.1
  let dc ← match p.2 with
    | some c => (coreR r 4 c).map some
    | none => pure none
  pure (rr, dc)

/-- The reading of a set of index spaces. -/
def readRS (names : List (String × String)) : Option Reading := do
  let m ← mainInst r
  let args ← argsAt r m
  let imports ← names.mapM (importR r args)
  let exports ← r.exports.toList.mapM (exportR r)
  let dtors ← (resources r).mapM (dtorR r)
  pure ⟨exports, imports, dtors⟩

end

/-- **The reading of a reference component**: `readRS` of its index spaces, filled by the
reference's rule. -/
def readRef {M : Type} (names : List (String × String)) (c : Syntax.Component M) :
    Option Reading :=
  readRS (spacesRef c) names

end Silmaril.Wasm.JcoTool.LayoutRef

namespace Silmaril.Wasm.JcoTool.ToolV

open Silmaril.Wasm.JcoTool.Layout

/-- The output read as a reference component (core modules as bytes). -/
def refOf (o : Tool.Out) : Except String (Silmaril.Wasm.Component.Syntax.Component ByteArray) :=
  match xparse o.bytes with
  | .error _ => .error "the emitted component does not parse back"
  | .ok x => match LayoutRef.toRef some x with
    | some c => .ok c
    | none => .error "the emitted component is outside the translation to the reference syntax"

/-- Bytes read as a Core 3.0 reference component (`Reference.Core3Component`): `xparse`, then
`toRef` with silmaril's verified decoder for the core modules. -/
def refCore3 (b : ByteArray) : Except String Silmaril.Wasm.Component.Reference.Core3Component :=
  match xparse b with
  | .error _ => .error "the component does not parse (xparse)"
  | .ok x => match LayoutRef.toRef Silmaril.Wasm.Perf.CoreDecode.decodeF x with
    | some c => .ok c
    | none => .error "the component is outside the translation to the reference syntax (or a core module does not decode)"

/-- **The reference validator on bytes**: `Reference.check?` (sound: `Reference.check?_sound`)
with every feature gate on, on the bytes read as a Core 3.0 reference component. It runs as
`ValidateR.checkCore3R` (`checkCore3R_eq`), and the core modules are decoded with
`CoreDecode.decodeF` (`decodeF_eq`); `refCheck_valid` states the result for the specifications. -/
def refCheck (b : ByteArray) : Except String Silmaril.Wasm.Component.Reference.ComponentType := do
  let c ← refCore3 b
  match Silmaril.Wasm.Perf.ValidateR.checkCore3R Silmaril.Wasm.Component.Features.all c with
  | .ok ct => pure ct
  | .error e => throw s!"the reference validator rejects the component: {repr e}"

/-- The verdict line of `refCheck`. -/
def refCheckLine (b : ByteArray) : String :=
  match refCheck b with
  | .ok _ => "reference-valid: yes (the bytes, read as a reference Core3Component, pass Reference.check? with Features.all; LayoutRef.refCheck_valid)"
  | .error e => s!"reference-valid: no ({e})"

/-- **`wasm-jco new`** with the helpers and the layout checked, and the output translated to
the reference component syntax; the summary reports the reference validator's verdict. -/
def newFullR (core : ByteArray) (wf : Silmaril.Wasm.Wit.Binary.WorldFull) : Except String Tool.Out := do
  let o ← newFullL core wf
  let _ ← refOf o
  pure { o with summary := o.summary ++ (if ToolI.inOld wf.world then [] else
    ["reference: the output read as a reference component (Syntax.Component) has the layout the world describes, its index spaces filled by Definition.sort (LayoutRef.newFullR_correct)"]) ++
    [refCheckLine o.bytes] }

end Silmaril.Wasm.JcoTool.ToolV
