module

public import Silmaril.Wasm.SpecTec.Scripts.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: what SpecTec's `Step` can reach (pass 7)

The planned proof of `Round7.Task.swapEquiv` swaps each module record `m` of a configuration
with its stripped form `stripModule m` in every value of a SpecTec derivation. That swap commutes
with the evaluator only where no expression reads or writes a module record's export list, and
no record update goes through a module record. The planned proof of `Round7.Task.envAgreeNE`
needs `$utf8` to be called only from the type `name`. Both are facts about the part of the
fixed wasm-3.0 script that `Step` can reach. This header makes them computable:

* `Ev`: the events of an IL term that the facts are about: a reference to a relation (`0`), a
  definition (`1`), a syntax type (`2`) or a grammar (`3`); an expression-level atom (a record
  field `{A e}`, a projection `e.A`, a path step `.A`); a record composition `e₁ ++ e₂`; and a record
  update `e[p = e']` or `e[p =.. e']`, with its root and the atoms of its path. Atoms that
  declare a record *type* (`TypField`) are not events.
* `evExp`, …, `evDef`: the events of every IL syntax class, in one structural mutual block.
* `items s`: each top-level definition of `s` (recursive groups flattened), with its kind,
  name and events.
* `stepReach`: 430 names, computed outside Lean from `specs/spectec/wasm-3.0.ast` by a
  reference-closure from the relation `Step` (two of them, the definition parameter `$f_` and the
  type parameter `X`, are bound names, not top-level definitions). `Closed R s` says that every
  reference made by a definition of `s` named in `R` is in `R`; the kernel checks it for
  `stepReach` (`Round7.Script.stepReach_closed`), so the list needs no trust.

The facts themselves (one `evOk` per event: no `EXPORTS` atom, `$utf8` only from `utf8Allowed`,
composition only in `compAllowed`, updates only from `rootsAllowed` and without `atomsBanned`)
are proved in `Proofs/…/Round7/Script/Assemble.lean` and summarised in `Round7/Script/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

/-! ## Events -/

/-- An event of an IL term. -/
inductive Ev where
  /-- A reference to a relation (`0`), definition (`1`), syntax type (`2`) or grammar (`3`). -/
  | ref (k : Nat) (x : String)
  /-- An atom used by an expression: a record field, a projection or a path step. -/
  | atom (a : String)
  /-- A record (or list) composition `e₁ ++ e₂`. -/
  | comp
  /-- A record update, with its root and the atoms of its path. -/
  | upd (root : Exp) (atoms : List String)

/-- The atoms of a path, outermost last. -/
def pathAtoms : Path → List String
  | .rootP => []
  | .idxP p _ => pathAtoms p
  | .sliceP p _ _ => pathAtoms p
  | .dotP p a => pathAtoms p ++ [a]

mutual
/-- Events of an iteration. -/
def evIter : Iter → List Ev
  | .listN e _ => evExp e
  | _ => []

/-- Events of a type. -/
def evTyp : Typ → List Ev
  | .varT x args => .ref 2 x :: evArgs args
  | .tupT bs => evBinds bs
  | .iterT t it => evTyp t ++ evIter it
  | _ => []

/-- Events of tuple binders. -/
def evBinds : List TypBind → List Ev
  | [] => []
  | .mk _ t :: bs => evTyp t ++ evBinds bs

/-- Events of a type definition's body. -/
def evDefTyp : DefTyp → List Ev
  | .aliasT t => evTyp t
  | .structT fs => evTFields fs
  | .variantT cs => evTCases cs

/-- Events of record type fields; the declared atoms are not events. -/
def evTFields : List TypField → List Ev
  | [] => []
  | .mk _ t qs prems :: fs => evTyp t ++ evParams qs ++ evPrems prems ++ evTFields fs

/-- Events of variant cases. -/
def evTCases : List TypCase → List Ev
  | [] => []
  | .mk _ t qs prems :: cs => evTyp t ++ evParams qs ++ evPrems prems ++ evTCases cs

/-- Events of an expression. -/
def evExp : Exp → List Ev
  | .unE _ _ e => evExp e
  | .binE _ _ e₁ e₂ => evExp e₁ ++ evExp e₂
  | .cmpE _ _ e₁ e₂ => evExp e₁ ++ evExp e₂
  | .tupE es => evExps es
  | .projE e _ => evExp e
  | .caseE _ e => evExp e
  | .uncaseE e _ => evExp e
  | .optE eo => evOExp eo
  | .theE e => evExp e
  | .strE fs => evEFields fs
  | .dotE e a => .atom a :: evExp e
  | .compE e₁ e₂ => .comp :: (evExp e₁ ++ evExp e₂)
  | .listE es => evExps es
  | .liftE e => evExp e
  | .memE e₁ e₂ => evExp e₁ ++ evExp e₂
  | .lenE e => evExp e
  | .catE e₁ e₂ => evExp e₁ ++ evExp e₂
  | .idxE e₁ e₂ => evExp e₁ ++ evExp e₂
  | .sliceE e₁ e₂ e₃ => evExp e₁ ++ evExp e₂ ++ evExp e₃
  | .updE e₁ p e₂ => .upd e₁ (pathAtoms p) :: (evExp e₁ ++ evPath p ++ evExp e₂)
  | .extE e₁ p e₂ => .upd e₁ (pathAtoms p) :: (evExp e₁ ++ evPath p ++ evExp e₂)
  | .callE x args => .ref 1 x :: evArgs args
  | .iterE e it => evExp e ++ evIterExp it
  | .cvtE e _ _ => evExp e
  | .subE e t₁ t₂ => evExp e ++ evTyp t₁ ++ evTyp t₂
  | _ => []

/-- Events of a list of expressions. -/
def evExps : List Exp → List Ev
  | [] => []
  | e :: es => evExp e ++ evExps es

/-- Events of an optional expression. -/
def evOExp : Option Exp → List Ev
  | none => []
  | some e => evExp e

/-- Events of record fields: each field's atom, then its expression. -/
def evEFields : List ExpField → List Ev
  | [] => []
  | .mk a e :: fs => .atom a :: (evExp e ++ evEFields fs)

/-- Events of a path: each `.A` step is an atom event. -/
def evPath : Path → List Ev
  | .rootP => []
  | .idxP p e => evPath p ++ evExp e
  | .sliceP p e₁ e₂ => evPath p ++ evExp e₁ ++ evExp e₂
  | .dotP p a => .atom a :: evPath p

/-- Events of an iteration with its domains. -/
def evIterExp : IterExp → List Ev
  | .mk it ds => evIter it ++ evDoms ds

/-- Events of iteration domains. -/
def evDoms : List Dom → List Ev
  | [] => []
  | .mk _ e :: ds => evExp e ++ evDoms ds

/-- Events of a grammar symbol. -/
def evSym : Sym → List Ev
  | .varG x args => .ref 3 x :: evArgs args
  | .seqG gs => evSyms gs
  | .altG gs => evSyms gs
  | .rangeG g₁ g₂ => evSym g₁ ++ evSym g₂
  | .iterG g it => evSym g ++ evIterExp it
  | .attrG e g => evExp e ++ evSym g
  | _ => []

/-- Events of a list of symbols. -/
def evSyms : List Sym → List Ev
  | [] => []
  | g :: gs => evSym g ++ evSyms gs

/-- Events of an argument; `def x` refers to the definition `x`. -/
def evArg : Arg → List Ev
  | .expA e => evExp e
  | .typA t => evTyp t
  | .defA x => [.ref 1 x]
  | .gramA g => evSym g

/-- Events of a list of arguments. -/
def evArgs : List Arg → List Ev
  | [] => []
  | a :: rest => evArg a ++ evArgs rest

/-- Events of a parameter or quantifier: its type. -/
def evParam : Param → List Ev
  | .expP _ t => evTyp t
  | .typP _ => []
  | .defP _ ps t => evParams ps ++ evTyp t
  | .gramP _ ps t => evParams ps ++ evTyp t

/-- Events of a list of parameters. -/
def evParams : List Param → List Ev
  | [] => []
  | p :: ps => evParam p ++ evParams ps

/-- Events of a premise; a rule premise refers to its relation. -/
def evPrem : Prem → List Ev
  | .rulePr x args _ e => .ref 0 x :: (evArgs args ++ evExp e)
  | .ifPr e => evExp e
  | .letPr e₁ e₂ => evExp e₁ ++ evExp e₂
  | .elsePr => []
  | .iterPr pr it => evPrem pr ++ evIterExp it

/-- Events of a list of premises. -/
def evPrems : List Prem → List Ev
  | [] => []
  | p :: ps => evPrem p ++ evPrems ps
end

/-- Events of a type family instance. -/
def evInst : Inst → List Ev
  | .instD qs args dt => evParams qs ++ evArgs args ++ evDefTyp dt

/-- Events of a relation's rule. -/
def evRule : Rule → List Ev
  | .ruleD _ qs _ e prems => evParams qs ++ evExp e ++ evPrems prems

/-- Events of a definition's clause. -/
def evClause : Clause → List Ev
  | .defD qs args e prems => evParams qs ++ evArgs args ++ evExp e ++ evPrems prems

/-- Events of a grammar production. -/
def evProd : IL.Prod → List Ev
  | .prodD qs g e prems => evParams qs ++ evSym g ++ evExp e ++ evPrems prems

/-! ## Top-level items -/

/-- A top-level definition: its kind (`0` relation, `1` definition, `2` type, `3` grammar), its
name and its events. -/
abbrev Item := Nat × String × List Ev

mutual
/-- The items of a top-level definition; a recursive group gives those of its members. -/
def defItems : Def → List Item
  | .typD x ps insts => [(2, x, evParams ps ++ insts.flatMap evInst)]
  | .relD x ps _ t rules => [(0, x, evParams ps ++ evTyp t ++ rules.flatMap evRule)]
  | .decD x ps t cls => [(1, x, evParams ps ++ evTyp t ++ cls.flatMap evClause)]
  | .gramD x ps t prods => [(3, x, evParams ps ++ evTyp t ++ prods.flatMap evProd)]
  | .recD ds => defsItems ds

/-- `defItems` on a list. -/
def defsItems : List Def → List Item
  | [] => []
  | d :: ds => defItems d ++ defsItems ds
end

/-- The items of a script. -/
def items (s : Script) : List Item := defsItems s

/-! ## Closure -/

/-- The references among a list of events. -/
def evRefs : List Ev → List (Nat × String)
  | [] => []
  | .ref k x :: evs => (k, x) :: evRefs evs
  | _ :: evs => evRefs evs

/-- **`R` is closed in `s`**: every reference made by an item of `s` named in `R` is in `R`. -/
def closedB (R : List (Nat × String)) (s : Script) : Bool :=
  (items s).all fun it => !(R.contains (it.1, it.2.1)) || (evRefs it.2.2).all R.contains

/-- The items of `s` named in `R`. -/
def itemsIn (R : List (Nat × String)) (s : Script) : List Item :=
  (items s).filter fun it => R.contains (it.1, it.2.1)

/-! ## The facts, as computations -/

/-- The items of `s` named in `R` whose events include the atom `a`. -/
def atomUsers (a : String) (R : List (Nat × String)) (s : Script) : List (Nat × String) :=
  (itemsIn R s).filterMap fun it =>
    if it.2.2.any (fun e => match e with | .atom b => b == a | _ => false) then some (it.1, it.2.1)
    else none

/-- The items of `s` named in `R` that refer to the definition `x`. -/
def defUsers (x : String) (R : List (Nat × String)) (s : Script) : List (Nat × String) :=
  (itemsIn R s).filterMap fun it =>
    if (evRefs it.2.2).contains (1, x) then some (it.1, it.2.1) else none

/-- The items of `s` named in `R` that compose records or lists (`e₁ ++ e₂`). -/
def compSites (R : List (Nat × String)) (s : Script) : List (Nat × String) :=
  (itemsIn R s).filterMap fun it =>
    if it.2.2.any (fun e => match e with | .comp => true | _ => false) then some (it.1, it.2.1)
    else none

/-- The head of an update's root: the definition it calls, or `"?"`. -/
def rootHead : Exp → String
  | .callE x _ => x
  | _ => "?"

/-- The record updates of the items of `s` named in `R`: the item, the root's head and the
path's atoms. -/
def updSites (R : List (Nat × String)) (s : Script) :
    List (Nat × String × String × List String) :=
  (itemsIn R s).flatMap fun it => it.2.2.filterMap fun e => match e with
    | .upd r ats => some (it.1, it.2.1, rootHead r, ats)
    | _ => none


/-- The type `x` is declared (at top level) as a record with a field `a`. Atoms of declared
fields are not events; this is how a witness sees them. -/
def declaresField (x a : String) : Def → Bool
  | .typD y _ insts => y == x && insts.any fun i => match i with
    | .instD _ _ (.structT fs) => fs.any fun f => match f with | .mk b _ _ _ => b == a
    | _ => false
  | _ => false

/-! ## One pass over a script -/

/-- The definitions allowed to call `$utf8`: `$utf8` itself and the type `name`. -/
def utf8Allowed : List (Nat × String) := [(1, "utf8"), (2, "name")]

/-- The items allowed to compose records or lists: the relation `Deftype_ok`. -/
def compAllowed : List (Nat × String) := [(0, "Deftype_ok")]

/-- The definitions an update may start from: `$sof` (a state's store), `$fof` (a state's frame)
and `$lanes_` (a vector's lanes). -/
def rootsAllowed : List String := ["sof", "fof", "lanes_"]

/-- The atoms no update path may contain: those of a module instance's own fields that a store or
a frame also has (`MODULE`, `FUNCS`) and `EXPORTS`. -/
def atomsBanned : List String := ["MODULE", "FUNCS", "EXPORTS"]

/-- **One event is harmless** for the item named `n`: it uses no `EXPORTS` atom, it calls
`$utf8` only if `n` is allowed to, it composes only if `n` is allowed to, and every update starts
from an allowed root along a path without a banned atom. -/
def evOk (n : Nat × String) : Ev → Bool
  | .ref k x => !(k == 1 && x == "utf8") || utf8Allowed.contains n
  | .atom a => a != "EXPORTS"
  | .comp => compAllowed.contains n
  | .upd r ats => rootsAllowed.contains (rootHead r) && ats.all fun a => !atomsBanned.contains a

/-- **One item is closed in `R` and harmless**: its references are in `R` and each of its
events is `evOk`. -/
def itemOk (R : List (Nat × String)) (it : Item) : Bool :=
  (evRefs it.2.2).all R.contains && it.2.2.all (evOk (it.1, it.2.1))

/-- **Every item of `s` named in `R` is closed in `R` and harmless.** -/
def scriptOk (R : List (Nat × String)) (s : Script) : Bool :=
  (items s).all fun it => !(R.contains (it.1, it.2.1)) || itemOk R it

/-! ## The closure of `Step` -/

/-- **The names `Step` can reach** in the fixed wasm-3.0 script, by kind: relations (`0`),
definitions (`1`), syntax types (`2`). Computed outside Lean by a reference closure over
`specs/spectec/wasm-3.0.ast`; `Round7.Script.stepReach_closed` checks it in the kernel. -/
def stepReach : List (Nat × String) :=
  [(0, "Comptype_ok"), (0, "Comptype_sub"), (0, "Deftype_ok"), (0, "Deftype_sub"), (0, "Expand"),
   (0, "Fieldtype_ok"), (0, "Fieldtype_sub"), (0, "Heaptype_ok"), (0, "Heaptype_sub"),
   (0, "Numtype_ok"), (0, "Numtype_sub"), (0, "Packtype_ok"), (0, "Packtype_sub"),
   (0, "Rectype_ok2"), (0, "Ref_ok"), (0, "Reftype_ok"), (0, "Reftype_sub"), (0, "Resulttype_ok"),
   (0, "Resulttype_sub"), (0, "Step"), (0, "Step_pure"), (0, "Step_read"), (0, "Storagetype_ok"),
   (0, "Storagetype_sub"), (0, "Subtype_ok2"), (0, "Typeuse_ok"), (0, "Valtype_ok"),
   (0, "Valtype_sub"), (0, "Vectype_ok"), (0, "Vectype_sub"), (1, "E"), (1, "Ki"), (1, "M"),
   (1, "ND"), (1, "R_idot"), (1, "R_swizzle"), (1, "add_arrayinst"), (1, "add_exninst"),
   (1, "add_structinst"), (1, "arrayinst"), (1, "as_deftype"), (1, "before"), (1, "binop_"),
   (1, "blocktype_"), (1, "bool"), (1, "clos_deftype"), (1, "clos_deftypes"), (1, "concat_"),
   (1, "concatn_"), (1, "const"), (1, "cont"), (1, "convert__"), (1, "cunpack"),
   (1, "cunpacknum_"), (1, "cvtop__"), (1, "data"), (1, "default_"), (1, "demote__"), (1, "dim"),
   (1, "elem"), (1, "exninst"), (1, "expon"), (1, "extend__"), (1, "f_"), (1, "fabs_"),
   (1, "fadd_"), (1, "fceil_"), (1, "fcopysign_"), (1, "fdiv_"), (1, "feq_"), (1, "ffloor_"),
   (1, "fge_"), (1, "fgt_"), (1, "fle_"), (1, "flt_"), (1, "fmax_"), (1, "fmin_"), (1, "fmul_"),
   (1, "fne_"), (1, "fnearest_"), (1, "fneg_"), (1, "fof"), (1, "fpmax_"), (1, "fpmin_"),
   (1, "frame"), (1, "frelaxed_madd_"), (1, "frelaxed_max_"), (1, "frelaxed_min_"),
   (1, "frelaxed_nmadd_"), (1, "fsize"), (1, "fsqrt_"), (1, "fsub_"), (1, "ftrunc_"),
   (1, "funcinst"), (1, "fvbinop_"), (1, "fvrelop_"), (1, "fvternop_"), (1, "fvunop_"),
   (1, "fzero"), (1, "global"), (1, "growmem"), (1, "growtable"), (1, "half"), (1, "halfop"),
   (1, "hostcall"), (1, "iabs_"), (1, "iadd_"), (1, "iadd_sat_"), (1, "iand_"), (1, "iandnot_"),
   (1, "iavgr_"), (1, "ibits_"), (1, "ibitselect_"), (1, "ibytes_"), (1, "iclz_"), (1, "ictz_"),
   (1, "idiv_"), (1, "ieq_"), (1, "ieqz_"), (1, "iextend_"), (1, "ige_"), (1, "igt_"),
   (1, "ile_"), (1, "ilt_"), (1, "imax_"), (1, "imin_"), (1, "imul_"), (1, "ine_"), (1, "ineg_"),
   (1, "inez_"), (1, "inot_"), (1, "inst_reftype"), (1, "inv_lanes_"), (1, "inv_signed_"),
   (1, "ior_"), (1, "ipopcnt_"), (1, "iq15mulr_sat_"), (1, "irelaxed_laneselect_"),
   (1, "irelaxed_q15mulr_"), (1, "irelaxed_swizzle_lane_"), (1, "irem_"), (1, "irev_"),
   (1, "irotl_"), (1, "irotr_"), (1, "ishl_"), (1, "ishr_"), (1, "isize"), (1, "isub_"),
   (1, "isub_sat_"), (1, "iswizzle_lane_"), (1, "ivadd_pairwise_"), (1, "ivbinop_"),
   (1, "ivbinopsx_"), (1, "ivbinopsxnd_"), (1, "ivbitmaskop_"), (1, "ivdot_"), (1, "ivdot_sat_"),
   (1, "ivextbinop__"), (1, "ivextunop__"), (1, "ivmul_"), (1, "ivrelop_"), (1, "ivrelopsx_"),
   (1, "ivshiftop_"), (1, "ivshiftopsx_"), (1, "ivshufflop_"), (1, "ivswizzlop_"),
   (1, "ivternopnd_"), (1, "ivunop_"), (1, "ixor_"), (1, "jsize"), (1, "jsizenn"), (1, "lanes_"),
   (1, "lanetype"), (1, "lcvtop__"), (1, "lift_result"), (1, "local"), (1, "lpacknum_"),
   (1, "lsize"), (1, "lsizenn"), (1, "lsizenn1"), (1, "lsizenn2"), (1, "lunpack"), (1, "mem"),
   (1, "memarg0"), (1, "minus_recs"), (1, "moduleinst"), (1, "narrow__"), (1, "nbytes_"),
   (1, "packfield_"), (1, "prod"), (1, "promote__"), (1, "psize"), (1, "psizenn"),
   (1, "reinterpret__"), (1, "relaxed2"), (1, "relaxed_trunc__"), (1, "relop_"), (1, "sat_s_"),
   (1, "sat_u_"), (1, "setproduct1_"), (1, "setproduct2_"), (1, "setproduct_"), (1, "signed_"),
   (1, "signif"), (1, "size"), (1, "sizenn"), (1, "sizenn1"), (1, "sizenn2"), (1, "sof"),
   (1, "store"), (1, "structinst"), (1, "subst_all_deftype"), (1, "subst_all_reftype"),
   (1, "subst_comptype"), (1, "subst_deftype"), (1, "subst_fieldtype"), (1, "subst_heaptype"),
   (1, "subst_numtype"), (1, "subst_packtype"), (1, "subst_rectype"), (1, "subst_reftype"),
   (1, "subst_storagetype"), (1, "subst_subtype"), (1, "subst_typeuse"), (1, "subst_typevar"),
   (1, "subst_valtype"), (1, "subst_vectype"), (1, "sx"), (1, "table"), (1, "tag"),
   (1, "tagaddr"), (1, "testop_"), (1, "trunc__"), (1, "trunc_sat__"), (1, "truncz"), (1, "type"),
   (1, "unop_"), (1, "unpack"), (1, "unpackfield_"), (1, "unrolldt"), (1, "unrollht_"),
   (1, "unrollrt"), (1, "utf8"), (1, "vbinop_"), (1, "vbitmaskop_"), (1, "vbytes_"),
   (1, "vcvtop__"), (1, "vextbinop__"), (1, "vextternop__"), (1, "vextunop__"),
   (1, "vnarrowop__"), (1, "vrelop_"), (1, "vshiftop_"), (1, "vshufflop_"), (1, "vsize"),
   (1, "vsizenn"), (1, "vswizzlop_"), (1, "vternop_"), (1, "vunop_"), (1, "vvbinop_"),
   (1, "vvternop_"), (1, "vvunop_"), (1, "with_array"), (1, "with_data"), (1, "with_elem"),
   (1, "with_global"), (1, "with_local"), (1, "with_mem"), (1, "with_meminst"),
   (1, "with_struct"), (1, "with_table"), (1, "with_tableinst"), (1, "wrap__"), (1, "zbytes_"),
   (1, "zero"), (1, "zeroop"), (1, "zsize"), (2, "Fnn"), (2, "Inn"), (2, "Jnn"), (2, "K"),
   (2, "Lnn"), (2, "M"), (2, "N"), (2, "Pnn"), (2, "Vnn"), (2, "X"), (2, "absheaptype"),
   (2, "addr"), (2, "addrtype"), (2, "arrayaddr"), (2, "arrayinst"), (2, "binop_"), (2, "bit"),
   (2, "blocktype"), (2, "bshape"), (2, "byte"), (2, "catch"), (2, "char"), (2, "comptype"),
   (2, "config"), (2, "consttype"), (2, "context"), (2, "cvtop__"), (2, "dataaddr"),
   (2, "dataidx"), (2, "datainst"), (2, "datatype"), (2, "deftype"), (2, "dim"), (2, "elemaddr"),
   (2, "elemidx"), (2, "eleminst"), (2, "elemtype"), (2, "exnaddr"), (2, "exninst"), (2, "exp"),
   (2, "exportinst"), (2, "expr"), (2, "externaddr"), (2, "fN"), (2, "fNmag"), (2, "fieldidx"),
   (2, "fieldtype"), (2, "fieldval"), (2, "final"), (2, "frame"), (2, "funcaddr"),
   (2, "funccode"), (2, "funcidx"), (2, "funcinst"), (2, "globaladdr"), (2, "globalidx"),
   (2, "globalinst"), (2, "globaltype"), (2, "half"), (2, "heaptype"), (2, "hostaddr"),
   (2, "hostcallresult"), (2, "hostfunc"), (2, "iN"), (2, "idx"), (2, "init"), (2, "instr"),
   (2, "instrtype"), (2, "ishape"), (2, "labelidx"), (2, "lane_"), (2, "laneidx"),
   (2, "lanetype"), (2, "limits"), (2, "list"), (2, "lit_"), (2, "loadop_"), (2, "local"),
   (2, "localidx"), (2, "localtype"), (2, "m"), (2, "memaddr"), (2, "memarg"), (2, "memidx"),
   (2, "meminst"), (2, "memtype"), (2, "moduleinst"), (2, "mut"), (2, "n"), (2, "name"),
   (2, "null"), (2, "num_"), (2, "numtype"), (2, "oktypenat"), (2, "pack_"), (2, "packtype"),
   (2, "rectype"), (2, "ref"), (2, "reftype"), (2, "relaxed2"), (2, "relop_"), (2, "result"),
   (2, "resulttype"), (2, "shape"), (2, "state"), (2, "storagetype"), (2, "store"),
   (2, "storeop_"), (2, "structaddr"), (2, "structinst"), (2, "subtype"), (2, "sx"), (2, "sz"),
   (2, "tableaddr"), (2, "tableidx"), (2, "tableinst"), (2, "tabletype"), (2, "tagaddr"),
   (2, "tagidx"), (2, "taginst"), (2, "tagtype"), (2, "testop_"), (2, "typeidx"), (2, "typeuse"),
   (2, "typevar"), (2, "u31"), (2, "u32"), (2, "u64"), (2, "u8"), (2, "uN"), (2, "unop_"),
   (2, "vN"), (2, "val"), (2, "valtype"), (2, "vbinop_"), (2, "vcvtop__"), (2, "vec_"),
   (2, "vectype"), (2, "vextbinop__"), (2, "vextternop__"), (2, "vextunop__"), (2, "vloadop_"),
   (2, "vrelop_"), (2, "vshiftop_"), (2, "vswizzlop_"), (2, "vternop_"), (2, "vtestop_"),
   (2, "vunop_"), (2, "vvbinop"), (2, "vvternop"), (2, "vvtestop"), (2, "vvunop"), (2, "zero")]

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
