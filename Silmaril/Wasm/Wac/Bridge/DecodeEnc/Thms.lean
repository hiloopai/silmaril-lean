module

public import Silmaril.Wasm.Wac.Bridge.Decode.Defs

/-!
# WAC bridge: decoding inverts the encoding of kinds (functions over primitives)

The encoder writes a package's kinds as a component type (`Bridge.Encode`:
`importDecls`, `exportDecls`, sharing equal function types with `share := true`, as for
the component types of packages); the decoder reads a component type back as a package
(`Bridge.Decode`: `decCDecls`, `pkgOfWorld`, the core of `decodePkg`). This module proves
`decode ∘ encode = id` for packages whose imports and exports are functions over
primitive value types (`PrimFns`):

* `decode_encode`: encoding the imports `is` and exports `es` gives declarations that
  `pkgOfWorld` reads back as `{ imports := is, exports := es }`, with no nominal
  definitions.

The proof is a lock-step simulation: `Match σ δ` relates the encoder's type scope (type
count, cache of function types) to the decoder's (its type index space); each function
type the encoder defines is decoded to the same signature (`dec_functype`), and each
import or export reads its function type back at the index the encoder used, shared or
not (`imports_run`, `exports_run`).

**Not covered.** Value types other than primitives (the encoder's caches of anonymous
value types and handles, named types and nominal definitions), type items, resources,
instance and component items. The byte level (`Component.Binary.parse`,
`Wit.Project.projectI`) of `decodePkg` is not part of the statement.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)

namespace DecodeEnc

/-! ## The fragment -/

/-- A primitive value type. -/
def PrimTy (t : Ty) : Prop := ∃ p, t = .prim p

/-- A function type over primitive value types. -/
def PrimSig (s : Sig) : Prop := (∀ p ∈ s.params, PrimTy p.2) ∧ ∀ t ∈ s.result, PrimTy t

/-- Named functions over primitive value types. -/
def PrimFns (es : Externs) : Prop := ∀ p ∈ es, ∃ s, p.2 = .func s ∧ PrimSig s

/-- The encoding of a primitive value type. -/
def vt : Ty → Silmaril.Wasm.Component.Binary.ValType
  | .prim p => .prim p
  | _ => .idx 0

/-- The function type the encoder defines for a signature over primitives. -/
def ft (s : Sig) : Silmaril.Wasm.Component.Binary.FuncType := ⟨s.params.map (fun p => (p.1, vt p.2)), s.result.map vt, s.async⟩

/-! ## The `Except` monad -/

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

attribute [local simp] ok_bind pure_ok Except.map_ok

/-! ## The encoder -/

theorem paramTys_run (σ : Scope) : ∀ (ps : List (String × Ty)), (∀ p ∈ ps, PrimTy p.2) →
    (paramTys ps).run σ = .ok (ps.map (fun p => (p.1, vt p.2)), σ)
  | [], _ => rfl
  | (n, t) :: ps, h => by
    obtain ⟨q, e⟩ : PrimTy t := h (n, t) List.mem_cons_self
    have ih := paramTys_run σ ps fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [e]
    simp [paramTys, valTy, vt, ih]

theorem valTyOpt_run (σ : Scope) : ∀ (r : Option Ty), (∀ t ∈ r, PrimTy t) →
    (valTyOpt r).run σ = .ok (r.map vt, σ)
  | none, _ => rfl
  | some t, h => by
    obtain ⟨q, e⟩ := h t rfl
    rw [e]
    simp [valTyOpt, valTy, vt]

/-- The scope after defining the function type of `s`. -/
def defFn (σ : Scope) (s : Sig) : Scope :=
  { σ with decls := σ.decls ++ [.inst (.type (.func (ft s)))], ntypes := σ.ntypes + 1,
           fcache := σ.fcache ++ [(s, σ.ntypes)] }

/-- **The function type of a signature over primitives**: shared (an equal one is
cached) or defined at the next index. -/
theorem funcTy_run {s : Sig} (hs : PrimSig s) (σ : Scope) :
    (∃ j, σ.fcache.lookup s = some j ∧ (funcTy s).run σ = .ok (j, σ)) ∨
      (funcTy s).run σ = .ok (σ.ntypes, defFn σ s) := by
  cases hsh : σ.share <;> cases hl : σ.fcache.lookup s
  case true.some j => exact Or.inl ⟨j, rfl, by simp [funcTy, hsh, hl]⟩
  all_goals exact Or.inr (by
    simp [funcTy, hsh, hl, paramTys_run σ s.params hs.1, valTyOpt_run σ s.result hs.2, defTy, defFn, ft])

/-! ## The decoder -/

theorem typeAt_run {δ : DScope} {i : Nat} {t : TInfo} (h : δ.types[i]? = some t) :
    (typeAt i).run δ = .ok (t, δ) := by
  simp [typeAt, h]

theorem mapM_run {g : String × Silmaril.Wasm.Component.Binary.ValType → DM (String × Ty)} {δ : DScope} :
    ∀ (ps : List (String × Ty)), (∀ p ∈ ps, (g (p.1, vt p.2)).run δ = .ok (p, δ)) →
      (List.mapM g (ps.map fun p => (p.1, vt p.2))).run δ = .ok (ps, δ)
  | [], _ => rfl
  | p :: ps, h => by
    have h1 : (g (p.1, vt p.2)).run δ = .ok (p, δ) := h p List.mem_cons_self
    have ih := mapM_run ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [List.map_cons, List.mapM_cons]
    simp only [StateT.run_bind, h1, ok_bind, ih]
    rfl

theorem decFunc_ft {s : Sig} (hs : PrimSig s) (δ : DScope) : (decFunc (ft s)).run δ = .ok (s, δ) := by
  have hp : (List.mapM (fun p : String × Silmaril.Wasm.Component.Binary.ValType => do let x ← decVal p.2; pure (p.1, x))
      ((ft s).params)).run δ = .ok (s.params, δ) :=
    mapM_run s.params fun p hp' => by
      obtain ⟨q, e⟩ : PrimTy p.2 := hs.1 p hp'
      rw [e]; simp only [vt, decVal, pure_bind, StateT.run_pure, pure_ok]; rw [← e]
  have hr : (decValOpt (ft s).result).run δ = .ok (s.result, δ) := by
    cases hres : s.result with
    | none => simp [ft, hres, decValOpt]
    | some t =>
      obtain ⟨q, e⟩ : PrimTy t := hs.2 t hres
      simp [ft, hres, e, decValOpt, decVal, vt]
  unfold decFunc
  simp only [StateT.run_bind, hp, hr, ok_bind, StateT.run_pure, pure_ok]
  rfl

theorem dec_functype {s : Sig} (hs : PrimSig s) (δ : DScope) (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.inst (.type (.func (ft s))) :: rest) is es).run δ =
      (decCDecls rest is es).run { δ with types := δ.types.push (.func s) } := by
  simp [decCDecls, decIDecl, decDefType, pushTy, decFunc_ft hs]

theorem dec_import {δ : DScope} {j : Nat} {s : Sig} (h : δ.types[j]? = some (.func s)) (n : String)
    (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.import ⟨n, .plain0⟩ (.func j) :: rest) is es).run δ =
      (decCDecls rest (is ++ [(n, .func s)]) es).run δ := by
  simp [decCDecls, decExtern, typeAt_run h]

theorem dec_export {δ : DScope} {j : Nat} {s : Sig} (h : δ.types[j]? = some (.func s)) (n : String)
    (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.inst (.export ⟨n, .plain0⟩ (.func j)) :: rest) is es).run δ =
      (decCDecls rest is (es ++ [(n, .func s)])).run δ := by
  simp [decCDecls, decIDecl, decExtern, typeAt_run h]

/-! ## The simulation -/

/-- The encoder's and the decoder's type scopes agree: as many types, and every cached
function type is decoded at its index. -/
structure Match (σ : Scope) (δ : DScope) : Prop where
  size : δ.types.size = σ.ntypes
  fc : ∀ s j, (s, j) ∈ σ.fcache → δ.types[j]? = some (.func s)

theorem mem_of_lookup {s : Sig} {j : Nat} : ∀ {l : List (Sig × Nat)}, l.lookup s = some j → (s, j) ∈ l
  | [], h => absurd h (by simp)
  | (s', j') :: l, h => by
    by_cases e : s = s'
    · have hb : (s == s') = true := beq_iff_eq.2 e
      have hj : j' = j := by simpa [List.lookup, hb] using h
      rw [e, hj]; exact List.mem_cons_self
    · have hb : (s == s') = false := beq_false_of_ne e
      have h' : l.lookup s = some j := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookup h')

theorem match_defFn {σ : Scope} {δ : DScope} (hm : Match σ δ) (s : Sig) :
    Match (defFn σ s) { δ with types := δ.types.push (.func s) } := by
  constructor
  · simp [defFn, hm.size]
  · intro s' j hj
    rcases List.mem_append.1 hj with hj | hj
    · have h0 : δ.types[j]? = some (.func s') := hm.fc s' j hj
      have hlt : j < δ.types.size := (Array.getElem?_eq_some_iff.1 h0).1
      simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using h0
    · have e : (s', j) = (s, σ.ntypes) := List.mem_singleton.1 hj
      rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2, ← hm.size]
      simp

/-- The decoder reads `E ++ rest` as `rest` with the imports `xs` added, ending in `δ'`. -/
def ReadsI (xs : Externs) (E : List ComponentDecl) (δ δ' : DScope) : Prop :=
  ∀ rest is es, (decCDecls (E ++ rest) is es).run δ = (decCDecls rest (is ++ xs) es).run δ'

/-- The decoder reads `E ++ rest` as `rest` with the exports `xs` added, ending in `δ'`. -/
def ReadsE (xs : Externs) (E : List ComponentDecl) (δ δ' : DScope) : Prop :=
  ∀ rest is es, (decCDecls (E ++ rest) is es).run δ = (decCDecls rest is (es ++ xs)).run δ'

/-- What encoding items does: ok, emitting `E`, keeping `Match`, `share` and the
decoder's nominal table, and the decoder reads `E` as `Rd` says. -/
def Sim (Rd : List ComponentDecl → DScope → DScope → Prop) (m : TM Unit) (σ : Scope) (δ : DScope) : Prop :=
  ∃ σ' E δ', m.run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧ Match σ' δ' ∧
    σ'.share = σ.share ∧ δ'.nom = δ.nom ∧ Rd E δ δ'

theorem importDecls_cons (n : String) (s : Sig) (es : Externs) (σ : Scope) :
    (importDecls ((n, .func s) :: es)).run σ = ((funcTy s).run σ).bind fun p =>
      (importDecls es).run { p.2 with decls := p.2.decls ++ [.import ⟨n, .plain0⟩ (.func p.1)] } := by
  simp [importDecls, externDesc, declared]
  rfl

theorem exportDecls_cons (n : String) (s : Sig) (es : Externs) (σ : Scope) :
    (exportDecls ((n, .func s) :: es)).run σ = ((funcTy s).run σ).bind fun p =>
      (exportDecls es).run { p.2 with decls := p.2.decls ++ [.inst (.export ⟨n, .plain0⟩ (.func p.1))] } := by
  simp [exportDecls, externDesc, declared]
  rfl

theorem imports_run : ∀ (is : Externs), PrimFns is → ∀ σ δ, Match σ δ → Sim (ReadsI is) (importDecls is) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl, fun rest is es => by simp [List.append_nil]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    obtain ⟨s, hk, hs⟩ : ∃ s, k = .func s ∧ PrimSig s := h (n, k) List.mem_cons_self
    have hxs : PrimFns xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [hk]
    rcases funcTy_run hs σ with ⟨j, hl, hf⟩ | hf
    · -- shared: only the import is emitted
      let σ2 : Scope := { σ with decls := σ.decls ++ [.import ⟨n, .plain0⟩ (.func j)] }
      have hm2 : Match σ2 δ := ⟨hm.size, hm.fc⟩
      obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads⟩ := imports_run xs hxs σ2 δ hm2
      refine ⟨σ', .import ⟨n, .plain0⟩ (.func j) :: E, δ', ?_, ?_, hm', hsh, hn, ?_⟩
      · rw [importDecls_cons, hf]; exact hr
      · rw [hd]; simp [σ2]
      · intro rest is es
        rw [List.cons_append, dec_import (hm.fc s j (mem_of_lookup hl)) n, hreads]
        simp
    · -- defined at the next index, then imported
      let σ1 := defFn σ s
      let δ1 : DScope := { δ with types := δ.types.push (.func s) }
      let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ (.func σ.ntypes)] }
      have hm1 : Match σ1 δ1 := match_defFn hm s
      have hm2 : Match σ2 δ1 := ⟨hm1.size, hm1.fc⟩
      have hat : δ1.types[σ.ntypes]? = some (.func s) := by rw [← hm.size]; simp [δ1]
      obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads⟩ := imports_run xs hxs σ2 δ1 hm2
      refine ⟨σ', .inst (.type (.func (ft s))) :: .import ⟨n, .plain0⟩ (.func σ.ntypes) :: E, δ', ?_, ?_,
        hm', hsh, hn, ?_⟩
      · rw [importDecls_cons, hf]; exact hr
      · rw [hd]; simp [σ2, σ1, defFn]
      · intro rest is es
        rw [List.cons_append, List.cons_append, dec_functype hs, dec_import hat n, hreads]
        simp

/-- Declarations that are all instance declarations (what may sit in an instance type). -/
def InstOnly (E : List ComponentDecl) : Prop := ∀ d ∈ E, ∃ x, d = .inst x

theorem exports_run : ∀ (es : Externs), PrimFns es → ∀ σ δ, Match σ δ →
    Sim (fun E δ δ' => ReadsE es E δ δ' ∧ InstOnly E) (exportDecls es) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl,
      fun rest is es => by simp [List.append_nil], fun d hd => absurd hd List.not_mem_nil⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    obtain ⟨s, hk, hs⟩ : ∃ s, k = .func s ∧ PrimSig s := h (n, k) List.mem_cons_self
    have hxs : PrimFns xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [hk]
    rcases funcTy_run hs σ with ⟨j, hl, hf⟩ | hf
    · let σ2 : Scope := { σ with decls := σ.decls ++ [.inst (.export ⟨n, .plain0⟩ (.func j))] }
      have hm2 : Match σ2 δ := ⟨hm.size, hm.fc⟩
      obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads, hinst⟩ := exports_run xs hxs σ2 δ hm2
      refine ⟨σ', .inst (.export ⟨n, .plain0⟩ (.func j)) :: E, δ', ?_, ?_, hm', hsh, hn, ?_, ?_⟩
      · rw [exportDecls_cons, hf]; exact hr
      · rw [hd]; simp [σ2]
      · intro rest is es
        rw [List.cons_append, dec_export (hm.fc s j (mem_of_lookup hl)) n, hreads]
        simp
      · intro d hd'
        rcases List.mem_cons.1 hd' with e | hm''
        · exact ⟨_, e⟩
        · exact hinst d hm''
    · let σ1 := defFn σ s
      let δ1 : DScope := { δ with types := δ.types.push (.func s) }
      let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ (.func σ.ntypes))] }
      have hm1 : Match σ1 δ1 := match_defFn hm s
      have hm2 : Match σ2 δ1 := ⟨hm1.size, hm1.fc⟩
      have hat : δ1.types[σ.ntypes]? = some (.func s) := by rw [← hm.size]; simp [δ1]
      obtain ⟨σ', E, δ', hr, hd, hm', hsh, hn, hreads, hinst⟩ := exports_run xs hxs σ2 δ1 hm2
      refine ⟨σ', .inst (.type (.func (ft s))) :: .inst (.export ⟨n, .plain0⟩ (.func σ.ntypes)) :: E, δ',
        ?_, ?_, hm', hsh, hn, ?_, ?_⟩
      · rw [exportDecls_cons, hf]; exact hr
      · rw [hd]; simp [σ2, σ1, defFn]
      · intro rest is es
        rw [List.cons_append, List.cons_append, dec_functype hs, dec_export hat n, hreads]
        simp
      · intro d hd'
        rcases List.mem_cons.1 hd' with e | hm''
        · exact ⟨_, e⟩
        rcases List.mem_cons.1 hm'' with e | hm'''
        · exact ⟨_, e⟩
        · exact hinst d hm'''

/-! ## Packages -/

/-- **Decoding inverts encoding** on packages of functions over primitive value types:
the declarations the encoder writes for the imports `is` and exports `es` (in a
sharing scope, as for a package's component type) are read back by `pkgOfWorld` as
exactly those imports and exports, with no definitions and no nominal types. -/
theorem decode_encode {is es : Externs} (his : PrimFns is) (hes : PrimFns es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := is, exports := es }, []) := by
  have hm0 : Match { share := true } {} := ⟨rfl, fun _ _ h => absurd h (by simp)⟩
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, -, hn1, hreads1⟩ := imports_run is his _ _ hm0
  obtain ⟨σ2, E2, δ2, hr2, hd2, -, -, hn2, hreads2, -⟩ := exports_run es hes σ1 δ1 hm1
  refine ⟨σ2, by simp [hr1, hr2], ?_⟩
  have hdec : (decCDecls σ2.decls [] []).run {} = .ok ((is, es), δ2) := by
    have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
    rw [e, hreads1, hreads2]
    simp [decCDecls]
  have hnom : δ2.nom = [] := by rw [hn2, hn1]
  simp [pkgOfWorld, hdec, hnom]
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨s, e, -⟩ := hes (a, b) hab; rw [show b = .func s from e]
  · obtain ⟨s, e, -⟩ := hes (a, b) hab; rw [show b = .func s from e]

end DecodeEnc

end Silmaril.Wasm.Wac.Bridge
