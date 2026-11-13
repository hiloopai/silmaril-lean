module

public import Silmaril.Wasm.Wac.Bridge.DecodeEnc.Thms

/-!
# WAC bridge: decoding inverts encoding on packages of functions and interfaces

`Bridge.DecodeEnc` proves `decode ∘ encode = id` for packages whose items are functions
over primitive value types. This module adds **instances** (interfaces) whose exports
are such functions, the shape of most WIT packages' imports and exports:

* `decode_encode_iface`: for imports `is` and exports `es` made of functions over
  primitives and instances of them (`Items1`), `pkgOfWorld` reads the encoded
  declarations back as `fixEx is` and `fixEx es`: the same items, where an instance's
  interface identifier is the one the decoder derives from its name (`ifaceId n`, as
  wac sets it; `fixK`). When the identifiers already are those, decoding returns the
  items unchanged (`decode_encode_iface_id`).

Instance types are shared by kind (`share := true`, the encoder's `kcache`) and defined
in a nested scope; `Match2` adds to `DecodeEnc.Match` that every cached instance kind is
decoded at its index, and `dec_instype` reads an instance type back through
`decIDecls` (`cdecls_inst` relates it to `decCDecls` on instance declarations).

**Not covered.** As in `DecodeEnc`: value types other than primitives, type items,
resources, nested instances inside instance types, component items, and the byte level.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeEnc

namespace DecodeIface

theorem okb {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a).bind f = f a := rfl

theorem errb {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e).bind f = .error e := rfl

theorem err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

attribute [local simp] ok_bind pure_ok Except.map_ok okb errb err_bind

theorem mem_of_lookupK {k : Kind} {j : Nat} : ∀ {l : List (Kind × Nat)}, l.lookup k = some j → (k, j) ∈ l
  | [], h => absurd h (by simp)
  | (k', j') :: l, h => by
    by_cases e : k = k'
    · have hb : (k == k') = true := beq_iff_eq.2 e
      have hj : j' = j := by simpa [List.lookup, hb] using h
      rw [e, hj]; exact List.mem_cons_self
    · have hb : (k == k') = false := beq_false_of_ne e
      have h' : l.lookup k = some j := by simpa [List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (mem_of_lookupK h')

/-! ## The fragment -/

/-- A function over primitives, or an instance exporting such functions. -/
def Item1 (k : Kind) : Prop :=
  (∃ s, k = .func s ∧ PrimSig s) ∨ ∃ i fs, k = .inst i fs ∧ PrimFns fs

/-- Items of the fragment. -/
def Items1 (es : Externs) : Prop := ∀ p ∈ es, Item1 p.2

/-- The kind the decoder reads back for an item named `n`: an instance gets the
identifier its name carries. -/
def fixK (n : String) : Kind → Kind
  | .inst _ es => .inst (ifaceId n) es
  | k => k

/-- `fixK` on named items. -/
def fixEx (es : Externs) : Externs := es.map fun p => (p.1, fixK p.1 p.2)

/-! ## The invariant -/

/-- `Match`, and every cached instance kind is decoded at its index. -/
structure Match2 (σ : Scope) (δ : DScope) : Prop where
  base : Match σ δ
  kc : ∀ k j, (k, j) ∈ σ.kcache → ∃ i es, k = .inst i es ∧ δ.types[j]? = some (.inst es)

theorem push_keep {δ : DScope} {t : TInfo} {j : Nat} {x : TInfo} (h : δ.types[j]? = some x) :
    (δ.types.push t)[j]? = some x := by
  have hlt : j < δ.types.size := (Array.getElem?_eq_some_iff.1 h).1
  simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using h

theorem match2_types {σ : Scope} {δ δ' : DScope} (h : Match2 σ δ) (e : δ'.types = δ.types) : Match2 σ δ' :=
  ⟨⟨by rw [e]; exact h.base.size, fun s j hj => by rw [e]; exact h.base.fc s j hj⟩,
    fun k j hj => by rw [e]; exact h.kc k j hj⟩

theorem match2_defFn {σ : Scope} {δ : DScope} (hm : Match2 σ δ) (s : Sig) :
    Match2 (defFn σ s) { δ with types := δ.types.push (.func s) } := by
  refine ⟨match_defFn hm.base s, fun k j hj => ?_⟩
  obtain ⟨i, es, e, h⟩ := hm.kc k j hj
  exact ⟨i, es, e, push_keep h⟩

/-- The scope after defining and caching the instance type of `.inst i fs`. -/
def defInst (σ : Scope) (i : Option String) (fs : Externs) (D : List InstanceDecl) : Scope :=
  { σ with decls := σ.decls ++ [.inst (.type (.instance D))], ntypes := σ.ntypes + 1,
           kcache := σ.kcache ++ [(.inst i fs, σ.ntypes)] }

theorem match2_defInst {σ : Scope} {δ : DScope} (hm : Match2 σ δ) (i : Option String) (fs : Externs)
    (D : List InstanceDecl) : Match2 (defInst σ i fs D) { δ with types := δ.types.push (.inst fs) } := by
  refine ⟨⟨by simp [defInst, hm.base.size], fun s j hj => push_keep (hm.base.fc s j hj)⟩, fun k j hj => ?_⟩
  rcases List.mem_append.1 hj with hj | hj
  · obtain ⟨i', es, e, h⟩ := hm.kc k j hj
    exact ⟨i', es, e, push_keep h⟩
  · have e : (k, j) = (.inst i fs, σ.ntypes) := List.mem_singleton.1 hj
    refine ⟨i, fs, (Prod.mk.inj e).1, ?_⟩
    rw [(Prod.mk.inj e).2, ← hm.base.size]
    simp

/-! ## Instance types -/

theorem instDecls_map (D : List InstanceDecl) : instDecls (D.map .inst) = D := by
  induction D with
  | nil => rfl
  | cons d D _ => simp [instDecls]

theorem instOnly_eq {E : List ComponentDecl} (h : InstOnly E) : E = (instDecls E).map .inst := by
  induction E with
  | nil => rfl
  | cons d E ih =>
    obtain ⟨x, e⟩ := h d List.mem_cons_self
    have ih' := ih fun d' hd => h d' (List.mem_cons_of_mem _ hd)
    rw [e, instDecls, List.filterMap_cons]
    simp only [List.map_cons]
    rw [← instDecls, ← ih']

/-- Component declarations that are instance declarations are read as an instance
type's declarations. -/
theorem cdecls_inst (δ : DScope) (is : Externs) : ∀ (D : List InstanceDecl) (es : Externs),
    (decCDecls (D.map .inst) is es).run δ =
      ((decIDecls D es).run δ).bind fun p => (decCDecls [] is p.1).run p.2
  | [], es => by simp [decCDecls, decIDecls]
  | d :: D, es => by
    cases hd : (decIDecl d es).run δ with
    | error e => simp [decCDecls, decIDecls, hd]
    | ok p => simp [decCDecls, decIDecls, hd, cdecls_inst p.2 is D p.1]

/-- **An instance type of functions over primitives** is encoded in a nested scope as
declarations `D` that `decIDecls` reads back as the functions. -/
theorem nested_exports {fs : Externs} (hfs : PrimFns fs) (σ : Scope) (δ : DScope) :
    ∃ D, (nested false (exportDecls fs)).run σ = .ok (D.map .inst, σ) ∧
      ∃ δi, (decIDecls D []).run { outer := δ.types :: δ.outer, nom := δ.nom } = .ok (fs, δi) ∧
        δi.nom = δ.nom := by
  have hm0 : Match { nom := σ.nom, share := false } { outer := δ.types :: δ.outer, nom := δ.nom } :=
    ⟨rfl, fun _ _ h => absurd h (by simp)⟩
  obtain ⟨σi, E, δi, hr, hd, -, -, hn, hreads, hinst⟩ := exports_run fs hfs _ _ hm0
  have hE : E = (instDecls E).map .inst := instOnly_eq hinst
  refine ⟨instDecls E, ?_, ?_⟩
  · have hdecls : σi.decls = E := by simpa using hd
    simp [nested, hr, hdecls, ← hE]
  · have h1 := hreads [] [] []
    rw [List.append_nil, hE, cdecls_inst] at h1
    cases hD : (decIDecls (instDecls E) []).run { outer := δ.types :: δ.outer, nom := δ.nom } with
    | error e => simp [hD, decCDecls] at h1
    | ok p =>
      have e : p.1 = fs ∧ p.2 = δi := by simpa [hD, decCDecls] using h1
      refine ⟨p.2, ?_, ?_⟩
      · rw [show p = (fs, p.2) from Prod.ext e.1 rfl]
      · rw [e.2, hn]

theorem dec_instype {δ δi : DScope} {D : List InstanceDecl} {fs : Externs}
    (hD : (decIDecls D []).run { outer := δ.types :: δ.outer, nom := δ.nom } = .ok (fs, δi))
    (hn : δi.nom = δ.nom) (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.inst (.type (.instance D)) :: rest) is es).run δ =
      (decCDecls rest is es).run { δ with types := δ.types.push (.inst fs) } := by
  simp [decCDecls, decIDecl, decDefType, pushTy, inNested, hD, hn]

/-! ## One item -/

/-- What encoding one item's descriptor does, and how the decoder reads it back. -/
def ItemOk (k : Kind) (σ : Scope) (δ : DScope) : Prop :=
  ∃ d σ1 E δ1, (externDesc k).run σ = .ok (d, σ1) ∧ (∀ b, d ≠ .type b) ∧ σ1.decls = σ.decls ++ E ∧
    Match2 σ1 δ1 ∧ σ1.share = σ.share ∧ δ1.nom = δ.nom ∧
    (∀ rest is es, (decCDecls (E ++ rest) is es).run δ = (decCDecls rest is es).run δ1) ∧
    ∀ n, ∃ δ2, (decExtern n d).run δ1 = .ok (fixK n k, δ2) ∧ δ2.types = δ1.types ∧ δ2.nom = δ1.nom

theorem item_func {s : Sig} (hs : PrimSig s) {σ : Scope} {δ : DScope} (hm : Match2 σ δ) :
    ItemOk (.func s) σ δ := by
  rcases funcTy_run hs σ with ⟨j, hl, hf⟩ | hf
  · have hj : δ.types[j]? = some (.func s) := hm.base.fc s j (mem_of_lookup hl)
    refine ⟨.func j, σ, [], δ, by simp [externDesc, hf], fun b => by simp, by simp, hm, rfl, rfl,
      fun rest is es => by simp, fun n => ⟨δ, by simp [decExtern, typeAt_run hj, fixK], rfl, rfl⟩⟩
  · let δ1 : DScope := { δ with types := δ.types.push (.func s) }
    have hj : δ1.types[σ.ntypes]? = some (.func s) := by rw [← hm.base.size]; simp [δ1]
    refine ⟨.func σ.ntypes, defFn σ s, [.inst (.type (.func (ft s)))], δ1, by simp [externDesc, hf],
      fun b => by simp, by simp [defFn], match2_defFn hm s, rfl, rfl, fun rest is es => ?_,
      fun n => ⟨δ1, by simp [decExtern, typeAt_run hj, fixK], rfl, rfl⟩⟩
    rw [List.singleton_append, dec_functype hs]

theorem item_inst_hit {i : Option String} {fs : Externs} {σ : Scope} {δ : DScope} (hm : Match2 σ δ)
    (hsh : σ.share = true) {j : Nat} (hl : σ.kcache.lookup (.inst i fs) = some j) :
    ItemOk (.inst i fs) σ δ := by
  obtain ⟨i', es, e, hj⟩ := hm.kc _ j (mem_of_lookupK hl)
  have hes : es = fs := (Kind.inst.inj e).2.symm
  have hj' : δ.types[j]? = some (.inst fs) := hes ▸ hj
  refine ⟨.instance j, σ, [], δ, by simp [externDesc, shared, hsh, hl], fun b => by simp, by simp, hm,
    rfl, rfl, fun rest is es => by simp, fun n => ⟨{ δ with insts := δ.insts.push fs }, ?_, rfl, rfl⟩⟩
  simp [decExtern, typeAt_run hj', fixK]

theorem item_inst_miss {i : Option String} {fs : Externs} (hfs : PrimFns fs) {σ : Scope} {δ : DScope}
    (hm : Match2 σ δ) (hc : ¬ (σ.share = true ∧ ∃ j, σ.kcache.lookup (.inst i fs) = some j)) :
    ItemOk (.inst i fs) σ δ := by
  obtain ⟨D, hnest, δi, hD, hn⟩ := nested_exports hfs σ δ
  let δ1 : DScope := { δ with types := δ.types.push (.inst fs) }
  have hj : δ1.types[σ.ntypes]? = some (.inst fs) := by rw [← hm.base.size]; simp [δ1]
  have hrun : (externDesc (.inst i fs)).run σ = .ok (.instance σ.ntypes, defInst σ i fs D) := by
    cases hsh : σ.share with
    | false => simp [externDesc, shared, hsh, hnest, instDecls_map, defTy, defInst]
    | true =>
      cases hl : σ.kcache.lookup (.inst i fs) with
      | none => simp [externDesc, shared, hsh, hl, hnest, instDecls_map, defTy, defInst]
      | some j => exact absurd ⟨hsh, j, hl⟩ hc
  refine ⟨.instance σ.ntypes, defInst σ i fs D, [.inst (.type (.instance D))], δ1, hrun,
    fun b => by simp, by simp [defInst], match2_defInst hm i fs D, rfl, rfl, fun rest is es => ?_,
    fun n => ⟨{ δ1 with insts := δ1.insts.push fs }, ?_, rfl, rfl⟩⟩
  · rw [List.singleton_append, dec_instype hD hn]
  · simp [decExtern, typeAt_run hj, fixK]

theorem item_inst {i : Option String} {fs : Externs} (hfs : PrimFns fs) {σ : Scope} {δ : DScope}
    (hm : Match2 σ δ) : ItemOk (.inst i fs) σ δ := by
  by_cases hc : σ.share = true ∧ ∃ j, σ.kcache.lookup (.inst i fs) = some j
  · obtain ⟨hsh, j, hl⟩ := hc
    exact item_inst_hit hm hsh hl
  · exact item_inst_miss hfs hm hc

theorem item_ok {k : Kind} (h : Item1 k) {σ : Scope} {δ : DScope} (hm : Match2 σ δ) : ItemOk k σ δ := by
  rcases h with ⟨s, e, hs⟩ | ⟨i, fs, e, hfs⟩
  · rw [e]; exact item_func hs hm
  · rw [e]; exact item_inst hfs hm

/-! ## Lists of items -/

/-- What encoding items does (`Match2` in place of `Match`). -/
def Sim2 (Rd : List ComponentDecl → DScope → DScope → Prop) (m : TM Unit) (σ : Scope) (δ : DScope) : Prop :=
  ∃ σ' E δ', m.run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧ Match2 σ' δ' ∧
    σ'.share = σ.share ∧ δ'.nom = δ.nom ∧ Rd E δ δ'

theorem importDecls_item {n : String} {k : Kind} {es : Externs} {σ σ1 : Scope} {d : ExternDesc}
    (h : (externDesc k).run σ = .ok (d, σ1)) (hd : ∀ b, d ≠ .type b) :
    (importDecls ((n, k) :: es)).run σ =
      (importDecls es).run { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ d] } := by
  cases d with
  | type b => exact absurd rfl (hd b)
  | _ => simp [importDecls, h, declared]

theorem exportDecls_item {n : String} {k : Kind} {es : Externs} {σ σ1 : Scope} {d : ExternDesc}
    (h : (externDesc k).run σ = .ok (d, σ1)) (hd : ∀ b, d ≠ .type b) :
    (exportDecls ((n, k) :: es)).run σ =
      (exportDecls es).run { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] } := by
  cases d with
  | type b => exact absurd rfl (hd b)
  | _ => simp [exportDecls, h, declared]

theorem dec_import_gen {δ δ2 : DScope} {n : String} {d : ExternDesc} {k : Kind}
    (h : (decExtern n d).run δ = .ok (k, δ2)) (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.import ⟨n, .plain0⟩ d :: rest) is es).run δ = (decCDecls rest (is ++ [(n, k)]) es).run δ2 := by
  simp [decCDecls, h]

theorem dec_export_gen {δ δ2 : DScope} {n : String} {d : ExternDesc} {k : Kind}
    (h : (decExtern n d).run δ = .ok (k, δ2)) (rest : List ComponentDecl) (is es : Externs) :
    (decCDecls (.inst (.export ⟨n, .plain0⟩ d) :: rest) is es).run δ = (decCDecls rest is (es ++ [(n, k)])).run δ2 := by
  simp [decCDecls, decIDecl, h]

theorem imports2_run : ∀ (is : Externs), Items1 is → ∀ σ δ, Match2 σ δ →
    Sim2 (ReadsI (fixEx is)) (importDecls is) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl, fun rest is es => by simp [fixEx]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    have hk : Item1 k := h (n, k) List.mem_cons_self
    have hxs : Items1 xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, σ1, E1, δ1, hr1, hd, hdec1, hm1, hsh1, hn1, hreads1, hext⟩ := item_ok hk hm
    obtain ⟨δ2, hx, ht2, hn2⟩ := hext n
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ d] }
    have hm2 : Match2 σ2 δ2 := match2_types ⟨⟨hm1.base.size, hm1.base.fc⟩, hm1.kc⟩ ht2
    obtain ⟨σ', E, δ', hr, hdec, hm', hsh, hn, hreads⟩ := imports2_run xs hxs σ2 δ2 hm2
    refine ⟨σ', E1 ++ .import ⟨n, .plain0⟩ d :: E, δ', ?_, ?_, hm', ?_, ?_, ?_⟩
    · rw [importDecls_item hr1 hd]; exact hr
    · rw [hdec]; simp [σ2, hdec1]
    · rw [hsh, ← hsh1]
    · rw [hn, hn2, hn1]
    · intro rest is es
      rw [List.append_assoc, hreads1, List.cons_append, dec_import_gen hx, hreads]
      simp [fixEx]

theorem exports2_run : ∀ (es : Externs), Items1 es → ∀ σ δ, Match2 σ δ →
    Sim2 (ReadsE (fixEx es)) (exportDecls es) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl, fun rest is es => by simp [fixEx]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    have hk : Item1 k := h (n, k) List.mem_cons_self
    have hxs : Items1 xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, σ1, E1, δ1, hr1, hd, hdec1, hm1, hsh1, hn1, hreads1, hext⟩ := item_ok hk hm
    obtain ⟨δ2, hx, ht2, hn2⟩ := hext n
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }
    have hm2 : Match2 σ2 δ2 := match2_types ⟨⟨hm1.base.size, hm1.base.fc⟩, hm1.kc⟩ ht2
    obtain ⟨σ', E, δ', hr, hdec, hm', hsh, hn, hreads⟩ := exports2_run xs hxs σ2 δ2 hm2
    refine ⟨σ', E1 ++ .inst (.export ⟨n, .plain0⟩ d) :: E, δ', ?_, ?_, hm', ?_, ?_, ?_⟩
    · rw [exportDecls_item hr1 hd]; exact hr
    · rw [hdec]; simp [σ2, hdec1]
    · rw [hsh, ← hsh1]
    · rw [hn, hn2, hn1]
    · intro rest is es
      rw [List.append_assoc, hreads1, List.cons_append, dec_export_gen hx, hreads]
      simp [fixEx]

/-! ## Packages -/

/-- **Decoding inverts encoding** on packages of functions over primitives and
interfaces of them: `pkgOfWorld` reads the encoded component type back as the same
imports and exports, each instance with the identifier its name carries. -/
theorem decode_encode_iface {is es : Externs} (his : Items1 is) (hes : Items1 es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := fixEx is, exports := fixEx es }, []) := by
  have hm0 : Match2 { share := true } {} :=
    ⟨⟨rfl, fun _ _ h => absurd h (by simp)⟩, fun _ _ h => absurd h (by simp)⟩
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, -, hn1, hreads1⟩ := imports2_run is his _ _ hm0
  obtain ⟨σ2, E2, δ2, hr2, hd2, -, -, hn2, hreads2⟩ := exports2_run es hes σ1 δ1 hm1
  refine ⟨σ2, by simp [hr1, hr2], ?_⟩
  have hdec : (decCDecls σ2.decls [] []).run {} = .ok ((fixEx is, fixEx es), δ2) := by
    have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
    rw [e, hreads1, hreads2]
    simp [decCDecls]
  have hnom : δ2.nom = [] := by rw [hn2, hn1]
  simp [pkgOfWorld, hdec, hnom]
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  all_goals
    obtain ⟨⟨n, k⟩, hk, e⟩ := List.mem_map.1 hab
    have e2 : fixK n k = b := congrArg Prod.snd e
    rcases hes (n, k) hk with ⟨s, ek, -⟩ | ⟨i, fs, ek, -⟩
    · have ek' : k = .func s := ek
      rw [← e2, ek']; rfl
    · have ek' : k = .inst i fs := ek
      rw [← e2, ek']; rfl

/-- Items whose instances carry the identifier of their name. -/
def IdsOk (es : Externs) : Prop := ∀ p ∈ es, fixK p.1 p.2 = p.2

theorem fixEx_id {es : Externs} (h : IdsOk es) : fixEx es = es := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    have hp : fixK p.1 p.2 = p.2 := h p List.mem_cons_self
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [fixEx, List.map_cons] at ih' ⊢
    rw [hp, ih']

/-- **`decode ∘ encode = id`** on such packages when every instance already has the
identifier of its name. -/
theorem decode_encode_iface_id {is es : Externs} (his : Items1 is) (hes : Items1 es) (hi : IdsOk is)
    (he : IdsOk es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := is, exports := es }, []) := by
  obtain ⟨σ, h1, h2⟩ := decode_encode_iface his hes
  exact ⟨σ, h1, by rw [h2, fixEx_id hi, fixEx_id he]⟩

end DecodeIface

end Silmaril.Wasm.Wac.Bridge
