module

public import Silmaril.Wasm.Wac.Bridge.DecodeAnon.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeIface.Thms

/-!
# WAC bridge: decoding inverts encoding on interfaces of functions over anonymous types

The simulation of `Silmaril.Wasm.Wac.Bridge.DecodeIface` (instance types, shared through
the cache `kcache` in component types) over that of `Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnon`
(anonymous value types): `Match3` is `MatchA` with the cached instance types.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeEnc (typeAt_run ReadsI ReadsE InstOnly)
open DecodeIface (fixK fixEx instDecls_map instOnly_eq cdecls_inst dec_instype mem_of_lookupK
  importDecls_item exportDecls_item dec_import_gen dec_export_gen)
open DecodeAnon

namespace DecodeAnonIface

attribute [local simp] DecodeEnc.ok_bind DecodeEnc.pure_ok Except.map_ok DecodeIface.okb
  DecodeIface.errb DecodeIface.err_bind

/-! ## The fragment -/

/-- A function over anonymous value types, or an instance exporting such functions. -/
def Item2 (k : Kind) : Prop :=
  (∃ s, k = .func s ∧ AnonSig s) ∨ ∃ i fs, k = .inst i fs ∧ AnonFns fs

/-- Items of the fragment. -/
def Items2 (es : Externs) : Prop := ∀ p ∈ es, Item2 p.2

/-! ## The invariant -/

/-- `MatchA`, and every cached instance kind is decoded at its index. -/
structure Match3 (σ : Scope) (δ : DScope) : Prop where
  base : MatchA σ δ
  kc : ∀ k j, (k, j) ∈ σ.kcache → ∃ i es, k = .inst i es ∧ δ.types[j]? = some (.inst es)

theorem ext_of_types {δ δ' : DScope} (e : δ'.types = δ.types) : Ext δ' δ :=
  fun i x h => by rw [e] at h; exact h

theorem matchA_types {σ : Scope} {δ δ' : DScope} (h : MatchA σ δ) (e : δ'.types = δ.types) :
    MatchA σ δ' := by
  refine ⟨by rw [e]; exact h.size, fun s j hj => by rw [e]; exact h.fc s j hj, fun d j hj => ?_⟩
  obtain ⟨t, ht, hd⟩ := h.vc d j hj
  exact ⟨t, by rw [e]; exact ht, hd.mono (ext_of_types e.symm)⟩

theorem match3_types {σ : Scope} {δ δ' : DScope} (h : Match3 σ δ) (e : δ'.types = δ.types) :
    Match3 σ δ' :=
  ⟨matchA_types h.base e, fun k j hj => by rw [e]; exact h.kc k j hj⟩

/-- A step of the value-level simulation keeps the cached instance types. -/
theorem match3_of_vsim {σ σ' : Scope} {δ δ' : DScope} (hm : Match3 σ δ) (hm' : MatchA σ' δ')
    (hk : σ'.kcache = σ.kcache) (he : Ext δ δ') : Match3 σ' δ' := by
  refine ⟨hm', fun k j hj => ?_⟩
  rw [hk] at hj
  obtain ⟨i, es, e, h⟩ := hm.kc k j hj
  exact ⟨i, es, e, he _ _ h⟩

/-- The scope after defining and caching the instance type of `.inst i fs`. -/
def defInst (σ : Scope) (i : Option String) (fs : Externs) (D : List InstanceDecl) : Scope :=
  { σ with decls := σ.decls ++ [.inst (.type (.instance D))], ntypes := σ.ntypes + 1,
           kcache := σ.kcache ++ [(.inst i fs, σ.ntypes)] }

theorem match3_defInst {σ : Scope} {δ : DScope} (hm : Match3 σ δ) (i : Option String)
    (fs : Externs) (D : List InstanceDecl) :
    Match3 (defInst σ i fs D) { δ with types := δ.types.push (.inst fs) } := by
  refine ⟨matchA_push hm.base (.inst fs) rfl (fun s j hj => Or.inl hj) (fun d j hj => Or.inl hj),
    fun k j hj => ?_⟩
  rcases List.mem_append.1 hj with hj | hj
  · obtain ⟨i', es, e, h⟩ := hm.kc k j hj
    exact ⟨i', es, e, push_keep h⟩
  · have e : (k, j) = (.inst i fs, σ.ntypes) := List.mem_singleton.1 hj
    refine ⟨i, fs, (Prod.mk.inj e).1, ?_⟩
    rw [(Prod.mk.inj e).2, ← hm.base.size]
    exact push_self δ _

/-! ## Instance types -/

theorem matchA_nested (σ : Scope) (δ : DScope) :
    MatchA { nom := σ.nom, share := false } { outer := δ.types :: δ.outer, nom := δ.nom } :=
  ⟨rfl, fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩

/-- **An instance type of functions over anonymous value types** is encoded in a nested
scope as declarations `D` that `decIDecls` reads back as the functions. -/
theorem nested_exports {fs : Externs} (hfs : AnonFns fs) (σ : Scope) (δ : DScope) :
    ∃ D, (nested false (exportDecls fs)).run σ = .ok (D.map .inst, σ) ∧
      ∃ δi, (decIDecls D []).run { outer := δ.types :: δ.outer, nom := δ.nom } = .ok (fs, δi) ∧
        δi.nom = δ.nom := by
  obtain ⟨σi, E, δi, hr, hd, -, -, hn, hreads, hinst⟩ := exports_sim fs hfs _ _ (matchA_nested σ δ)
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

/-! ## One item -/

/-- What encoding one item's descriptor does, and how the decoder reads it back. -/
def ItemOk (k : Kind) (σ : Scope) (δ : DScope) : Prop :=
  ∃ d σ1 E δ1, (externDesc k).run σ = .ok (d, σ1) ∧ (∀ b, d ≠ .type b) ∧ σ1.decls = σ.decls ++ E ∧
    Match3 σ1 δ1 ∧ σ1.share = σ.share ∧ δ1.nom = δ.nom ∧
    (∀ rest is es, (decCDecls (E ++ rest) is es).run δ = (decCDecls rest is es).run δ1) ∧
    ∀ n, ∃ δ2, (decExtern n d).run δ1 = .ok (fixK n k, δ2) ∧ δ2.types = δ1.types ∧ δ2.nom = δ1.nom

theorem item_func {s : Sig} (hs : AnonSig s) {σ : Scope} {δ : DScope} (hm : Match3 σ δ) :
    ItemOk (.func s) σ δ := by
  obtain ⟨j, σ1, E1, δ1, hr, hd, hm1, hsh, hk, hn, he, hR, hj⟩ := funcTy_sim hs hm.base
  have hdesc : (externDesc (.func s)).run σ = .ok (.func j, σ1) := by simp [externDesc, hr]
  have hdec : ∀ n, (decExtern n (.func j)).run δ1 = .ok (fixK n (.func s), δ1) := fun n => by
    simp [decExtern, typeAt_run hj, fixK]
  exact ⟨.func j, σ1, E1, δ1, hdesc, fun b => by simp, hd, match3_of_vsim hm hm1 hk he, hsh, hn,
    hR.2, fun n => ⟨δ1, hdec n, rfl, rfl⟩⟩

theorem item_inst_hit {i : Option String} {fs : Externs} {σ : Scope} {δ : DScope} (hm : Match3 σ δ)
    (hsh : σ.share = true) {j : Nat} (hl : σ.kcache.lookup (.inst i fs) = some j) :
    ItemOk (.inst i fs) σ δ := by
  obtain ⟨i', es, e, hj⟩ := hm.kc _ j (mem_of_lookupK hl)
  have hes : es = fs := (Kind.inst.inj e).2.symm
  have hj' : δ.types[j]? = some (.inst fs) := hes ▸ hj
  refine ⟨.instance j, σ, [], δ, by simp [externDesc, shared, hsh, hl], fun b => by simp, by simp, hm,
    rfl, rfl, fun rest is es => by simp, fun n => ⟨{ δ with insts := δ.insts.push fs }, ?_, rfl, rfl⟩⟩
  simp [decExtern, typeAt_run hj', fixK]

theorem externDesc_inst_miss {i : Option String} {fs : Externs} {σ : Scope} {D : List InstanceDecl}
    (hnest : (nested false (exportDecls fs)).run σ = .ok (D.map .inst, σ))
    (hc : ¬ (σ.share = true ∧ ∃ j, σ.kcache.lookup (.inst i fs) = some j)) :
    (externDesc (.inst i fs)).run σ = .ok (.instance σ.ntypes, defInst σ i fs D) := by
  cases hsh : σ.share with
  | false => simp [externDesc, shared, hsh, hnest, instDecls_map, defTy, defInst]
  | true =>
    cases hl : σ.kcache.lookup (.inst i fs) with
    | none => simp [externDesc, shared, hsh, hl, hnest, instDecls_map, defTy, defInst]
    | some j => exact absurd ⟨hsh, j, hl⟩ hc

theorem item_inst_miss {i : Option String} {fs : Externs} (hfs : AnonFns fs) {σ : Scope}
    {δ : DScope} (hm : Match3 σ δ)
    (hc : ¬ (σ.share = true ∧ ∃ j, σ.kcache.lookup (.inst i fs) = some j)) :
    ItemOk (.inst i fs) σ δ := by
  obtain ⟨D, hnest, δi, hD, hn⟩ := nested_exports hfs σ δ
  let δ1 : DScope := { δ with types := δ.types.push (.inst fs) }
  have hj : δ1.types[σ.ntypes]? = some (.inst fs) := by rw [← hm.base.size]; exact push_self δ _
  refine ⟨.instance σ.ntypes, defInst σ i fs D, [.inst (.type (.instance D))], δ1,
    externDesc_inst_miss hnest hc, fun b => by simp, by simp [defInst], match3_defInst hm i fs D,
    rfl, rfl, fun rest is es => ?_, fun n => ⟨{ δ1 with insts := δ1.insts.push fs }, ?_, rfl, rfl⟩⟩
  · rw [List.singleton_append, dec_instype hD hn]
  · simp [decExtern, typeAt_run hj, fixK]

theorem item_ok {k : Kind} (h : Item2 k) {σ : Scope} {δ : DScope} (hm : Match3 σ δ) :
    ItemOk k σ δ := by
  rcases h with ⟨s, e, hs⟩ | ⟨i, fs, e, hfs⟩
  · rw [e]; exact item_func hs hm
  · rw [e]
    by_cases hc : σ.share = true ∧ ∃ j, σ.kcache.lookup (.inst i fs) = some j
    · obtain ⟨hsh, j, hl⟩ := hc
      exact item_inst_hit hm hsh hl
    · exact item_inst_miss hfs hm hc

/-! ## Lists of items -/

/-- What encoding items does (`Match3`). -/
def Sim3 (Rd : List ComponentDecl → DScope → DScope → Prop) (m : TM Unit) (σ : Scope)
    (δ : DScope) : Prop :=
  ∃ σ' E δ', m.run σ = .ok ((), σ') ∧ σ'.decls = σ.decls ++ E ∧ Match3 σ' δ' ∧
    σ'.share = σ.share ∧ δ'.nom = δ.nom ∧ Rd E δ δ'

theorem imports3_run : ∀ (is : Externs), Items2 is → ∀ σ δ, Match3 σ δ →
    Sim3 (ReadsI (fixEx is)) (importDecls is) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl,
      fun rest is es => by simp [fixEx]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    have hk : Item2 k := h (n, k) List.mem_cons_self
    have hxs : Items2 xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, σ1, E1, δ1, hr1, hd, hdec1, hm1, hsh1, hn1, hreads1, hext⟩ := item_ok hk hm
    obtain ⟨δ2, hx, ht2, hn2⟩ := hext n
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.import ⟨n, .plain0⟩ d] }
    have hm2 : Match3 σ2 δ2 :=
      match3_types ⟨⟨hm1.base.size, hm1.base.fc, hm1.base.vc⟩, hm1.kc⟩ ht2
    obtain ⟨σ', E, δ', hr, hdec, hm', hsh, hn, hreads⟩ := imports3_run xs hxs σ2 δ2 hm2
    refine ⟨σ', E1 ++ .import ⟨n, .plain0⟩ d :: E, δ', ?_, ?_, hm', ?_, ?_, ?_⟩
    · rw [importDecls_item hr1 hd]; exact hr
    · rw [hdec]; simp [σ2, hdec1]
    · rw [hsh, ← hsh1]
    · rw [hn, hn2, hn1]
    · intro rest is es
      rw [List.append_assoc, hreads1, List.cons_append, dec_import_gen hx, hreads]
      simp [fixEx]

theorem exports3_run : ∀ (es : Externs), Items2 es → ∀ σ δ, Match3 σ δ →
    Sim3 (ReadsE (fixEx es)) (exportDecls es) σ δ
  | [], _, σ, δ, hm => ⟨σ, [], δ, rfl, (List.append_nil _).symm, hm, rfl, rfl,
      fun rest is es => by simp [fixEx]⟩
  | (n, k) :: xs, h, σ, δ, hm => by
    have hk : Item2 k := h (n, k) List.mem_cons_self
    have hxs : Items2 xs := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, σ1, E1, δ1, hr1, hd, hdec1, hm1, hsh1, hn1, hreads1, hext⟩ := item_ok hk hm
    obtain ⟨δ2, hx, ht2, hn2⟩ := hext n
    let σ2 : Scope := { σ1 with decls := σ1.decls ++ [.inst (.export ⟨n, .plain0⟩ d)] }
    have hm2 : Match3 σ2 δ2 :=
      match3_types ⟨⟨hm1.base.size, hm1.base.fc, hm1.base.vc⟩, hm1.kc⟩ ht2
    obtain ⟨σ', E, δ', hr, hdec, hm', hsh, hn, hreads⟩ := exports3_run xs hxs σ2 δ2 hm2
    refine ⟨σ', E1 ++ .inst (.export ⟨n, .plain0⟩ d) :: E, δ', ?_, ?_, hm', ?_, ?_, ?_⟩
    · rw [exportDecls_item hr1 hd]; exact hr
    · rw [hdec]; simp [σ2, hdec1]
    · rw [hsh, ← hsh1]
    · rw [hn, hn2, hn1]
    · intro rest is es
      rw [List.append_assoc, hreads1, List.cons_append, dec_export_gen hx, hreads]
      simp [fixEx]

theorem match3_empty : Match3 { share := true } {} :=
  ⟨⟨rfl, fun _ _ h => absurd h (by simp), fun _ _ h => absurd h (by simp)⟩,
    fun _ _ h => absurd h (by simp)⟩

end DecodeAnonIface

end Silmaril.Wasm.Wac.Bridge
