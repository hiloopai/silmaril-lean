module

public import Silmaril.Wasm.Link.PreparedObservation
public import Silmaril.Wasm.Binaryen.LinkBehaviours
public import Silmaril.Wasm.Binaryen.MergeProgram

@[expose] public section

/-! # In-order N-ary GC merge

The existing
binary linker `Link.GC.link?` and its terminal agreement are reused. `merge?`
iterates linking under one namespace; `merge_sound` compares the result against
separate instantiation with namespace-sensitive import resolution, distinct
module names and the existing GC profile. Full behavior sets include divergence
under the deterministic grow-oracle profile and a closed host.

The GC profile rejects memories, tables, tags, segments and starts. The explicit
`InitsPure` hypothesis is preserved. General start/initializer reordering, named
IR fusion, cyclic linking and arbitrary-profile behavior are not proved here.
`MergeChecked` makes the graph, namespace, profile and validation preconditions
executable. The broader target is Binaryen `version_133` (`fba5005a`),
`src/tools/wasm-merge.cpp`, but this module proves only the scoped result above.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics Link.GC

variable {H : Type}

/-! ## Layer D / Core: N-ary merge -/

/-- Point every import at one namespace. -/
def retarget (ns : String) (m : Module) : Module :=
  { m with imports := m.imports.map fun i => { i with moduleName := ns } }

/-- **N-ary merge**: iterate `link?`, the accumulated module providing every
earlier export under the namespace `"merged"`. -/
def merge? : List Module → Option Module
  | [] => none
  | m :: ms => ms.foldlM (fun acc c => link? "merged" acc (retarget "merged" c)) m

/-- Resolve imports by `(module, name)` against earlier instances' exports. -/
def resolveImportsBy (insts : List (String × ModuleInst)) (imps : List Import) :
    Option (List ExternAddr) :=
  imps.mapM fun i => do
    let p ← insts.find? (·.1 == i.moduleName)
    let e ← p.2.exports.find? (·.name == i.name)
    pure e.addr

/-- **Separate instantiation** of a program, module by module (each runs its own
initialisers and start before the next is instantiated). -/
inductive SeparateReady (P : Profile) (host : HostSemantics H) :
    Store H → List (String × ModuleInst) → List (String × Module) →
      Store H → List (String × ModuleInst) → Prop where
  | nil {s : Store H} {insts : List (String × ModuleInst)} : SeparateReady P host s insts [] s insts
  | cons {s s₁ s₂ : Store H} {insts insts' : List (String × ModuleInst)} {n : String} {m : Module}
      {rest : List (String × Module)} {xas : List ExternAddr} {mi : ModuleInst}
      (himp : resolveImportsBy insts m.imports = some xas) (hready : Ready P host s m xas s₁ mi)
      (tail : SeparateReady P host s₁ ((n, mi) :: insts) rest s₂ insts') :
      SeparateReady P host s insts ((n, m) :: rest) s₂ insts'

/-- Behaviours of export `x` of module `n` of a separately instantiated program. -/
def Program.beh (P : Profile) (host : HostSemantics H) (prog : List (String × Module))
    (n x : String) (vs : List Val) : Set (Behaviour Val) :=
  {b | ∃ (s : Store H) (insts : List (String × ModuleInst)) (mi : ModuleInst) (a : Nat),
    SeparateReady P host {} [] prog s insts ∧
    insts.lookup n = some mi ∧ exportFunc? mi x = some a ∧ b ∈ behaviours P host s a vs}

/-- Imports only refer to earlier modules (acyclic, in order). -/
def ImportsBackward (prog : List (String × Module)) : Prop :=
  ∀ (i : Nat) (p : String × Module), prog[i]? = some p →
    ∀ imp ∈ p.2.imports, ∃ j < i, ∃ q : String × Module, prog[j]? = some q ∧ q.1 = imp.moduleName

/-- Every import names an export of the earlier module it refers to (separate
instantiation resolves by `(module, name)`, `merge?` by name alone). -/
def ImportsResolve (prog : List (String × Module)) : Prop :=
  ∀ (i : Nat) (p : String × Module), prog[i]? = some p →
    ∀ imp ∈ p.2.imports, ∃ j < i, ∃ q : String × Module, prog[j]? = some q ∧
      q.1 = imp.moduleName ∧ ∃ e ∈ q.2.exports, e.name = imp.name

/-- Initialisers are pure: no data or element segments (global initialisers are
constant expressions, and in the profile only functions are imported), so
running all initialisers before all starts is unobservable. -/
def InitsPure (prog : List (String × Module)) : Prop :=
  ∀ p ∈ prog, p.2.data = [] ∧ p.2.elems = [] ∧ p.2.start = none

/-- **Two-module linking agrees with separate instantiation on full behaviour sets**,
divergence included: the lift of `separate_linked_agreement` (terminal agreement theorem). -/
theorem link_sound {namespaceName : String} {provider consumer result : Module}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL))
    {o : SingleThreaded.GrowOracle} {a : Nat} {vs : List Val}
    (valid : StoreOk sc) (typed : InvokeOk sc a vs) :
    behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost sl a vs =
      behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost sc a vs := by
  have stores := StoreRelation.separate_linked w linked hp hc hm
  obtain ⟨fi, params, results, lookup, signature, configTyped⟩ := invoke_ok valid typed
  have matching := Simulation.Matching.invoke stores lookup vs
  ext b
  constructor
  · rintro (⟨T, r, hT, hTr, rfl⟩ | ⟨rfl, hdiv⟩)
    · rcases LinkBehaviours.diverges_or_nf (invoke sc a vs) with hsd | ⟨S, hS, hSnf⟩
      · exact absurd (LinkBehaviours.diverges_forward configTyped matching hsd)
          (LinkBehaviours.no_diverges_of_nf hT (LinkObservation.result_terminal hTr))
      · by_cases hterm : ∃ r' : Result, S.code = r'.toAdmin
        · obtain ⟨r', hr'⟩ := hterm
          obtain ⟨heq, -⟩ := LinkObservation.result_agreement hS configTyped matching hr' hT hTr
          subst heq
          exact Or.inl ⟨S, _, hS, hr', rfl⟩
        · obtain ⟨T', hT', hm'⟩ := WholeSimulation.steps hS configTyped matching
          have hdec := LinkBehaviours.stuck_transfer hm'
            (WholeSimulation.hostfree_typed configTyped hS) hterm hSnf
          have heqT : T' = T := SingleThreaded.nf_unique_of_join
            (fun ha hb => SingleThreaded.Det.DStep.join' ha hb) hT' hT
            (LinkBehaviours.no_step_of_decompose hdec) (LinkObservation.result_terminal hTr)
          subst heqT
          exact absurd (by rw [hTr]; exact LinkBehaviours.decompose?_result _) hdec
    · rcases LinkBehaviours.diverges_or_nf (invoke sc a vs) with hsd | ⟨S, hS, hSnf⟩
      · exact Or.inr ⟨rfl, hsd⟩
      · exfalso
        obtain ⟨T', hT', hm'⟩ := WholeSimulation.steps hS configTyped matching
        by_cases hterm : ∃ r' : Result, S.code = r'.toAdmin
        · obtain ⟨r', hr'⟩ := hterm
          exact LinkBehaviours.no_diverges_of_nf hT'
            (LinkObservation.result_terminal (LinkObservation.paired_result hm' hr')) hdiv
        · exact LinkBehaviours.no_diverges_of_nf hT' (LinkBehaviours.no_step_of_decompose
            (LinkBehaviours.stuck_transfer hm' (WholeSimulation.hostfree_typed configTyped hS)
              hterm hSnf)) hdiv
  · rintro (⟨S, r, hS, hSr, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨T, hT, -, hTr⟩ := PreparedObservation.separate_linked_result w linked hp hc hm
        valid typed hS hSr
      exact Or.inl ⟨T, r, hT, hTr, rfl⟩
    · exact Or.inr ⟨rfl, LinkBehaviours.diverges_forward configTyped matching hdiv⟩

/-! ## Proof of `merge_sound`

By induction on the program from the front. A prefix `ps` with merge `acc`
satisfies `PrefixOk`: if `ps` instantiates separately, `acc` instantiates and the
two stores are joined by a store chain (`MergeChain.Chain`, which keeps behaviour
sets) and every module's exports agree with the merged instance's (`Inv`); and
if `acc` instantiates, so does `ps`. One more module is one more `link?`
(`MergeChain.step_forward`, `step_backward`): its imports resolve against the
earlier instances as `link?` resolves them against `acc` (`resolve`, using
`ImportsResolve` and distinct names).
-/

theorem SeparateReady.snoc {P : Profile} {host : HostSemantics H} {s s₁ s₂ : Store H}
    {insts insts₁ : List (String × ModuleInst)} {ps : List (String × Module)} {n : String}
    {m : Module} {xas : List ExternAddr} {mi : ModuleInst}
    (h : SeparateReady P host s insts ps s₁ insts₁)
    (himp : resolveImportsBy insts₁ m.imports = some xas) (hready : Ready P host s₁ m xas s₂ mi) :
    SeparateReady P host s insts (ps ++ [(n, m)]) s₂ ((n, mi) :: insts₁) := by
  revert himp hready
  induction h with
  | nil => intro himp hready; exact .cons himp hready .nil
  | cons himp' hready' _ ih => intro himp hready; exact .cons himp' hready' (ih himp hready)

theorem SeparateReady.split {P : Profile} {host : HostSemantics H} {n : String} {m : Module} :
    ∀ {ps : List (String × Module)} {s s₂ : Store H} {insts insts₂ : List (String × ModuleInst)},
      SeparateReady P host s insts (ps ++ [(n, m)]) s₂ insts₂ →
      ∃ s₁ insts₁ xas mi, SeparateReady P host s insts ps s₁ insts₁ ∧
        resolveImportsBy insts₁ m.imports = some xas ∧ Ready P host s₁ m xas s₂ mi ∧
        insts₂ = (n, mi) :: insts₁
  | [], s, s₂, insts, insts₂, h => by
    rw [List.nil_append] at h
    cases h with
    | cons himp hready tail =>
      cases tail
      exact ⟨_, _, _, _, .nil, himp, hready, rfl⟩
  | p :: ps, s, s₂, insts, insts₂, h => by
    rw [List.cons_append] at h
    cases h with
    | cons himp hready tail =>
      obtain ⟨s₁, insts₁, xas, mi, hsep, himp', hready', rfl⟩ := SeparateReady.split tail
      exact ⟨s₁, insts₁, xas, mi, .cons himp hready hsep, himp', hready', rfl⟩

namespace MergeProof

theorem merge?_snoc {ms : List Module} (hne : ms ≠ []) {q r : Module}
    (h : merge? (ms ++ [q]) = some r) :
    ∃ acc, merge? ms = some acc ∧ link? "merged" acc (retarget "merged" q) = some r := by
  cases ms with
  | nil => exact absurd rfl hne
  | cons m ms =>
    simp only [merge?, List.cons_append, List.foldlM_append, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨acc, hacc, hr⟩ := h
    refine ⟨acc, hacc, ?_⟩
    simpa using hr

/-- How the instances of a separately instantiated prefix relate to its merge:
same names in order, and each export of each module is in the merge and is
exported alike by the merged instance. -/
def Inv (ps : List (String × Module)) (insts : List (String × ModuleInst)) (acc : Module)
    (miA : ModuleInst) : Prop :=
  List.Forall₂ (fun (p : String × Module) (e : String × ModuleInst) => p.1 = e.1 ∧
    ∀ y, (p.2.exports.find? (fun x => x.name == y)).isSome →
      (acc.exports.find? (fun x => x.name == y)).isSome ∧
        MergeChain.kind e.2 y = MergeChain.kind miA y)
    ps insts.reverse

theorem forall₂_fst {R : (String × Module) → (String × ModuleInst) → Prop}
    (hR : ∀ a b, R a b → a.1 = b.1) {l : List (String × Module)} {l' : List (String × ModuleInst)}
    (h : List.Forall₂ R l l') : l'.map Prod.fst = l.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hR _ _ hab, ih]

theorem inv_keys {ps : List (String × Module)} {insts : List (String × ModuleInst)}
    {acc : Module} {miA : ModuleInst} (hinv : Inv ps insts acc miA)
    (hps : (ps.map Prod.fst).Nodup) : (insts.map Prod.fst).Nodup := by
  have h := forall₂_fst (fun _ _ h => h.1) hinv
  rw [List.map_reverse] at h
  exact List.nodup_reverse.mp (h ▸ hps)

theorem find_key {α : Type} {l : List (String × α)} (hl : (l.map Prod.fst).Nodup)
    {k : String} {v : α} (hm : (k, v) ∈ l) : l.find? (fun x => x.1 == k) = some (k, v) := by
  have hs : (l.find? (fun x => x.1 == k)).isSome := List.find?_isSome.mpr ⟨(k, v), hm, by simp⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have h1 : (x.1 == k) = true := (List.find?_eq_some_iff_append.mp hx).1
  have h2 := List.mem_of_find?_eq_some hx
  have : x = (k, v) := List.inj_on_of_nodup_map hl h2 hm (by simpa using h1)
  rw [hx, this]

theorem lookup_of_mem {α : Type} :
    ∀ {l : List (String × α)}, (l.map Prod.fst).Nodup → ∀ {k : String} {v : α},
      (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (k', v') :: l, hl, k, v, h => by
    simp only [List.map_cons, List.nodup_cons] at hl
    rcases List.mem_cons.mp h with h | h
    · cases h
      simp [List.lookup]
    · have hneq : k ≠ k' := fun e => hl.1 (by rw [← e]; exact List.mem_map_of_mem h)
      have hb : (k == k') = false := by simp [hneq]
      simp only [List.lookup, hb]
      exact lookup_of_mem hl.2 h

/-- **Imports resolve alike**: separate instantiation resolves the next module's
imports against the earlier instances to the addresses `link?` resolves them to. -/
theorem resolve {prog ps rest : List (String × Module)} {n : String} {q acc r : Module}
    (hprog : prog = ps ++ (n, q) :: rest) (hres : ImportsResolve prog)
    (hnames : (prog.map Prod.fst).Nodup)
    (w : Recipe.Assembly "merged" acc (MergeChain.renamespace "merged" q) r)
    {sA : Store H} {miA : ModuleInst}
    (hA : Execution.Core.prepare? evalConst? ({} : Store H) acc (Preparation.imports []) =
      some (⟨sA, { module := miA }, []⟩, none))
    {insts : List (String × ModuleInst)} (hinv : Inv ps insts acc miA) :
    resolveImportsBy insts q.imports = some (Preparation.imports
      (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) := by
  have hps : (ps.map Prod.fst).Nodup := by
    rw [hprog, List.map_append] at hnames
    exact (List.nodup_append.mp hnames).1
  have hkeys := inv_keys hinv hps
  unfold Inv at hinv
  unfold resolveImportsBy
  apply MergeChain.mapM_of_forall₂
  apply MergeChain.forall₂_of_getElem?
  · simp [Preparation.imports, w.imports_length, MergeChain.renamespace]
  · intro j imp a hj ha
    obtain ⟨f, hf, hk⟩ := MergeChain.import_kind w hA hj
    have hk2 : MergeChain.kind miA imp.name =
        some (some (({} : Store H).funcs.length + f.toNat)) := hk
    have ha' : a = .func (({} : Store H).funcs.length + f.toNat) := by
      simp only [Preparation.imports, List.map_map, List.getElem?_map, hf, Option.map_some,
        Option.some.injEq, Function.comp_apply] at ha
      exact ha.symm
    subst ha'
    have hq : prog[ps.length]? = some (n, q) := by
      rw [hprog, List.getElem?_append_right (le_refl _), Nat.sub_self]
      rfl
    obtain ⟨jj, hjj, p', hp', hname, e, he, hen⟩ :=
      hres ps.length (n, q) hq imp (List.mem_of_getElem? hj)
    have hp'' : ps[jj]? = some p' := by
      rw [hprog, List.getElem?_append_left hjj] at hp'
      exact hp'
    obtain ⟨⟨n', mi'⟩, hpart, hn', hkind⟩ := MergeChain.forall₂_lookup_left hinv hp''
    have hfy : (p'.2.exports.find? (fun x => x.name == imp.name)).isSome :=
      List.find?_isSome.mpr ⟨e, he, by simp [hen]⟩
    obtain ⟨-, hk'⟩ := hkind imp.name hfy
    have hk3 : MergeChain.kind mi' imp.name =
        some (some (({} : Store H).funcs.length + f.toNat)) := hk'.trans hk2
    have hn'' : n' = imp.moduleName := hn'.symm.trans hname
    have hmem : (imp.moduleName, mi') ∈ insts := by
      rw [← hn'']
      exact List.mem_reverse.mp (List.mem_of_getElem? hpart)
    have hfind := find_key hkeys hmem
    unfold MergeChain.kind at hk3
    obtain ⟨xi, hxi, haddr⟩ : ∃ xi, mi'.exports.find? (fun e => e.name == imp.name) = some xi ∧
        MergeChain.addrFunc xi.addr = some (({} : Store H).funcs.length + f.toNat) := by
      revert hk3
      cases mi'.exports.find? (fun e => e.name == imp.name) with
      | none => intro h; cases h
      | some xi => intro h; exact ⟨xi, rfl, Option.some.inj h⟩
    have hxa : xi.addr = .func (({} : Store H).funcs.length + f.toNat) := by
      revert haddr
      cases xi.addr <;> simp [MergeChain.addrFunc]
    simp only [hfind, hxi, hxa, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- What the merge `acc` of a prefix `ps` of the program satisfies. -/
def PrefixOk (H : Type) (P : Profile) (ps : List (String × Module)) (acc : Module) : Prop :=
  Link.GC.inProfile acc = true ∧
  (∀ {s : Store H} {insts : List (String × ModuleInst)},
    SeparateReady P (SingleThreaded.Det.noHost (H := H)) {} [] ps s insts →
    ∃ sA miA, Execution.Core.prepare? evalConst? ({} : Store H) acc (Preparation.imports []) =
        some (⟨sA, { module := miA }, []⟩, none) ∧
      Ready P (SingleThreaded.Det.noHost (H := H)) {} acc [] sA miA ∧
      MergeChain.Chain s sA ∧ Inv ps insts acc miA) ∧
  (∀ {cl : Config H} {st : Option FuncIdx}, (∃ mt, ModuleOk acc mt) →
    Execution.Core.prepare? evalConst? ({} : Store H) acc (Preparation.imports []) =
      some (cl, st) →
    ∃ (s : Store H) (insts : List (String × ModuleInst)),
      SeparateReady P (SingleThreaded.Det.noHost (H := H)) {} [] ps s insts)

theorem base_sound {P : Profile} {n : String} {m : Module} (hm : Link.GC.inProfile m = true)
    (himp : m.imports = []) : PrefixOk H P [(n, m)] m := by
  refine ⟨hm, ?_, ?_⟩
  · intro s insts h
    obtain ⟨s₁, insts₁, xas, mi, h0, himp', hready, rfl⟩ := SeparateReady.split (ps := []) h
    cases h0
    rw [himp] at himp'
    have hx : xas = [] := by simpa [resolveImportsBy] using himp'.symm
    subst hx
    have hp := MergeChain.prepare_of_ready (as := []) hm hready
    exact ⟨_, _, hp, hready, .refl _,
      List.Forall₂.cons ⟨rfl, fun y hy => ⟨hy, rfl⟩⟩ List.Forall₂.nil⟩
  · intro cl st hok hp
    obtain ⟨mt, hmt⟩ := hok
    obtain ⟨-, -, -, -, -, hloc, hcode, hst⟩ := Preparation.prepare_allocation hm hp
    rcases cl with ⟨sl, ⟨loc, mi⟩, code⟩
    have h1 : loc = [] := hloc
    have h2 : code = [] := hcode
    subst h1 h2 hst
    have hready := MergeChain.ready_of_prepare (P := P) (host := SingleThreaded.Det.noHost)
      (MergeChain.valid_closed hmt himp) hp
    exact ⟨sl, [(n, mi)], SeparateReady.cons (by rw [himp]; rfl) hready .nil⟩

theorem step_sound {P : Profile} {prog ps rest : List (String × Module)} {n : String}
    {q acc r : Module} (hprog : prog = ps ++ (n, q) :: rest) (hres : ImportsResolve prog)
    (hnames : (prog.map Prod.fst).Nodup)
    (hl : link? "merged" acc (retarget "merged" q) = some r) (ih : PrefixOk H P ps acc) :
    PrefixOk H P (ps ++ [(n, q)]) r := by
  obtain ⟨w⟩ := Link.GC.link?_recipe hl
  have w' : Recipe.Assembly "merged" acc (MergeChain.renamespace "merged" q) r := w
  have hl' : link? "merged" acc (MergeChain.renamespace "merged" q) = some r := hl
  obtain ⟨-, ihA, ihB⟩ := ih
  refine ⟨MergeChain.result_profile w', ?_, ?_⟩
  · intro s' insts' h
    obtain ⟨s, insts, xas, miQ, hsep, himp, hready, rfl⟩ := SeparateReady.split h
    obtain ⟨sA, miA, hA, -, hchain, hinv⟩ := ihA hsep
    rw [resolve hprog hres hnames w' hA hinv] at himp
    cases himp
    have hq : Link.GC.inProfile q = true := by
      rw [← MergeChain.inProfile_renamespace "merged" q]; exact w'.consumerProfile
    have hQ := MergeChain.prepare_of_ready hq hready
    obtain ⟨sl, miR, hR, hchain', hk1, hk2⟩ := MergeChain.step_forward w' hl' hA hchain hQ
    obtain ⟨mt, hmt⟩ := Link.GC.link?_valid hl
    have hready' := MergeChain.ready_of_prepare (P := P) (host := SingleThreaded.Det.noHost)
      (MergeChain.valid_closed hmt (MergeChain.result_imports w')) hR
    refine ⟨sl, miR, hR, hready', hchain', ?_⟩
    unfold Inv at hinv ⊢
    rw [List.reverse_cons]
    refine MergeChain.forall₂_append' (List.Forall₂.imp ?_ hinv)
      (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)
    · rintro p e ⟨h1, h2⟩
      refine ⟨h1, fun y hy => ?_⟩
      obtain ⟨ha, hk⟩ := h2 y hy
      exact ⟨MergeChain.find_result w' (.inl ha), hk.trans (hk1 y ha).symm⟩
    · intro y hy
      exact ⟨MergeChain.find_result w' (.inr hy), hk2 y hy⟩
  · intro cl st _ hR
    obtain ⟨cp, startP, hp, -⟩ := MergeChain.separate_exists w' hl' hR
    obtain ⟨s, insts, hsep⟩ := ihB ⟨_, validate?_sound w'.providerValidation⟩ hp
    obtain ⟨sA, miA, hA, -, hchain, hinv⟩ := ihA hsep
    obtain ⟨s', miQ, hQ, hvQ⟩ := MergeChain.step_backward w' hl' hA hchain hR
    have hready := MergeChain.ready_of_prepare (P := P) (host := SingleThreaded.Det.noHost) hvQ hQ
    exact ⟨s', _, SeparateReady.snoc hsep (resolve hprog hres hnames w' hA hinv) hready⟩

theorem prefix_sound {P : Profile} {prog : List (String × Module)}
    (hback : ImportsBackward prog) (hres : ImportsResolve prog)
    (hprof : ∀ p ∈ prog, Link.GC.inProfile p.2 = true) (hnames : (prog.map Prod.fst).Nodup) :
    ∀ (rs : List (String × Module)), rs ≠ [] → ∀ {rest : List (String × Module)} {acc : Module},
      prog = rs.reverse ++ rest → merge? (rs.reverse.map Prod.snd) = some acc →
      PrefixOk H P rs.reverse acc := by
  intro rs
  induction rs with
  | nil => intro h; exact absurd rfl h
  | cons q rs ih =>
    intro _ rest acc hprog hmerge
    rw [List.reverse_cons] at hprog hmerge ⊢
    rcases q with ⟨n, m⟩
    by_cases hrs : rs = []
    · subst hrs
      simp only [List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
        List.singleton_append] at hprog hmerge ⊢
      simp only [merge?, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hmerge
      subst hmerge
      have hm : Link.GC.inProfile m = true := hprof (n, m) (by rw [hprog]; simp)
      have himp : m.imports = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro imp himp
        obtain ⟨j, hj, -⟩ := hback 0 (n, m) (by rw [hprog]; rfl) imp himp
        exact absurd hj (Nat.not_lt_zero _)
      exact base_sound hm himp
    · simp only [List.map_append, List.map_cons, List.map_nil] at hmerge
      have hne : rs.reverse.map Prod.snd ≠ [] := by simpa using hrs
      obtain ⟨acc', hacc', hl⟩ := merge?_snoc hne hmerge
      have ih' := @ih hrs ((n, m) :: rest) acc' (by rw [hprog]; simp) hacc'
      exact step_sound (rest := rest) (by rw [hprog]; simp) hres hnames hl ih'

theorem export_agree {ps : List (String × Module)} {insts : List (String × ModuleInst)}
    {acc : Module} {miA : ModuleInst} (hinv : Inv ps insts acc miA)
    (hnames : (ps.map Prod.fst).Nodup) {n x : String}
    (hx : ∃ p ∈ ps, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    (∃ mi, insts.lookup n = some mi) ∧
      ∀ mi, insts.lookup n = some mi → exportFunc? mi x = exportFunc? miA x := by
  have hkeys := inv_keys hinv hnames
  unfold Inv at hinv
  obtain ⟨p, hp, hpn, e, he, hen⟩ := hx
  obtain ⟨⟨n', mi⟩, hmem, hn', hkind⟩ := MergeChain.forall₂_mem_left hinv p hp
  have hn'' : n' = n := hn'.symm.trans hpn
  have hmem' : (n, mi) ∈ insts := by
    rw [← hn'']
    exact List.mem_reverse.mp hmem
  have hlook := lookup_of_mem hkeys hmem'
  have hfx : (p.2.exports.find? (fun y => y.name == x)).isSome :=
    List.find?_isSome.mpr ⟨e, he, by simp [hen]⟩
  obtain ⟨-, hk⟩ := hkind x hfx
  have hk' : MergeChain.kind mi x = MergeChain.kind miA x := hk
  refine ⟨⟨mi, hlook⟩, fun mi' hmi' => ?_⟩
  rw [hlook, Option.some.injEq] at hmi'
  subst hmi'
  rw [MergeChain.exportFunc_kind, MergeChain.exportFunc_kind, hk']

theorem prep_inj {s₁ s₂ : Store H} {m₁ m₂ : ModuleInst}
    (h : (some (⟨s₁, { module := m₁ }, []⟩, none) : Option (Config H × Option FuncIdx)) =
      some (⟨s₂, { module := m₂ }, []⟩, none)) : s₁ = s₂ ∧ m₁ = m₂ := by
  cases h
  exact ⟨rfl, rfl⟩

end MergeProof

/-- **N-ary merge is sound** for an acyclic, in-order program in the linker's
profile with pure initialisers: every export of every module behaves in the
merged module as in the separately instantiated program. -/
theorem merge_sound {prog : List (String × Module)} {r : Module}
    (h : merge? (prog.map Prod.snd) = some r) (hback : ImportsBackward prog)
    -- FLAG(statement-change): added `hres`. Without it the statement is false
    -- (`MergeCounterexamples.merge_sound_false`): an import `("A", "g")` with `A`
    -- lacking `g` fails separate instantiation, but `merge?` resolves it by name.
    (hres : ImportsResolve prog)
    (hprof : ∀ p ∈ prog, inProfile p.2 = true) (hinit : InitsPure prog)
    (hnames : (prog.map Prod.fst).Nodup)
    {o : SingleThreaded.GrowOracle} {n x : String} {vs : List Val}
    (hx : ∃ p ∈ prog, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh (SingleThreaded.profile o) (SingleThreaded.Det.noHost (H := H)) prog n x vs =
      (moduleEntryPoints (SingleThreaded.profile o) (SingleThreaded.Det.noHost (H := H))
        closedEnv).beh r x vs := by
  let _ := hinit
  have hne : prog ≠ [] := by
    rintro rfl
    obtain ⟨p, hp, -⟩ := hx
    simp at hp
  have hpre := MergeProof.prefix_sound (H := H) (P := SingleThreaded.profile o) hback hres hprof
    hnames prog.reverse (by simpa using hne) (rest := []) (by simp) (by simpa using h)
  rw [List.reverse_reverse] at hpre
  obtain ⟨hprofR, hA, hB⟩ := hpre
  ext b
  simp only [Program.beh, moduleEntryPoints, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, insts, mi, a, hsep, hlook, hexp, hb⟩
    obtain ⟨sA, miA, -, hready, hchain, hinv⟩ := hA hsep
    refine ⟨{}, [], sA, miA, a, by unfold closedEnv; exact ⟨rfl, rfl⟩, hready, ?_, ?_⟩
    · rw [← hexp]
      exact ((MergeProof.export_agree hinv hnames hx).2 mi hlook).symm
    · rw [MergeChain.Chain.behaviours hchain]
      exact hb
  · rintro ⟨s0, xas, s', mi, a, ⟨rfl, rfl⟩, hready, hexp, hb⟩
    have hprep := MergeChain.prepare_of_ready (as := []) hprofR hready
    obtain ⟨s, insts, hsep⟩ := hB (MergeChain.moduleOk_of_ready hready) hprep
    obtain ⟨sA, miA, hprepA, -, hchain, hinv⟩ := hA hsep
    obtain ⟨rfl, rfl⟩ := MergeProof.prep_inj (hprep.symm.trans hprepA)
    obtain ⟨mi_n, hlook⟩ := (MergeProof.export_agree hinv hnames hx).1
    refine ⟨s, insts, mi_n, a, hsep, hlook, ?_, ?_⟩
    · rw [(MergeProof.export_agree hinv hnames hx).2 mi_n hlook]
      exact hexp
    · rw [← MergeChain.Chain.behaviours hchain]
      exact hb


end Silmaril.Wasm.Binaryen
