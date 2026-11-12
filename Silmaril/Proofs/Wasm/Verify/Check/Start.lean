module

public import Silmaril.Proofs.Wasm.Verify.Check.Basic
public import Silmaril.Proofs.Wasm.Verify.Start.Plays
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Proofs.Wasm.Verify.Check.Instance

/-!
# Soundness of the verifier for modules with a start function

The decided invariant `cfgInB` implies `CfgIn` (`cfgInB_sound`), so a `proved` decision of
`decideSpec` on the configuration of `$instantiate` gives `StartIn` (`startIn_of_decideSpec`).
For a spec instance (`IsSpecInstance m mt I c₀`), a `proved` verdict of `checkSpec`, and of
`check` on a module with a start function, means that no play of the strategy with the
specification's instantiation phase, `I.specStrategy P c₀`, asks import `i`
(`checkSpec_sound`, `check_start_sound`), for every profile; and Core runs of the
instantiation and of later export calls never reach a callout of `i`
(`check_start_closed_world`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## The decided invariant -/

theorem mem_localsFuncs {ls : List (Option Val)} {r : Ref} (hr : some (Val.ref r) ∈ ls) {a : Nat}
    (ha : a ∈ refFuncs r) : a ∈ localsFuncs ls := by
  simp only [localsFuncs, List.mem_flatMap]
  exact ⟨some (.ref r), hr, .ref r, by simp, by simpa [valFuncs] using ha⟩

theorem frameB_sound {G fs : List Nat} {fr : Frame} (h : frameB G fs fr = true) :
    FrameIn (· ∈ G) fs fr := by
  simp only [frameB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff,
    List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1, fun r hr a ha => h.2 a (mem_localsFuncs hr ha)⟩

theorem instrB_sound {G fs : List Nat} {i : Instr} (h : instrB G fs i = true) :
    InstrIn (· ∈ G) fs i := by
  intro x hx a ha
  have hx' := List.all_eq_true.1 h x hx
  simpa [ha] using hx'

/-- Code made of source instructions holds no reference and no frame. -/
theorem plainsOf?_sound : ∀ {code : List Admin} {is : List Instr}, plainsOf? code = some is →
    codeRefs code = [] ∧ codeFrames code = [] ∧ codePlains code = is
  | [], is, h => by
    have h' : is = [] := (Option.some.inj h).symm
    subst h'
    exact ⟨by simp, by simp, by simp⟩
  | .plain i :: rest, is, h => by
    obtain ⟨is', h', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨h₁, h₂, h₃⟩ := plainsOf?_sound h'
    exact ⟨by simpa [codeRefs] using h₁, by simpa [codeFrames] using h₂,
      by simp [h₃]⟩
  | .trap :: _, _, h | .ref _ :: _, _, h | .callRefType _ :: _, _, h
  | .returnCallRefType _ :: _, _, h | .label _ _ _ :: _, _, h | .handler _ _ _ :: _, _, h
  | .frame _ _ _ :: _, _, h => by cases h

/-- **The decided invariant is sound.** -/
theorem cfgInB_sound {G fs : List Nat} {c : Config Nat} (h : cfgInB G fs c = true) :
    CfgIn (· ∈ G) fs (InstrIn (· ∈ G) fs) c := by
  simp only [cfgInB, Bool.and_eq_true] at h
  obtain ⟨⟨hs, hf⟩, hpl⟩ := h
  have hstore : StoreIn (· ∈ G) c.store :=
    mem_storeFuncs_of fun a ha => by simpa using List.all_eq_true.1 hs a ha
  obtain ⟨is, his, hall⟩ : ∃ is, plainsOf? c.code = some is ∧ is.all (instrB G fs) = true := by
    split at hpl
    · exact ⟨_, ‹_›, hpl⟩
    · cases hpl
  obtain ⟨hrefs, hframes, hplains⟩ := plainsOf?_sound his
  have hcode : CodeIn (· ∈ G) fs (InstrIn (· ∈ G) fs) c.code :=
    ⟨by simp [hrefs], by simp [hframes], fun i hi =>
      .inr (instrB_sound (List.all_eq_true.1 hall i (hplains ▸ hi)))⟩
  exact ⟨hstore, frameB_sound hf, hcode⟩

/-! ## Decisions -/

/-- A `proved` decision with the instantiation phase passed the certificate check. -/
theorem decideSpec_proved {c₀ : Config Nat} {addrs : List Nat} {i : Nat}
    (h : (decideSpec c₀ addrs i).verdict = .proved) :
    ∃ G, closedB c₀.store c₀.frame.module.funcs G = true ∧
      rootsB G (rootsOf c₀.store addrs) = true ∧ cfgInB G c₀.frame.module.funcs c₀ = true ∧
      avoidsB c₀.store G i = true := by
  unfold decideSpec at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨_, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · cases h

/-- **A `proved` decision gives `StartIn`** for the thread of the configuration. -/
theorem startIn_of_decideSpec {I : ScalarInstance} {c₀ : Config Nat} {i : Nat}
    (hlen : I.addrs.length = I.exports.length) (h : (decideSpec c₀ I.addrs i).verdict = .proved) :
    ∃ G : List Nat, StartIn I c₀.store (configThread c₀) (· ∈ G) c₀.frame.module.funcs i := by
  obtain ⟨G, hc, hr, hcfg, ha⟩ := decideSpec_proved h
  refine ⟨G, closedB_sound hc, cfgInB_sound hcfg, fun j => ?_, avoidsB_sound ha⟩
  have hj : j.val < I.addrs.length := by rw [hlen]; exact j.isLt
  have hmem : I.addr j ∈ I.addrs := by
    simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact List.getElem_mem hj
  exact rootsB_mem hr _ (by simp [rootsOf, hmem])

/-- The configuration computed by `specConfig?` is the configuration of a spec instance. -/
theorem specConfig?_eq {m : Module} {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance m mt I c₀) : specConfig? m mt = some (c₀, I.addrs) := by
  obtain ⟨c, st, hp, rfl, -, haddrs⟩ := hI.prepared
  simp only [specConfig?, hp, haddrs]

/-- A `proved` verdict of `checkSpec` on a spec instance gives `StartIn`. -/
theorem startIn_of_checkSpec {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (hI : IsSpecInstance m mt I c₀) {i : Nat}
    (h : (checkSpec m mt i).verdict = .proved) :
    ∃ (G : List Nat) (fs : List Nat), StartIn I c₀.store (configThread c₀) (· ∈ G) fs i := by
  rw [checkSpec, specConfig?_eq hI] at h
  have hlen : I.addrs.length = I.exports.length := hI.exportTypes.length_eq
  obtain ⟨G, hG⟩ := startIn_of_decideSpec hlen h
  exact ⟨G, _, hG⟩

/-- **Soundness of the verifier with the instantiation phase** (every profile): if `checkSpec`
proves "never calls import `i`", no play of the strategy of the module with the specification's
instantiation phase (`I.specStrategy P c₀`: segment initialisation and the start function, then
export calls) asks import `i`. -/
theorem checkSpec_sound {m : Module} {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance m mt I c₀) {i : Nat} (h : (checkSpec m mt i).verdict = .proved)
    (P : Profile) {p : List (Move I.E (I.F.withInst (Behaviour Val)))}
    (hp : p ∈ (I.specStrategy P c₀).toStrategy) :
    ∀ e, (.inl (.ask e) : Move I.E (I.F.withInst (Behaviour Val))) ∈ p → e.1.val ≠ i := by
  obtain ⟨G, fs, hR⟩ := startIn_of_checkSpec hI h
  exact instStrategyT_no_icall hR P hp

/-- On a module with a start function, the verifier for "never calls import `i`" is `checkSpec`
(or a pre-check fails). -/
theorem check_start_cases {m : Module} {mt : CModuleType} (hv : validate? m = some mt)
    (hst : m.start.isSome = true) (i : Nat) :
    (check m (.neverCall i)).verdict = .unknown ∨ check m (.neverCall i) = checkSpec m mt i := by
  by_cases hall : mt.imports.all isFuncImport = true
  · by_cases hi : mt.imports.length ≤ i
    · left
      simp only [check, hv, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi]
    · right
      simp only [check, hv, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, hst]
  · left
    have hall' : mt.imports.all isFuncImport = false := by simpa using hall
    simp only [check, hv, hall', Bool.not_false, ↓reduceIte]

/-- **Soundness of the verifier for modules with a start function** (every profile): if `check`
proves "never calls import `i`" for a module with a start function, then no play of the strategy
with the specification's instantiation phase asks import `i`. -/
theorem check_start_sound {m : Module} {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance m mt I c₀) (hst : m.start.isSome = true) {i : Nat}
    (h : (check m (.neverCall i)).verdict = .proved) (P : Profile)
    {p : List (Move I.E (I.F.withInst (Behaviour Val)))}
    (hp : p ∈ (I.specStrategy P c₀).toStrategy) :
    ∀ e, (.inl (.ask e) : Move I.E (I.F.withInst (Behaviour Val))) ∈ p → e.1.val ≠ i := by
  rcases check_start_cases hI.valid hst i with hc | hc
  · rw [hc] at h
    cases h
  · rw [hc] at h
    exact checkSpec_sound hI h P hp

/-- **Closed world with a start function** (every profile): if `check` proves "never calls
import `i`" for a module with a start function, then against every environment no Core run of the
configuration of `$instantiate` reaches a callout of `i`, and from any store such a run leaves,
no Core run of an export call does. -/
theorem check_start_closed_world {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (hI : IsSpecInstance m mt I c₀) (hst : m.start.isSome = true) {i : Nat}
    (h : (check m (.neverCall i)).verdict = .proved) (P : Profile) (K₀ : Env I.E) {c : Config Nat}
    (h₀ : Steps P (hostOf I.imports K₀) c₀ c) :
    (∀ E a args', decompose? c.store c.code ≠ some (E, a, i, args')) ∧
      ∀ (K : Env I.E) (j : Fin I.exports.length) (args : Typed (I.exports.get j).params)
        (d : Config Nat), Steps P (hostOf I.imports K) (invoke c.store (I.addr j) args.1) d →
        ∀ E a args', decompose? d.store d.code ≠ some (E, a, i, args') := by
  have hcs : check m (.neverCall i) = checkSpec m mt i := by
    rcases check_start_cases hI.valid hst i with hc | hc
    · rw [hc] at h
      cases h
    · exact hc
  rw [hcs] at h
  obtain ⟨G, fs, hR⟩ := startIn_of_checkSpec hI h
  have h₀' : Steps P (hostOf I.imports K₀) ((configThread c₀).config c₀.store) c := h₀
  exact ⟨(inst_closed_world hR P K₀ h₀').2.2,
    fun K j args d hd => export_closed_world hR P h₀' j args hd⟩

/-! ## The computed spec instance -/

/-- **The computed spec instance of a module is its spec instance** (`IsSpecInstance`). -/
theorem isSpecInstance_of_specInstance? {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : specInstance? m = some (mt, I, c₀)) : IsSpecInstance m mt I c₀ := by
  obtain ⟨mt', hv, h₁⟩ := Option.bind_eq_some_iff.1 h
  have hall : mt'.imports.all isFuncImport = true := by
    by_contra hne
    simp [hne] at h₁
  simp only [hall, ↓reduceIte] at h₁
  obtain ⟨imps, himps, h₂⟩ := Option.bind_eq_some_iff.1 h₁
  split at h₂
  · rename_i c st hp
    obtain ⟨exps, hexps, he⟩ := Option.map_eq_some_iff.1 h₂
    cases he
    have hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, c.store.funcs[a]? = some fi ∧
        FnType.ofDefType? fi.type = some ft) (exportFuncAddrs c.frame.module) exps :=
      (forall₂_of_mapM hexps).imp fun a ft hft => Option.bind_eq_some_iff.1 hft
    exact ⟨hv, isFuncImport_all hall, forall₂_of_mapM himps, ⟨c, st, hp, rfl, rfl, rfl⟩, hexp⟩
  · cases h₂

/-- The computed spec instance of a module. -/
noncomputable def specInstOf (m : Module) (hm : (specInstance? m).isSome = true) :
    CModuleType × ScalarInstance × Config Nat :=
  (specInstance? m).get hm

/-- **The verifier on a module with a start function**: if the module's spec instance is
computed and `check` proves "never calls import `i`", no play of the module's strategy with the
specification's instantiation phase asks `i`, every profile. All hypotheses are decidable by
kernel evaluation. -/
theorem check_start_module {m : Module} (hm : (specInstance? m).isSome = true)
    (hst : m.start.isSome = true) {i : Nat} (h : (check m (.neverCall i)).verdict = .proved)
    (P : Profile) {p : List (Move (specInstOf m hm).2.1.E
      ((specInstOf m hm).2.1.F.withInst (Behaviour Val)))}
    (hp : p ∈ ((specInstOf m hm).2.1.specStrategy P (specInstOf m hm).2.2).toStrategy) :
    ∀ e, (.inl (.ask e) : Move (specInstOf m hm).2.1.E
      ((specInstOf m hm).2.1.F.withInst (Behaviour Val))) ∈ p → e.1.val ≠ i := by
  have hI : IsSpecInstance m (specInstOf m hm).1 (specInstOf m hm).2.1 (specInstOf m hm).2.2 :=
    isSpecInstance_of_specInstance? (by simp [specInstOf])
  exact check_start_sound hI hst h P hp

end Silmaril.Wasm.Verify
