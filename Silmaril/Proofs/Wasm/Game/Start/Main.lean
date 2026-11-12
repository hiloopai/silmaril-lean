module

public import Silmaril.Proofs.Wasm.Game.Start.Export
public import Silmaril.Proofs.Wasm.Game.Start.Instance
public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Main

/-!
# Adequacy of instantiation and of the calls that follow it: proofs

For every profile `P`, an instance well formed at `s` whose start function (if
any) has type `[] → []`, and an environment `K` throwing only existing
exceptions:

* `adequacy_inst`: the instantiation observations of the closed program
  `I.closedInst P s start K` are the closed-world behaviours of the start
  phase (`returns []` exactly when the start function may return, a trap or
  an uncaught exception exactly when it may fail so, `diverges` exactly when
  it may diverge);
* `traces_after_inst`, `div_after_inst`: after a successful instantiation the
  closed program plays (and diverges) exactly as the closed program
  `I.closedD P s' K` at a store `s'` that the start phase may return at;
* `adequacy_after_inst`: hence the observations of an export call right after
  instantiation are the Core behaviours of the call at the stores the start
  phase may leave: Core instantiation-then-invocation.

Typing: the start function as the export `0` of `plusStart I a` (exports
`startType :: I.exports`), so that M2's typing results (`result_typed`,
`wellFormed_after_run`) apply to the start run.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Start

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.ScalarInstance Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-! ## Plays -/

section Plays

variable {E F : Sig.{0}}

/-- A play of `Strategy.ofLTS L` ending in a Proponent move is a trace of `L` (restated from
`Silmaril.Proofs.Games.Inst.Basic`, layout rules). -/
theorem trace_of_mem_ofLTS {L : LTS E F} {s : List (Move E F)} {o : Move E F}
    (h : s ++ [o] ∈ Strategy.ofLTS L) (ho : o.IsP) : s ++ [o] ∈ L.Traces := by
  obtain ⟨-, u, hu, hp⟩ := Strategy.mem_generate.1 h
  have hO : ∀ p₀ o', s ++ [o] = p₀ ++ [o'] → ¬ o'.IsO := by
    intro p₀ o' he
    obtain ⟨-, h'⟩ := List.append_inj' he rfl
    obtain rfl : o = o' := by simpa using h'
    exact Move.not_isO_of_isP ho
  rcases hu with rfl | ⟨hu, -⟩
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · simpa using hp.length_le
    · exact (hO p₀ o' he ho').elim
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · exact LTS.traces_of_prefix hu hp
    · exact (hO p₀ o' he ho').elim

/-- Membership of a legal play ending in a Proponent move is a trace. -/
theorem mem_ofLTS_iff {L : LTS E F} {s : List (Move E F)} {o : Move E F} (ho : o.IsP)
    (hl : Legal (s ++ [o])) : s ++ [o] ∈ Strategy.ofLTS L ↔ s ++ [o] ∈ L.Traces :=
  ⟨fun h => trace_of_mem_ofLTS h ho, fun h => Strategy.mem_ofLTS_of_mem_traces h hl⟩

/-- Positions of `E ↠ F` as positions of `E ↠ F.withInst R`. -/
def liftPos {R : Type} : Pos E F → Pos E (F.withInst R)
  | .idle => .idle
  | .run q => .run (some q)
  | .wait q m => .wait (some q) m

theorem step_lift {R : Type} {x y : Pos E F} {o : Move E F} (h : Silmaril.Games.Step x o y) :
    Silmaril.Games.Step (liftPos (R := R) x) (liftMove o) (liftPos y) := by
  cases h with
  | ask q => exact Silmaril.Games.Step.ask (E := E) (F := F.withInst R) (some q)
  | call q m => exact Silmaril.Games.Step.call (E := E) (F := F.withInst R) (some q) m
  | reply q m n => exact Silmaril.Games.Step.reply (E := E) (F := F.withInst R) (some q) m n
  | ret q r => exact Silmaril.Games.Step.ret (E := E) (F := F.withInst R) (some q) r

theorem step_unlift {R : Type} {x : Pos E F} {o : Move E F} {z : Pos E (F.withInst R)}
    (h : Silmaril.Games.Step (liftPos x) (liftMove o) z) :
    ∃ y, z = liftPos y ∧ Silmaril.Games.Step x o y := by
  rcases x with _ | q | ⟨q, m⟩ <;> rcases o with (⟨m'⟩ | ⟨m', n⟩) | (⟨q'⟩ | ⟨q', r⟩) <;>
    cases h
  all_goals first
    | exact ⟨_, rfl, .ask _⟩
    | exact ⟨_, rfl, .call _ _⟩
    | exact ⟨_, rfl, .reply _ _ _⟩
    | exact ⟨_, rfl, .ret _ _⟩

theorem path_lift {R : Type} {x y : Pos E F} {p : List (Move E F)} (h : Path x p y) :
    Path (liftPos (R := R) x) (p.map liftMove) (liftPos y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (step_lift hs) ih

theorem path_unlift {R : Type} {x : Pos E F} {p : List (Move E F)} {z : Pos E (F.withInst R)}
    (h : Path (liftPos x) (p.map liftMove) z) : ∃ y, z = liftPos y ∧ Path x p y := by
  induction p generalizing x with
  | nil => cases h; exact ⟨x, rfl, .nil _⟩
  | cons o p ih =>
    cases h with
    | cons hs hp =>
      obtain ⟨y, rfl, hy⟩ := step_unlift hs
      obtain ⟨y', rfl, hy'⟩ := ih hp
      exact ⟨y', rfl, .cons hy hy'⟩

/-- The instantiation exchange, as a path. -/
theorem path_inst {R : Type} (a : InstAns R) :
    Path (E := E) (F := F.withInst R) .idle [askInst, ansInst a] .idle :=
  .cons (Silmaril.Games.Step.ask (E := E) (F := F.withInst R) none)
    (.cons (Silmaril.Games.Step.ret (E := E) (F := F.withInst R) none a) (.nil _))

theorem legal_inst {R : Type} (a : InstAns R) :
    Legal ([askInst, ansInst a] : List (Move E (F.withInst R))) := ⟨_, path_inst a⟩

/-- The paths past a successful instantiation. -/
theorem path_after_inst_iff {R : Type} {p : List (Move E F)} {q' : (F.withInst R).Op} :
    Path .idle ([askInst, ansInst .ready] ++ p.map liftMove) (.run q') ↔
      ∃ q, q' = some q ∧ Path .idle p (.run q) := by
  constructor
  · intro h
    obtain ⟨y, h₁, h₂⟩ := Path.of_append h
    obtain rfl : y = .idle := (Path.det h₁ (path_inst .ready)).symm ▸ rfl
    obtain ⟨y', hy', hp⟩ := path_unlift (x := .idle) h₂
    rcases y' with _ | q | ⟨q, m⟩
    · cases hy'
    · cases hy'
      exact ⟨q, rfl, hp⟩
    · cases hy'
  · rintro ⟨q, rfl, hp⟩
    exact (path_inst .ready).append (path_lift (R := R) hp)

end Plays

/-! ## The start function as an export -/

/-- The instance with the start function at `a` as an extra export `0`. -/
def plusStart (I : ScalarInstance) (a : Nat) : ScalarInstance :=
  { I with exports := startType :: I.exports, addrs := a :: I.addrs }

/-- The call of the start function, as an export call of `plusStart I a`. -/
def startOp (I : ScalarInstance) (a : Nat) : (plusStart I a).F.Op :=
  ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨[], .nil⟩⟩

variable {I : ScalarInstance} {P : Profile} {s : Store Nat} {start : Option Nat}
  {K : Silmaril.Wasm.Game.Env I.E}

theorem plusStart_wellFormed {a : Nat} (hw : I.WellFormed s) (ha : StartTyped s a) :
    (plusStart I a).WellFormed s where
  storeOk := hw.storeOk
  addrs_length := congrArg (· + 1) hw.addrs_length
  export_type j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ha
    · exact hw.export_type j
  host_type := hw.host_type

theorem wellFormed_of_plusStart {a : Nat} (hw : (plusStart I a).WellFormed s) :
    I.WellFormed s where
  storeOk := hw.storeOk
  addrs_length := Nat.succ.inj hw.addrs_length
  export_type j := hw.export_type j.succ
  host_type := hw.host_type

/-- Without a start function, the start phase has finished. -/
theorem startConfig_none_code : (startConfig s none).code = (Result.values []).toAdmin := rfl

/-- Without a start function, the start phase has no step. -/
theorem steps_startConfig_none {host : HostSemantics Nat} {c' : Config Nat}
    (h : Steps P host (startConfig s none) c') : c' = startConfig s none := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, hst, -⟩
  · rfl
  · exact absurd hst (Step.not_result startConfig_none_code)

/-- **Without a start function, the start phase returns at the store unchanged.** -/
theorem startsTo_none {host : HostSemantics Nat} {s' : Store Nat} :
    StartsTo P host s none s' ↔ s' = s := by
  constructor
  · rintro ⟨c', hc', -, rfl⟩
    rw [steps_startConfig_none hc']
    rfl
  · rintro rfl
    exact ⟨_, .refl, startConfig_none_code, rfl⟩

/-- A typed answer of the start type is `values []`, a trap or an exception. -/
theorem result_of_startType {r : Result} {w : Answer startType}
    (h : Answer.ofResult? startType r = some w) :
    r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  have hr : w.toResult = r := Answer.toResult_of_ofResult? h
  rcases w with ⟨vs, hvs⟩ | _ | x
  · have hvs' : vs = [] := List.forall₂_nil_left_iff.1 hvs
    exact .inl (hr.symm.trans (congrArg Result.values hvs'))
  · exact .inr (.inl hr.symm)
  · exact .inr (.inr ⟨x, hr.symm⟩)

/-- **Typed start results.** A result reached by the start phase is `values []`, a trap or
an exception. -/
theorem start_result_cases (hw : I.WellFormed s) (hst : ∀ a ∈ start, StartTyped s a)
    (hK : ThrowsBelow K s.exns.length) {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) (startConfig s start) c')
    (final : c'.code = r.toAdmin) : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  cases start with
  | none =>
    have hc : c' = startConfig s none := steps_startConfig_none run
    have hr : r.toAdmin = (Result.values []).toAdmin := final.symm.trans (hc ▸ rfl)
    exact .inl (result_toAdmin_injective hr)
  | some a =>
    have hw' : (plusStart I a).WellFormed s := plusStart_wellFormed hw (hst a rfl)
    obtain ⟨w, hw''⟩ := result_typed (I := plusStart I a) hw' hK (f := startOp I a) run final
    exact result_of_startType hw''

/-- The store left by a start phase returning `values []` is well formed. -/
theorem start_wellFormed (hw : I.WellFormed s) (hst : ∀ a ∈ start, StartTyped s a)
    (hK : ThrowsBelow K s.exns.length) {s' : Store Nat}
    (h : StartsTo P (hostOf I.imports K) s start s') :
    I.WellFormed s' ∧ ThrowsBelow K s'.exns.length := by
  cases start with
  | none =>
    obtain rfl : s' = s := startsTo_none.1 h
    exact ⟨hw, hK⟩
  | some a =>
    obtain ⟨c', run, final, rfl⟩ := h
    have hw' : (plusStart I a).WellFormed s := plusStart_wellFormed hw (hst a rfl)
    obtain ⟨h₁, h₂⟩ := wellFormed_after_run (I := plusStart I a) hw' hK (f := startOp I a) run final
    exact ⟨wellFormed_of_plusStart h₁, h₂⟩

/-! ## Typing of an arbitrary instantiation thread -/

/-- **Typed instantiation results.** A result reached by an instantiation thread typed at `[]`
is `values []`, a trap or an exception. -/
theorem startT_result_cases {t₀ : Thread} (hw : I.WellFormed s)
    (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length) {c' : Config Nat}
    {r : Result} (run : Steps P (hostOf I.imports K) (t₀.config s) c')
    (final : c'.code = r.toAdmin) : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  have h0 : RunInv s [] (t₀.config s) :=
    ⟨hok, by rw [Thread.config_store], by rw [Thread.config_store]; exact Extend.refl hw.storeOk⟩
  have hend : RunInv s [] c' := RunInv.steps hw hK run h0
  cases r with
  | trap => exact .inr (.inl rfl)
  | throw x => exact .inr (.inr ⟨x, rfl⟩)
  | values vs =>
    have hok' : ConfigOk c' (([] : List ScalarType).map ScalarType.toC) := hend.1
    have hvs : List.Forall₂ ScalarType.HasVal [] vs := hasVal_of_configOk hok' final
    have hnil : vs = [] := List.forall₂_nil_left_iff.1 hvs
    exact .inl (by rw [hnil])

/-- The store left by an instantiation thread typed at `[]` returning `values []` is well
formed. -/
theorem startT_wellFormed {t₀ : Thread} (hw : I.WellFormed s)
    (hok : ConfigOk (t₀.config s) []) (hK : ThrowsBelow K s.exns.length) {s' : Store Nat}
    (h : StartsToT P (hostOf I.imports K) s t₀ s') :
    I.WellFormed s' ∧ ThrowsBelow K s'.exns.length := by
  obtain ⟨c', run, -, rfl⟩ := h
  have h0 : RunInv s [] (t₀.config s) :=
    ⟨hok, by rw [Thread.config_store], by rw [Thread.config_store]; exact Extend.refl hw.storeOk⟩
  obtain ⟨hok', hfun, hext⟩ : RunInv s [] c' := RunInv.steps hw hK run h0
  have hw' : I.WellFormed c'.store :=
    WellFormed.of_funcs_eq hw (SingleThreaded.ConfigOk.storeOk hok') hfun
  exact ⟨hw', throwsBelow_mono hK hext.exns.1⟩

/-! ## Adequacy of instantiation -/

section Thread

variable {t₀ : Thread}

theorem mem_inst_iff (a : InstAns (Behaviour Val)) :
    [askInst, ansInst a] ∈ (I.closedInstT P s t₀ K).toStrategy ↔
      [askInst, ansInst a] ∈ (CI I P s t₀ K).Traces :=
  mem_ofLTS_iff (s := [askInst]) trivial (legal_inst a)

theorem instAnsOf_ready {r : Result} : InstAnsOf r .ready ↔ r = .values [] := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact h
    · cases h
  · intro h
    exact .inl ⟨h, rfl⟩

theorem instAnsOf_fail {r : Result} {b : Behaviour Val} :
    InstAnsOf r (.fail b) ↔ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour := by
  constructor
  · rintro (⟨-, h⟩ | ⟨h, h'⟩)
    · cases h
    · exact ⟨h, InstAns.fail.inj h'⟩
  · rintro ⟨h, rfl⟩
    exact .inr ⟨h, rfl⟩

/-- Instantiation succeeds exactly when the instantiation thread may return. -/
theorem instReady_closedInstT_iff :
    (I.closedInstT P s t₀ K).InstReady ↔
      ∃ (c' : Config Nat), Steps P (hostOf I.imports K) (t₀.config s) c' ∧
        c'.code = (Result.values []).toAdmin := by
  refine (mem_inst_iff .ready).trans (traces_inst_iff.trans ?_)
  constructor
  · rintro ⟨c', r, h₁, h₂, h₃⟩
    exact ⟨c', h₁, instAnsOf_ready.1 h₃ ▸ h₂⟩
  · rintro ⟨c', h₁, h₂⟩
    exact ⟨c', _, h₁, h₂, instAnsOf_ready.2 rfl⟩

/-- Instantiation fails with `b` exactly when the instantiation thread may trap or throw, read
as `b`. -/
theorem instFails_closedInstT_iff (b : Behaviour Val) :
    (I.closedInstT P s t₀ K).InstFails b ↔
      ∃ (c' : Config Nat) (r : Result), Steps P (hostOf I.imports K) (t₀.config s) c' ∧
        c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour := by
  refine (mem_inst_iff (.fail b)).trans (traces_inst_iff.trans ?_)
  constructor
  · rintro ⟨c', r, h₁, h₂, h₃⟩
    exact ⟨c', r, h₁, h₂, instAnsOf_fail.1 h₃⟩
  · rintro ⟨c', r, h₁, h₂, h₃⟩
    exact ⟨c', r, h₁, h₂, instAnsOf_fail.2 h₃⟩

/-- **Adequacy of instantiation for an arbitrary instantiation thread, every profile**, given
that its results are typed at `[]`. -/
theorem adequacy_instT_of
    (hcases : ∀ {c' : Config Nat} {r : Result}, Steps P (hostOf I.imports K) (t₀.config s) c' →
      c'.code = r.toAdmin → r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x) :
    instObs (I.closedInstT P s t₀ K) = behavioursOf P (hostOf I.imports K) (t₀.config s) := by
  ext b
  show ((b = .returns [] ∧ (I.closedInstT P s t₀ K).InstReady) ∨
      (I.closedInstT P s t₀ K).InstFails b) ∨
      (b = .diverges ∧ (I.closedInstT P s t₀ K).InstDiverges) ↔
    (∃ (c' : Config Nat) (r : Result), Steps P (hostOf I.imports K) (t₀.config s) c' ∧
      c'.code = r.toAdmin ∧ b = r.toBehaviour) ∨
      (b = .diverges ∧ Diverges P (hostOf I.imports K) (t₀.config s))
  rw [instReady_closedInstT_iff, instFails_closedInstT_iff b, ← div_inst_iff]
  constructor
  · rintro ((⟨hb, c', h₁, h₂⟩ | ⟨c', r, h₁, h₂, -, hb⟩) | hd)
    · exact .inl ⟨c', _, h₁, h₂, hb⟩
    · exact .inl ⟨c', r, h₁, h₂, hb⟩
    · exact .inr hd
  · rintro (⟨c', r, h₁, h₂, hb⟩ | hd)
    · have hcases' : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := hcases h₁ h₂
      have hb' : r = .values [] → b = .returns [] := fun hr => hb.trans (by rw [hr]; rfl)
      exact hcases'.elim (fun hr => .inl (.inl ⟨hb' hr, c', h₁, hr ▸ h₂⟩))
        (fun hr => .inl (.inr ⟨c', r, h₁, h₂, hr, hb⟩))
    · exact .inr hd

/-- **Adequacy of instantiation for an instantiation thread typed at `[]`, every profile.** -/
theorem adequacy_instT (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) [])
    (hK : ThrowsBelow K s.exns.length) :
    instObs (I.closedInstT P s t₀ K) = behavioursOf P (hostOf I.imports K) (t₀.config s) :=
  adequacy_instT_of fun h₁ h₂ => startT_result_cases hw hok hK h₁ h₂

/-! ## After instantiation -/

/-- The closed instance system denotes the closed program. -/
theorem cmp_denotes (s' : Store Nat) :
    (Cmp I P s' K).Denotes (I.closedWith P s' K) :=
  LTS.Denotes.comp (Silmaril.Proofs.Wasm.Game.Env.denotes_dlts K) (denotes_dlts P s')

/-- **Plays after a successful instantiation, every profile.** -/
theorem traces_after_instT (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (CI I P s t₀ K).Traces ↔
      ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧ p ∈ I.closedWith P s' K := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c', h₁, h₂, hr⟩ := run_ready_iff.1 hz
    obtain ⟨y, -, hy⟩ :=
      ((cmpB I P s c'.store t₀ K).run_iff (x := (Cmp I P c'.store K).init) (w := p)).1 hr
    exact ⟨c'.store, ⟨c', h₁, h₂, rfl⟩, (cmp_denotes c'.store p).1 ⟨y, hy⟩⟩
  · rintro ⟨_, ⟨c', h₁, h₂, rfl⟩, hp⟩
    obtain ⟨y, hy⟩ := (cmp_denotes c'.store p).2 hp
    have hr : (CI I P s t₀ K).Run (none, .ready c'.store) (p.map liftMove)
        ((cmpB I P s c'.store t₀ K).φ y) :=
      (cmpB I P s c'.store t₀ K).run_fwd hy
    exact ⟨_, run_ready_iff.2 ⟨c', h₁, h₂, hr⟩⟩

/-- **Divergence after a successful instantiation, every profile.** -/
theorem div_after_instT (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.closedInstT P s t₀ K).div ↔
      ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧ p ∈ (I.closedD P s' K).div := by
  have hpath : (∃ q, Path .idle ([askInst, ansInst .ready] ++ p.map liftMove)
      (.run (E := Sig.empty) (F := I.F.withInst (Behaviour Val)) q)) ↔
      ∃ q, Path .idle p (.run (E := Sig.empty) (F := I.F) q) := by
    constructor
    · rintro ⟨q', hq'⟩
      obtain ⟨q, -, hq⟩ := path_after_inst_iff.1 hq'
      exact ⟨q, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨some q, path_after_inst_iff.2 ⟨q, rfl, hq⟩⟩
  show (∃ y, (CI I P s t₀ K).Run (CI I P s t₀ K).init
      ([askInst, ansInst .ready] ++ p.map liftMove) y ∧ (CI I P s t₀ K).Diverges y) ∧
      (∃ q, Path .idle ([askInst, ansInst .ready] ++ p.map liftMove) (.run q)) ↔
    ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
      (∃ y, (Cmp I P s' K).Run (Cmp I P s' K).init p y ∧ (Cmp I P s' K).Diverges y) ∧
        ∃ q, Path .idle p (.run q)
  rw [hpath]
  constructor
  · rintro ⟨⟨z, hz, hd⟩, hq⟩
    obtain ⟨c', h₁, h₂, hr⟩ := run_ready_iff.1 hz
    obtain ⟨y, rfl, hy⟩ :=
      ((cmpB I P s c'.store t₀ K).run_iff (x := (Cmp I P c'.store K).init) (w := p)).1 hr
    exact ⟨c'.store, ⟨c', h₁, h₂, rfl⟩,
      ⟨y, hy, (cmpB I P s c'.store t₀ K).diverges_iff.1 hd⟩, hq⟩
  · rintro ⟨_, ⟨c', h₁, h₂, rfl⟩, ⟨y, hy, hd⟩, hq⟩
    have hr : (CI I P s t₀ K).Run (none, .ready c'.store) (p.map liftMove)
        ((cmpB I P s c'.store t₀ K).φ y) :=
      (cmpB I P s c'.store t₀ K).run_fwd hy
    exact ⟨⟨_, run_ready_iff.2 ⟨c', h₁, h₂, hr⟩,
      (cmpB I P s c'.store t₀ K).diverges_iff.2 hd⟩, hq⟩

/-- An export call answered right after instantiation. -/
theorem legal_call (f : I.F.Op) (w : I.F.Ar f) :
    Legal ([askInst, ansInst .ready, askEx f, ansEx f w] :
      List (Move Sig.empty (I.F.withInst (Behaviour Val)))) :=
  ⟨_, (path_inst .ready).append (path_lift (R := Behaviour Val)
    (.cons (Silmaril.Games.Step.ask f) (.cons (Silmaril.Games.Step.ret f w) (.nil _))))⟩

/-- An answered export call right after instantiation is an answer of the closed program at a
store the instantiation thread may return at. -/
theorem mem_call_after_instT_iff (f : I.F.Op) (w : I.F.Ar f) :
    [askInst, ansInst .ready, askEx f, ansEx f w] ∈ (I.closedInstT P s t₀ K).toStrategy ↔
      ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
        Responds (I.closedD P s' K).toStrategy f w := by
  have h₁ := mem_ofLTS_iff (L := CI I P s t₀ K)
    (s := [askInst, ansInst .ready, askEx f]) (o := ansEx f w) trivial (legal_call f w)
  refine h₁.trans ((traces_after_instT [.inr (.ask f), .inr (.ans f w)]).trans ?_)
  refine exists_congr fun s' => and_congr_right fun _ => ?_
  show _ ↔ _ ∈ (I.closedD P s' K).forget
  rw [forget_closedD P s' K]

/-- The observations of the closed program at the stores the instantiation thread may return
at. -/
theorem obsAfterInstT_eq (f : I.F.Op) :
    obsAfterInst (I.closedInstT P s t₀ K) f =
      {b | ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
        b ∈ dcompositeObs (I.closedD P s' K) f} := by
  ext b
  constructor
  · rintro (⟨w, hm, hb⟩ | ⟨hb, hd⟩)
    · obtain ⟨s', hs', hr⟩ := (mem_call_after_instT_iff f w).1 hm
      exact ⟨s', hs', .inl ⟨w, hr, hb⟩⟩
    · obtain ⟨s', hs', hd'⟩ := (div_after_instT [.inr (.ask f)]).1 hd
      exact ⟨s', hs', .inr ⟨hb, hd'⟩⟩
  · rintro ⟨s', hs', ⟨w, hr, hb⟩ | ⟨hb, hd⟩⟩
    · exact .inl ⟨w, (mem_call_after_instT_iff f w).2 ⟨s', hs', hr⟩, hb⟩
    · exact .inr ⟨hb, (div_after_instT [.inr (.ask f)]).2 ⟨s', hs', hd⟩⟩

/-- **Adequacy of the calls after instantiation for an arbitrary instantiation thread, every
profile**, given that the stores it returns at are well formed. -/
theorem adequacy_after_instT_of
    (hwf : ∀ {s'}, StartsToT P (hostOf I.imports K) s t₀ s' →
      I.WellFormed s' ∧ ThrowsBelow K s'.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInstT P s t₀ K) f =
      {b | ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} := by
  rw [obsAfterInstT_eq f]
  refine Set.ext fun b => exists_congr fun s' => ?_
  constructor
  · rintro ⟨hs', hb⟩
    obtain ⟨hw', hK'⟩ := hwf hs'
    exact ⟨hs', (adequacy_div hw' K hK' f).symm ▸ hb⟩
  · rintro ⟨hs', hb⟩
    obtain ⟨hw', hK'⟩ := hwf hs'
    exact ⟨hs', (adequacy_div hw' K hK' f) ▸ hb⟩

/-- **Adequacy of the calls after instantiation for an instantiation thread typed at `[]`,
every profile.** -/
theorem adequacy_after_instT (hw : I.WellFormed s) (hok : ConfigOk (t₀.config s) [])
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInstT P s t₀ K) f =
      {b | ∃ s', StartsToT P (hostOf I.imports K) s t₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  adequacy_after_instT_of (fun h => startT_wellFormed hw hok hK h) f

end Thread

/-! ## Start functions -/

/-- Instantiation succeeds exactly when the start phase may return. -/
theorem instReady_closedInst_iff :
    (I.closedInst P s start K).InstReady ↔
      ∃ (c' : Config Nat), Steps P (hostOf I.imports K) (startConfig s start) c' ∧
        c'.code = (Result.values []).toAdmin :=
  instReady_closedInstT_iff

/-- **Adequacy of instantiation, every profile.** -/
theorem adequacy_inst (hw : I.WellFormed s) (hst : ∀ a ∈ start, StartTyped s a)
    (hK : ThrowsBelow K s.exns.length) :
    instObs (I.closedInst P s start K) = startBehaviours P (hostOf I.imports K) s start :=
  adequacy_instT_of (t₀ := startThread start) fun h₁ h₂ => start_result_cases hw hst hK h₁ h₂

/-- **Plays after a successful instantiation, every profile.** -/
theorem traces_after_inst (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (CI I P s (startThread start) K).Traces ↔
      ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧ p ∈ I.closedWith P s' K :=
  traces_after_instT p

/-- **Divergence after a successful instantiation, every profile.** -/
theorem div_after_inst (p : List (Move Sig.empty I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.closedInst P s start K).div ↔
      ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧ p ∈ (I.closedD P s' K).div :=
  div_after_instT p

/-- **Adequacy of the calls after instantiation, every profile**: the observations of an export
call right after instantiation are its Core behaviours at the stores the start phase may
return at. -/
theorem adequacy_after_inst (hw : I.WellFormed s) (hst : ∀ a ∈ start, StartTyped s a)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedInst P s start K) f =
      {b | ∃ s', StartsTo P (hostOf I.imports K) s start s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  adequacy_after_instT_of (t₀ := startThread start)
    (fun h => start_wellFormed hw hst hK h) f

end Silmaril.Proofs.Wasm.Game.Start

namespace Silmaril.Proofs.Wasm.Game.Start

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.ScalarInstance Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-! ## The open system without a start function -/

variable {I : ScalarInstance} {P : Profile} {s : Store Nat}

/-- A state without silent steps reaches only itself silently. -/
theorem run_nil_stuck {E F : Sig.{0}} {L : LTS E F} {x y : L.State}
    (hx : ∀ z, ¬ L.step x none z) (h : L.Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hst _ => exact (hx _ hst).elim

/-- Without a start function the instantiation phase is the exchange `[askInst, ansInst ready]`
leaving the store unchanged. -/
theorem run_inst_none {y : (I.instSys P s none).St}
    (h : (I.instSys P s none).toLTS.Run .fresh [askInst, ansInst .ready] y) : y = .ready s := by
  have hres : ResultAt s (startThread none) (.values []) := rfl
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  have e₁ : x₁ = .fresh := run_nil_stuck (fun _ h => by cases h) h₁
  rw [e₁] at h₂
  cases h₂
  obtain ⟨x₃, x₄, h₄, h₅, h₆⟩ := LTS.Run.cons_inv h₃
  have e₃ : x₃ = .inst (s, startThread none) := run_nil_stuck
    (fun _ h => by cases h with | itau hi => exact resultAt_no_internal hres _ hi) h₄
  rw [e₃] at h₅
  cases h₅ with
  | @iready _ st hr =>
    have hst : st = s := hr.2
    have hy : y = .ready st := run_nil_stuck (fun _ h => by cases h) h₆
    exact hy.trans (congrArg _ hst)

/-- **Without a start function the module strategy is the instance strategy**: after the
instantiation exchange, the plays of `I.instSys P s none` are the plays of `I.strategy P s`,
export questions relabelled. -/
theorem instSys_none_traces (p : List (Move I.E I.F)) :
    [askInst, ansInst .ready] ++ p.map liftMove ∈ (I.instSys P s none).toLTS.Traces ↔
      p ∈ I.strategy P s := by
  have hready : (I.instSys P s none).toLTS.Run .fresh [askInst, ansInst .ready] (.ready s) :=
    .vis InstSystem.Step.askInst (.vis (InstSystem.Step.iready ⟨rfl, rfl⟩) (.nil _))
  refine Iff.trans ?_ (denotes_dlts P s p)
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy, hr⟩ := LTS.Run.of_append hz
    have e : y = .ready s := run_inst_none hy
    rw [e] at hr
    obtain ⟨y', -, hy'⟩ :=
      ((exportB I P s s none).run_iff (x := (I.dlts P s).init) (w := p)).1 hr
    exact ⟨y', hy'⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, hready.append ((exportB I P s s none).run_fwd hy)⟩

end Silmaril.Proofs.Wasm.Game.Start
