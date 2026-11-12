module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Encoding
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# Round 7, memory SIMD: round 6's generic backward recursion at `configVD`

Round 6's backward recursion `Round6.Target.backward_upToVC` reads a SpecTec `Step` from the
`configV` image of a configuration back to a Core step, by recursion on the code: `Step/pure`
and `Step/read` go to per-rule obligations, the four context rules recurse into the redex, and
the store-changing rules go to per-rule obligations. This file re-runs it at `configVD`, where
the memory SIMD instructions are encoded against the IL type `instr` at every depth.

* The encoding facts the recursion uses, at `configVD`: `adminsToVD_eq_map`,
  `adminsToVD_append`, `adminsToVD_split3`, `configVD_cfgV`, `cfgV_of_configEqD`, and the
  constructor of a `case` image (`instrToVD_case`, `adminToVD_case`: `adminToVD a` is headed by
  `Typing.adminHead a`, as `adminToV a` is).
* `StructDecodeD`, `structDecodeD_simEnv`: the decoders the recursion needs (label, handler,
  frame, and a typed `val*` is a value sequence), **proved** at `configVD` for every
  `simEnv B` from the head lemmas of `Sim.Typing`.
* `typingFactsD_simEnv`: the typing facts the recursion needs, **proved** at `configVD` for
  every `simEnv B` (they read `config`, `state` and `instr` structurally).
* `backward_upToD`: **the recursion at `configVD`**, under a predicate closed under SpecTec's
  context decompositions (`Round6.Target.CtxClosedVals`), from `TypingFactsD` and the per-rule
  obligations `BackwardUpToD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Bwd (codeSize CodeEq ConfigEq CtxtInstrsInv CtxtFrameInv stV_inj findRel_of_ruleAt)
open Round6.MemSimd (memSimd)
open Round6.Target (CtxClosedVals)

variable {H : Type}

/-! ## The encoding, as a map -/

theorem adminsToVD_eq_map : ∀ l : List Admin, adminsToVD l = l.map adminToVD
  | [] => rfl
  | a :: l => by simp only [adminsToVD, List.map_cons, adminsToVD_eq_map l]

theorem adminsToVD_append (a b : List Admin) :
    adminsToVD (a ++ b) = adminsToVD a ++ adminsToVD b := by
  simp only [adminsToVD_eq_map, List.map_append]

theorem adminsToVD_vals (vs : List Val) : adminsToVD (vals vs) = adminsToV (vals vs) :=
  adminsToVD_eq _ (by
    induction vs with
    | nil => trivial
    | cons v vs ih =>
      refine ⟨?_, ih⟩
      rcases v with ⟨t, b⟩ | b | r
      · rcases t with t | t <;> rfl
      · rfl
      · trivial)

/-- An image split in three is the image of a split. -/
theorem adminsToVD_split3 {l : List Admin} {A B C : List Value}
    (h : adminsToVD l = A ++ B ++ C) :
    ∃ a b c, l = a ++ b ++ c ∧ adminsToVD a = A ∧ adminsToVD b = B ∧ adminsToVD c = C := by
  rw [adminsToVD_eq_map] at h
  obtain ⟨l₁, c, rfl, h₁, h₃⟩ := List.map_eq_append_iff.1 h
  obtain ⟨a, b, rfl, h₁', h₂⟩ := List.map_eq_append_iff.1 h₁
  exact ⟨a, b, c, rfl, by rw [adminsToVD_eq_map, h₁'], by rw [adminsToVD_eq_map, h₂],
    by rw [adminsToVD_eq_map, h₃]⟩

/-- A one-element image is the image of a one-element sequence. -/
theorem adminsToVD_eq_single {is : List Admin} {v : Value} (h : adminsToVD is = [v]) :
    ∃ a, is = [a] ∧ adminToVD a = v := by
  match is, h with
  | [a], h => exact ⟨a, rfl, (List.cons.inj h).1⟩
  | [], h => simp [adminsToVD] at h
  | _ :: _ :: _, h => simp [adminsToVD] at h

/-- The image of a configuration, as `cfgV`. -/
theorem configVD_eq (hn : H → String) (c : Config H) :
    configVD hn c = cfgV (stV (storeVD hn c.store) (frameV c.frame)) (adminsToVD c.code) := rfl

/-- Reading `configVD` against a `cfgV`. -/
theorem configVD_cfgV {hn : H → String} {c : Config H} {z : Value} {is : List Value}
    (h : configVD hn c = cfgV z is) :
    z = stateVD hn c.store c.frame ∧ is = adminsToVD c.code := by
  have h' := Bwd.cfgV_inj h
  exact ⟨h'.1.symm, h'.2.symm⟩

/-- A successor read up to `ConfigEq`, unpacked at `configVD`. -/
theorem cfgV_of_configEqD {hn : H → String} {c d : Config H} (he : ConfigEq c d) {z : Value}
    {is : List Value} (h : cfgV z is = configVD hn d) :
    z = stateVD hn c.store c.frame ∧ is = adminsToVD d.code := by
  obtain ⟨hs, hf, -⟩ := he
  have h' := configVD_cfgV h.symm
  exact ⟨by rw [hs, hf]; exact h'.1, h'.2⟩

/-! ## The constructor of an image -/

/-- A memory SIMD instruction's image is headed by its constructor. -/
theorem instrToVM_case_memSimd {i : Instr} (hm : memSimd i = true) {op : MixopS} {w : Value}
    (h : Round6.MemSimd.instrToVM i = .case op w) : op = Typing.instrHead i := by
  cases i <;> simp_all [memSimd, Round6.MemSimd.instrToVM, Round6.MemSimd.vecMemV,
    Typing.instrHead]

/-- **A `case` image at `instrToVD` has the instruction's head.** -/
theorem instrToVD_case {i : Instr} {op : MixopS} {w : Value} (h : instrToVD i = .case op w) :
    op = Typing.instrHead i := by
  by_cases hb : (∃ bt body, i = .block bt body) ∨ (∃ bt body, i = .loop bt body) ∨
      (∃ bt b₁ b₂, i = .if_ bt b₁ b₂) ∨ (∃ bt cs body, i = .tryTable bt cs body)
  · rcases hb with ⟨bt, body, rfl⟩ | ⟨bt, body, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ | ⟨bt, cs, body, rfl⟩ <;>
    · simp only [instrToVD, Value.case.injEq] at h
      exact h.1.symm
  · have hv : instrToVD i = Round6.MemSimd.instrToVM i :=
      instrToVD.eq_5 i (fun bt body e => hb (.inl ⟨bt, body, e⟩))
        (fun bt body e => hb (.inr (.inl ⟨bt, body, e⟩)))
        (fun bt b₁ b₂ e => hb (.inr (.inr (.inl ⟨bt, b₁, b₂, e⟩))))
        (fun bt cs body e => hb (.inr (.inr (.inr ⟨bt, cs, body, e⟩))))
    rw [hv] at h
    cases hm : memSimd i
    · rw [Round6.MemSimd.instrToVM_of_not hm] at h
      exact Typing.instrToV_case h
    · exact instrToVM_case_memSimd hm h

/-- **A `case` image at `adminToVD` has the instruction's head.** -/
theorem adminToVD_case {a : Admin} {op : MixopS} {w : Value} (h : adminToVD a = .case op w) :
    op = Typing.adminHead a := by
  cases a with
  | plain i => exact instrToVD_case (by simpa only [adminToVD] using h)
  | label n c b => simp only [adminToVD, Value.case.injEq] at h; exact h.1.symm
  | handler n c b => simp only [adminToVD, Value.case.injEq] at h; exact h.1.symm
  | frame n f b => simp only [adminToVD, Value.case.injEq] at h; exact h.1.symm
  | _ => exact Typing.adminToV_case (by simpa only [adminToVD, adminToV] using h)

/-! ## The decoders at `configVD` -/

/-- **The decoders the generic recursion needs, at `adminToVD`.** -/
structure StructDecodeD (env : Env) : Prop where
  /-- `LABEL_n{…} …`. -/
  label : ∀ (a : Admin) (x : Value), adminToVD a = .case "LABEL_%{%}%" x →
    ∃ n cont body, a = .label n cont body
  /-- `HANDLER_n{…} …`. -/
  handler : ∀ (a : Admin) (x : Value), adminToVD a = .case "HANDLER_%{%}%" x →
    ∃ n cs body, a = .handler n cs body
  /-- `FRAME_n{…} …`. -/
  frame : ∀ (a : Admin) (x : Value), adminToVD a = .case "FRAME_%{%}%" x →
    ∃ n fi body, a = .frame n fi body
  /-- A code sequence whose image is a `val*` is a value sequence. -/
  vals : ∀ (ρ : VarEnv) (l : List Admin), ValsOnly ρ → HasTyp env ρ valsT (.list (adminsToVD l)) →
    ∃ vs, l = vals vs

/-- A code sequence whose `adminsToVD` image is a typed `val*` is a value sequence. -/
theorem vals_of_typedD {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) :
    ∀ {l : List Admin}, HasTyp (simEnv B) ρ valsT (.list (adminsToVD l)) → ∃ vs, l = vals vs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
      obtain ⟨vs₀, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
      have hvs' : adminsToVD (a :: l) = vs₀ := Value.list.inj hvs
      have hall := hasTypList_iff.1 hl
      have ha : HasTyp (simEnv B) ρ (.varT "val" []) (adminToVD a) :=
        hall (adminToVD a) (by simp [← hvs', adminsToVD])
      obtain ⟨op, w, hw, hop⟩ := Typing.head_of_typed_val hρ ha
      obtain ⟨v, rfl⟩ := Typing.head_val ((adminToVD_case hw) ▸ hop)
      have hl' : HasTyp (simEnv B) ρ valsT (.list (adminsToVD l)) :=
        hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun u hu =>
          hall u (by simp [← hvs', adminsToVD, hu])⟩
      obtain ⟨vs, rfl⟩ := vals_of_typedD hρ hl'
      exact ⟨v :: vs, rfl⟩

/-- **The decoders hold at `configVD` in every `simEnv B`.** -/
theorem structDecodeD_simEnv (B : Builtins) : StructDecodeD (simEnv B) where
  label _ _ h := Typing.head_label (adminToVD_case h).symm
  handler _ _ h := Typing.head_handler (adminToVD_case h).symm
  frame _ _ h := Typing.head_frame (adminToVD_case h).symm
  vals _ _ hρ h := vals_of_typedD hρ h

/-! ## The typing facts at `configVD` -/

set_option maxRecDepth 100000 in
/-- **The typing facts the recursion needs hold at `configVD` in every `simEnv B`**: they read
the IL types `config`, `state` and `instr` structurally, as `Typing.typingFacts_simEnv` does at
`configV`. -/
theorem typingFactsD_simEnv (B : Builtins) (hn : H → String) :
    TypingFactsD (simEnv B) hn where
  config c := by
    unfold TypedD configVD
    rw [Typing.typedV_pair_iff Typing.findTyp_config rfl (Typing.closedT_var _)
      (Typing.closedT_list _)]
  state s f := by
    unfold stateVD
    rw [Typing.typedV_iff_empty (Typing.closedT_var _), Typing.typedV_pair_iff
      Typing.findTyp_state rfl (Typing.closedT_var _) (Typing.closedT_var _)]
  append _ _ := typedV_list_append
  label _ _ _ h := (Typing.typedV_admin3 (Typing.closedT_list "instr") rfl h).2.2
  handler _ _ _ h := (Typing.typedV_admin3 (Typing.closedT_list "catch") rfl h).2.2
  frame _ _ _ h := (Typing.typedV_admin3 (Typing.closedT_var "frame") rfl h).2

/-! ## The recursion at `configVD` -/

section Ctxt

variable {V : Config H → Prop} {env : Env} {hn : H → String} {P : Numerics.Profile}
  {host : HostSemantics H}

/-- The induction hypothesis, for code smaller than `n`, under `V`, at `configVD`. -/
def IHD (V : Config H → Prop) (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), codeSize c.code < n → V c → TypedD env hn c →
    SStep env (configVD hn c) w → BwdUpToD hn P host c w

/-- The redex of a typed split is typed. -/
theorem typedD_mid (T : TypingFactsD env hn) {s : Store H} {f : Frame} {A I R : List Admin}
    (hc : TypedD env hn ⟨s, f, A ++ I ++ R⟩) : TypedD env hn ⟨s, f, I⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  have h₁ : TypedV env instrsT (.list (adminsToVD A ++ adminsToVD I ++ adminsToVD R)) := by
    simpa only [adminsToVD_append] using hcode
  have h₂ := ((T.append _ _).1 ((T.append _ _).1 h₁).1).2
  exact (T.config _).2 ⟨hst, h₂⟩

/-- The body of a typed one-instruction configuration is typed, given that the instruction's
typing gives the body's. -/
theorem typedD_inner (T : TypingFactsD env hn) {s : Store H} {f : Frame} {a : Admin}
    {body : List Admin} (hc : TypedD env hn ⟨s, f, [a]⟩)
    (hin : TypedV env instrsT (.list [adminToVD a]) →
      TypedV env instrsT (.list (adminsToVD body))) :
    TypedD env hn ⟨s, f, body⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  exact (T.config _).2 ⟨hst, hin hcode⟩

/-- The inner configuration of a typed frame is typed. -/
theorem typedD_frame (T : TypingFactsD env hn) {s : Store H} {f fi : Frame} {k : Nat}
    {body : List Admin} (hc : TypedD env hn ⟨s, f, [.frame k fi body]⟩) :
    TypedD env hn ⟨s, fi, body⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  have hfr := T.frame k fi body hcode
  have hs := ((T.state s f).1 hst).1
  exact (T.config _).2 ⟨(T.state s fi).2 ⟨hs, hfr.1⟩, hfr.2⟩

/-- `ctxt-instrs` backwards, under `V`, at `configVD`. -/
theorem bwdD_ctxtInstrs (CV : CtxClosedVals V) (D : StructDecodeD env) (T : TypingFactsD env hn)
    {n : Nat} (ih : IHD V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : TypedD env hn ⟨s, f, code⟩)
    (hinv : CtxtInstrsInv env (configVD hn ⟨s, f, code⟩) w) :
    BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, h₂, hs⟩ := hinv
  have e₁ : z = stateVD hn s f ∧ vs ++ is ++ rest = adminsToVD code := configVD_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := adminsToVD_split3 e₁.2.symm
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := D.vals ρ A hρ (hA ▸ hvs)
  have hneA' : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have hneA : vs₀ ≠ [] ∨ R ≠ [] := hneA'.imp (fun h he => h (by rw [hv₀, he]; rfl)) id
  have hT : TypedD env hn ⟨s, f, I⟩ := typedD_mid T (hcode ▸ hc)
  have hV : V ⟨s, f, I⟩ := CV.mid s f vs₀ I R (hv₀ ▸ hcode ▸ hv)
  have hsz : codeSize I < n := by
    have h₁ : codeSize I < codeSize (A ++ I ++ R) := Bwd.codeSize_mid hneA'
    have h₂ : codeSize (A ++ I ++ R) < n + 1 := hcode ▸ hlt
    omega
  have e₂ : cfgV z is = configVD hn ⟨s, f, I⟩ := by rw [configVD_eq, e₁.1, hI]; rfl
  have hs' : SStep env (configVD hn ⟨s, f, I⟩) (cfgV z' is') := e₂ ▸ hs
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ := ih _ _ hsz hV hT hs'
  obtain ⟨hz', his'⟩ := cfgV_of_configEqD hE hw
  refine ⟨⟨s₂, f₂, vals vs₀ ++ K ++ R⟩, ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩,
    ⟨rfl, rfl, (CodeEq.refl _).append hE.2.2 |>.append (CodeEq.refl _)⟩, ?_, ?_⟩
  · show w = configVD hn ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩
    rw [h₂, hz', his', configVD_eq, adminsToVD_append, adminsToVD_append, ← hv₀, hA, hR]
    rfl
  · show Step P host ⟨s, f, code⟩ ⟨s₂, f₂, vals vs₀ ++ K ++ R⟩
    rw [hcode, hv₀]
    exact .ctxtInstrs hst hneA

/-- `ctxt-label` backwards, under `V`, at `configVD`. -/
theorem bwdD_ctxtLabel (CV : CtxClosedVals V) (D : StructDecodeD env) (T : TypingFactsD env hn)
    {n : Nat} (ih : IHD V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : TypedD env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cont is is',
      configVD hn ⟨s, f, code⟩ = cfgV z [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is])] ∧
      w = cfgV z' [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configVD_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := D.label a _ ha
  have hp : Value.num (.natN k) = m ∧ instrsToVD cont₀ = cont ∧ adminsToVD body = is := by
    simpa only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : TypedD env hn ⟨s, f, body⟩ :=
    typedD_inner T hc fun h => T.label k cont₀ body h
  have e₂ : cfgV z is = configVD hn ⟨s, f, body⟩ := by rw [configVD_eq, e₁.1, hp.2.2]; rfl
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_label k cont₀ body) (Nat.le_of_lt_succ hlt))
      (CV.label s f k cont₀ body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEqD hE hw
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ⟨s₂, f₂, [.label k cont₀ K']⟩,
    ⟨rfl, rfl, .cons (.label hE.2.2) .nil⟩, ?_, .ctxtLabel hst⟩
  show w = configVD hn ⟨s₂, f₂, [.label k cont₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-handler` backwards, under `V`, at `configVD`. -/
theorem bwdD_ctxtHandler (CV : CtxClosedVals V) (D : StructDecodeD env)
    (T : TypingFactsD env hn) {n : Nat} (ih : IHD V env hn P host n) {s : Store H} {f : Frame}
    {code : List Admin} {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : TypedD env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cs is is',
      configVD hn ⟨s, f, code⟩ = cfgV z [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is])] ∧
      w = cfgV z' [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cs, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configVD_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, cs₀, body, rfl⟩ := D.handler a _ ha
  have hp : Value.num (.natN k) = m ∧ cs₀.map Encode.toValue = cs ∧ adminsToVD body = is := by
    simpa only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : TypedD env hn ⟨s, f, body⟩ :=
    typedD_inner T hc fun h => T.handler k cs₀ body h
  have e₂ : cfgV z is = configVD hn ⟨s, f, body⟩ := by rw [configVD_eq, e₁.1, hp.2.2]; rfl
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_handler k cs₀ body) (Nat.le_of_lt_succ hlt))
      (CV.handler s f k cs₀ body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEqD hE hw
  refine ⟨⟨s₂, f₂, [.handler k cs₀ K]⟩, ⟨s₂, f₂, [.handler k cs₀ K']⟩,
    ⟨rfl, rfl, .cons (.handler hE.2.2) .nil⟩, ?_, .ctxtHandler hst⟩
  show w = configVD hn ⟨s₂, f₂, [.handler k cs₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-frame` backwards, under `V`, at `configVD`. -/
theorem bwdD_ctxtFrame (CV : CtxClosedVals V) (D : StructDecodeD env) (T : TypingFactsD env hn)
    {n : Nat} (ih : IHD V env hn P host n) {s : Store H} {f : Frame} {code : List Admin}
    {w : Value} (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩)
    (hc : TypedD env hn ⟨s, f, code⟩)
    (hinv : CtxtFrameInv env (configVD hn ⟨s, f, code⟩) w) :
    BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configVD_cfgV h₁
  have e₀ : sv = storeVD hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := D.frame a _ ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToVD body = is := by
    simpa only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : TypedD env hn ⟨s, fi, body⟩ := typedD_frame T hc
  have e₂ : cfgV (stV sv fr) is = configVD hn ⟨s, fi, body⟩ := by
    rw [configVD_eq, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (Bwd.codeSize_frame k fi body) (Nat.le_of_lt_succ hlt))
      (CV.frame s f fi k body hv) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEqD hE hw
  have hz'' : sv' = storeVD hn s₂ ∧ fr' = frameV f₂ := stV_inj hz'
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ⟨s₂, f, [.frame k f₂ K']⟩,
    ⟨rfl, rfl, .cons (.frame hE.2.2) .nil⟩, ?_, .ctxtFrame hst⟩
  show w = configVD hn ⟨s₂, f, [.frame k f₂ K']⟩
  rw [h₂, hz''.1, hz''.2, his', e₀.2, ← hp.1]
  rfl

/-- `Step/pure` backwards, under `V`, at `configVD`. -/
theorem bwdD_pure (Bk : BackwardUpToD V env hn P host)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    {s : Store H} {f : Frame} {code : List Admin} {w : Value} (hv : V ⟨s, f, code⟩)
    (hc : TypedD env hn ⟨s, f, code⟩)
    (hinv : ∃ z is js, configVD hn ⟨s, f, code⟩ = cfgV z is ∧ w = cfgV z js ∧ SPure env is js) :
    BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hP
  have e₁ := configVD_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_pure" i (.tuple [.list (adminsToVD code), .list js]) := e₁.2 ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.pure i s f code (.list js) hv hc hf'
  refine ⟨⟨s, f, is'⟩, ⟨s, f, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- `Step/read` backwards, under `V`, at `configVD`. -/
theorem bwdD_read (Bk : BackwardUpToD V env hn P host)
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    {c : Config H} {w : Value} (hv : V c) (hc : TypedD env hn c)
    (hinv : ∃ z is js, configVD hn c = cfgV z is ∧ w = cfgV z js ∧ SRead env (cfgV z is) js) :
    BwdUpToD hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hR
  have e₁ := configVD_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_read" i (.tuple [configVD hn c, .list js]) := h₁ ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.read i c (.list js) hv hc hf'
  refine ⟨⟨c.store, c.frame, is'⟩, ⟨c.store, c.frame, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- One step of the recursion, under `V`, at `configVD`. -/
theorem bwdD_dispatch (CV : CtxClosedVals V) (Bk : BackwardUpToD V env hn P host)
    (D : StructDecodeD env) (T : TypingFactsD env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) {n : Nat}
    (ih : IHD V env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hv : V ⟨s, f, code⟩) (hc : TypedD env hn ⟨s, f, code⟩)
    (hs : SStep env (configVD hn ⟨s, f, code⟩) w) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt R.pure
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact bwdD_pure Bk hP hv hc (Bwd.inv_pure R.pure hf)
  | 1, hf => exact bwdD_read Bk hR hv hc (Bwd.inv_read R.read hf)
  | 2, hf => exact bwdD_ctxtInstrs CV D T ih hlt hv hc (Bwd.inv_ctxtInstrs R.ctxtInstrs hf)
  | 3, hf => exact bwdD_ctxtLabel CV D T ih hlt hv hc (Bwd.inv_ctxtLabel R.ctxtLabel hf)
  | 4, hf => exact bwdD_ctxtHandler CV D T ih hlt hv hc (Bwd.inv_ctxtHandler R.ctxtHandler hf)
  | 5, hf => exact bwdD_ctxtFrame CV D T ih hlt hv hc (Bwd.inv_ctxtFrame R.ctxtFrame hf)
  | k + 6, hf => exact Bk.step (k + 6) (by omega) _ w hv hc hf

/-- The recursion on the size of the code, under `V`, at `configVD`. -/
theorem bwdD_all (CV : CtxClosedVals V) (Bk : BackwardUpToD V env hn P host)
    (D : StructDecodeD env) (T : TypingFactsD env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) :
    ∀ n, IHD V env hn P host n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨_, _, _⟩ _ hlt hv hc hs =>
      bwdD_dispatch CV Bk D T R hP hR (bwdD_all CV Bk D T R hP hR n) hlt hv hc hs

end Ctxt

/-- **Round 6's backward recursion at `configVD`** (SpecTec → Core, up to `ConfigEq`): under a
predicate `V` closed under SpecTec's context decompositions, a declarative SpecTec `Step` from
the `configVD` image of a typed configuration is the image of a configuration equivalent to a
Core successor, given the typing facts and the per-rule obligations at `configVD`. -/
theorem backward_upToD {V : Config H → Prop} {env : Env} {hn : H → String}
    {P : Numerics.Profile} {host : HostSemantics H} (CV : CtxClosedVals V)
    (Bk : BackwardUpToD V env hn P host) (D : StructDecodeD env) (T : TypingFactsD env hn)
    (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    (c : Config H) (w : Value) (hv : V c) (hc : TypedD env hn c)
    (hs : SStep env (configVD hn c) w) : BwdUpToD hn P host c w :=
  bwdD_all CV Bk D T R hP hR (codeSize c.code + 1) c w (Nat.lt_succ_self _) hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
