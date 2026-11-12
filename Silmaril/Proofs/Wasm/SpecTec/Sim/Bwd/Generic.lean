module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Invert
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.CallEq

/-!
# The generic SpecTec → Core direction

`backward_upTo`: given the per-rule obligations `BackwardUpTo` (one per `Step_pure`, `Step_read`
and store-changing `Step` rule), the decoders `StructDecode` and the encoding's `TypingFacts`,
every SpecTec step from the image of a typed configuration lands on the image of a configuration
equivalent (`ConfigEq`) to a Core successor. This is the dispatch skeleton of the second conjunct of
`Task.wholeStepUpTo`: `Step` rules 0 and 1 go to `BackwardUpTo.pure`/`.read`, rules 2–5 (the four
contexts, for *every* split of `ctxt-instrs`) recurse into the redex, and rules ≥ 6 go to
`BackwardUpTo.step`.

The recursion is on `codeSize`, the number of administrative instructions at any depth of
labels, handlers and frames: each context rule's premise is a step of a strictly smaller code
(`ctxt-instrs` because its prefix or suffix is non-empty).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The size of active code -/

mutual
/-- The number of administrative instructions in `a`, at any depth of labels, handlers and
frames. -/
def adminSize : Admin → Nat
  | .label _ _ b => codeSize b + 1
  | .handler _ _ b => codeSize b + 1
  | .frame _ _ b => codeSize b + 1
  | _ => 1

/-- `adminSize`, summed over a sequence. -/
def codeSize : List Admin → Nat
  | [] => 0
  | a :: l => adminSize a + codeSize l
end

/-- Every instruction counts at least once. -/
theorem adminSize_pos (a : Admin) : 0 < adminSize a := by
  cases a <;> simp [adminSize]

/-- `codeSize` is additive. -/
theorem codeSize_append (a b : List Admin) : codeSize (a ++ b) = codeSize a + codeSize b := by
  induction a with
  | nil => simp [codeSize]
  | cons x a ih => simp [codeSize, ih, Nat.add_assoc]

/-- A non-empty sequence has positive size. -/
theorem codeSize_pos {l : List Admin} (h : l ≠ []) : 0 < codeSize l := by
  match l, h with
  | a :: l, _ => exact Nat.lt_of_lt_of_le (adminSize_pos a) (Nat.le_add_right _ _)

/-- The redex of a non-trivial split is smaller. -/
theorem codeSize_mid {a b c : List Admin} (h : a ≠ [] ∨ c ≠ []) :
    codeSize b < codeSize (a ++ b ++ c) := by
  rw [codeSize_append, codeSize_append]
  rcases h with h | h
  · have := codeSize_pos h
    omega
  · have := codeSize_pos h
    omega

/-- The body of a label, handler or frame is smaller. -/
theorem codeSize_label (n : Nat) (cont : List Instr) (b : List Admin) :
    codeSize b < codeSize [.label n cont b] := by
  simp [codeSize, adminSize]

/-- See `codeSize_label`. -/
theorem codeSize_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    codeSize b < codeSize [.handler n cs b] := by
  simp [codeSize, adminSize]

/-- See `codeSize_label`. -/
theorem codeSize_frame (n : Nat) (f : Frame) (b : List Admin) :
    codeSize b < codeSize [.frame n f b] := by
  simp [codeSize, adminSize]

/-! ## Reading the encoding back -/

/-- An image that splits in three splits its preimage. -/
theorem adminsToV_split3 {l : List Admin} {A B C : List Value} (h : adminsToV l = A ++ B ++ C) :
    ∃ a b c, l = a ++ b ++ c ∧ adminsToV a = A ∧ adminsToV b = B ∧ adminsToV c = C := by
  rw [adminsToV_eq_map] at h
  obtain ⟨l₁, c, rfl, h₁, h₃⟩ := List.map_eq_append_iff.1 h
  obtain ⟨a, b, rfl, h₁', h₂⟩ := List.map_eq_append_iff.1 h₁
  exact ⟨a, b, c, rfl, by rw [adminsToV_eq_map, h₁'], by rw [adminsToV_eq_map, h₂],
    by rw [adminsToV_eq_map, h₃]⟩

/-- The image of a configuration, as `cfgV`. -/
theorem configV_eq (hn : H → String) (c : Config H) :
    configV hn c = cfgV (stateV hn c.store c.frame) (adminsToV c.code) := rfl

/-- The image of a state, as `stV`. -/
theorem stateV_eq (hn : H → String) (s : Store H) (f : Frame) :
    stateV hn s f = stV (storeV hn s) (frameV f) := rfl

/-- Reading `configV` against a `cfgV`. -/
theorem configV_cfgV {hn : H → String} {c : Config H} {z : Value} {is : List Value}
    (h : configV hn c = cfgV z is) : z = stateV hn c.store c.frame ∧ is = adminsToV c.code := by
  have h' := cfgV_inj h
  exact ⟨h'.1.symm, h'.2.symm⟩

/-- A successor read up to `ConfigEq`, unpacked: the image of `d` is a `cfgV`. -/
theorem cfgV_of_configEq {hn : H → String} {c d : Config H} (he : ConfigEq c d) {z : Value}
    {is : List Value} (h : cfgV z is = configV hn d) :
    z = stateV hn c.store c.frame ∧ is = adminsToV d.code := by
  obtain ⟨hs, hf, -⟩ := he
  have h' := configV_cfgV h.symm
  exact ⟨by rw [hs, hf]; exact h'.1, h'.2⟩

/-! ## The four context rules, backwards -/

section Ctxt

variable {env : Env} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The induction hypothesis of the generic backward proof, for code smaller than `n`. -/
def IH (env : Env) (hn : H → String) (P : Numerics.Profile) (host : HostSemantics H)
    (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), codeSize c.code < n → Typed env hn c →
    SStep env (configV hn c) w → BwdUpTo hn P host c w

/-- `ctxt-instrs` backwards: decode the split, recurse into the redex, and rebuild. -/
theorem bwd_ctxtInstrs (D : StructDecode env) (T : TypingFacts env hn) {n : Nat}
    (ih : IH env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtInstrsInv env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, h₂, hs⟩ := hinv
  have e₁ : z = stateV hn s f ∧ vs ++ is ++ rest = adminsToV code := configV_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := adminsToV_split3 e₁.2.symm
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := D.vals ρ A hρ (hA ▸ hvs)
  have hneA' : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have hneA : vs₀ ≠ [] ∨ R ≠ [] := hneA'.imp (fun h he => h (by rw [hv₀, he]; rfl)) id
  have hT : Typed env hn ⟨s, f, I⟩ := typed_mid T (hcode ▸ hc)
  have hsz : codeSize I < n := by
    have h₁ : codeSize I < codeSize (A ++ I ++ R) := codeSize_mid hneA'
    have h₂ : codeSize (A ++ I ++ R) < n + 1 := hcode ▸ hlt
    omega
  have e₂ : cfgV z is = configV hn ⟨s, f, I⟩ := by rw [configV_eq, e₁.1, hI]
  have hs' : SStep env (configV hn ⟨s, f, I⟩) (cfgV z' is') := e₂ ▸ hs
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ := ih _ _ hsz hT hs'
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, vals vs₀ ++ K ++ R⟩, ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩,
    ⟨rfl, rfl, (CodeEq.refl _).append hE.2.2 |>.append (CodeEq.refl _)⟩, ?_, ?_⟩
  · show w = configV hn ⟨s₂, f₂, vals vs₀ ++ K' ++ R⟩
    rw [h₂, hz', his', configV_eq, adminsToV_append, adminsToV_append, ← hv₀, hA, hR]
  · show Step P host ⟨s, f, code⟩ ⟨s₂, f₂, vals vs₀ ++ K ++ R⟩
    rw [hcode, hv₀]
    exact .ctxtInstrs hst hneA
where
  /-- The redex of a typed split is typed. -/
  typed_mid (T : TypingFacts env hn) {s : Store H} {f : Frame} {A I R : List Admin}
      (hc : Typed env hn ⟨s, f, A ++ I ++ R⟩) : Typed env hn ⟨s, f, I⟩ := by
    obtain ⟨hst, hcode⟩ := (T.config _).1 hc
    have h₁ : TypedV env instrsT (.list (adminsToV A ++ adminsToV I ++ adminsToV R)) := by
      simpa only [adminsToV_append] using hcode
    have h₂ := ((T.append _ _).1 ((T.append _ _).1 h₁).1).2
    exact (T.config _).2 ⟨hst, h₂⟩

/-- The body of a typed one-instruction context is typed, at any frame. -/
theorem typed_inner (T : TypingFacts env hn) {s : Store H} {f : Frame} {a : Admin} {body : List Admin}
    (hc : Typed env hn ⟨s, f, [a]⟩)
    (hin : TypedV env instrsT (.list [adminToV a]) → TypedV env instrsT (.list (adminsToV body)))
    : Typed env hn ⟨s, f, body⟩ := by
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  exact (T.config _).2 ⟨hst, hin hcode⟩

/-- `ctxt-label` backwards. -/
theorem bwd_ctxtLabel (D : StructDecode env) (T : TypingFacts env hn) {n : Nat}
    (ih : IH env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cont is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is])] ∧
      w = cfgV z' [.case "LABEL_%{%}%" (.tuple [m, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := D.label a _ ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, f, body⟩ := typed_inner T hc fun h => (T.label k cont₀ body h).2.2
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (codeSize_label k cont₀ body) (Nat.le_of_lt_succ hlt)) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ⟨s₂, f₂, [.label k cont₀ K']⟩,
    ⟨rfl, rfl, .cons (.label hE.2.2) .nil⟩, ?_, .ctxtLabel hst⟩
  show w = configV hn ⟨s₂, f₂, [.label k cont₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-handler` backwards. -/
theorem bwd_ctxtHandler (D : StructDecode env) (T : TypingFacts env hn) {n : Nat}
    (ih : IH env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z z' m cs is is',
      configV hn ⟨s, f, code⟩ = cfgV z [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is])] ∧
      w = cfgV z' [.case "HANDLER_%{%}%" (.tuple [m, .list cs, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is')) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cs, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cs₀, body, rfl⟩ := D.handler a _ ha
  have hp : Value.num (.natN k) = m ∧ cs₀.map Encode.toValue = cs ∧ adminsToV body = is := by
    simpa only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, f, body⟩ := typed_inner T hc fun h => (T.handler k cs₀ body h).2.2
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (codeSize_handler k cs₀ body) (Nat.le_of_lt_succ hlt)) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  refine ⟨⟨s₂, f₂, [.handler k cs₀ K]⟩, ⟨s₂, f₂, [.handler k cs₀ K']⟩,
    ⟨rfl, rfl, .cons (.handler hE.2.2) .nil⟩, ?_, .ctxtHandler hst⟩
  show w = configV hn ⟨s₂, f₂, [.handler k cs₀ K']⟩
  rw [h₂, hz', his', ← hp.1, ← hp.2.1]
  rfl

/-- `ctxt-frame` backwards: the premise runs in the frame's own frame and leaves the outer one. -/
theorem bwd_ctxtFrame (D : StructDecode env) (T : TypingFacts env hn) {n : Nat}
    (ih : IH env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : CtxtFrameInv env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ := hinv
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := D.frame a _ ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have hT : Typed env hn ⟨s, fi, body⟩ := typed_frame T hc
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq, e₀.1, ← hp.2.1, hp.2.2]
    rfl
  obtain ⟨⟨s₂, f₂, K⟩, ⟨s₃, f₃, K'⟩, hE, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (codeSize_frame k fi body) (Nat.le_of_lt_succ hlt)) hT (e₂ ▸ hs)
  obtain ⟨hz', his'⟩ := cfgV_of_configEq hE hw
  have hz'' : sv' = storeV hn s₂ ∧ fr' = frameV f₂ := stV_inj hz'
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ⟨s₂, f, [.frame k f₂ K']⟩,
    ⟨rfl, rfl, .cons (.frame hE.2.2) .nil⟩, ?_, .ctxtFrame hst⟩
  show w = configV hn ⟨s₂, f, [.frame k f₂ K']⟩
  rw [h₂, hz''.1, hz''.2, his', e₀.2, ← hp.1]
  rfl
where
  /-- The inner configuration of a typed frame is typed. -/
  typed_frame (T : TypingFacts env hn) {s : Store H} {f fi : Frame} {k : Nat} {body : List Admin}
      (hc : Typed env hn ⟨s, f, [.frame k fi body]⟩) : Typed env hn ⟨s, fi, body⟩ := by
    obtain ⟨hst, hcode⟩ := (T.config _).1 hc
    have hfr := T.frame k fi body hcode
    have hs := ((T.state s f).1 hst).1
    exact (T.config _).2 ⟨(T.state s fi).2 ⟨hs, hfr.2.1⟩, hfr.2.2⟩

/-! ## Dispatch -/

/-- `Step/pure` backwards: one `BackwardUpTo.pure` field. -/
theorem bwd_pure (Bk : BackwardUpTo env hn P host)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    {s : Store H} {f : Frame} {code : List Admin} {w : Value} (hc : Typed env hn ⟨s, f, code⟩)
    (hinv : ∃ z is js, configV hn ⟨s, f, code⟩ = cfgV z is ∧ w = cfgV z js ∧ SPure env is js) :
    BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hP
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_pure" i (.tuple [.list (adminsToV code), .list js]) := e₁.2 ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.pure i s f code (.list js) hc hf'
  refine ⟨⟨s, f, is'⟩, ⟨s, f, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- `Step/read` backwards: one `BackwardUpTo.read` field. -/
theorem bwd_read (Bk : BackwardUpTo env hn P host)
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    {c : Config H} {w : Value} (hc : Typed env hn c)
    (hinv : ∃ z is js, configV hn c = cfgV z is ∧ w = cfgV z js ∧ SRead env (cfgV z is) js) :
    BwdUpTo hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, hp⟩ := hinv
  obtain ⟨t, rules, hrel⟩ := hR
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hp
  have hf' : Fires env "Step_read" i (.tuple [configV hn c, .list js]) := h₁ ▸ hf
  obtain ⟨is', js', hE, hw, hst⟩ := Bk.read i c (.list js) hc hf'
  refine ⟨⟨c.store, c.frame, is'⟩, ⟨c.store, c.frame, js'⟩, ⟨rfl, rfl, hE⟩, ?_, hst⟩
  rw [h₂, e₁.1, Value.list.inj hw]
  rfl

/-- One step of the generic backward proof: dispatch on the `Step` rule that fired. -/
theorem bwd_dispatch (Bk : BackwardUpTo env hn P host) (D : StructDecode env)
    (T : TypingFacts env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) {n : Nat}
    (ih : IH env hn P host n) {s : Store H} {f : Frame} {code : List Admin} {w : Value}
    (hlt : codeSize code < n + 1) (hc : Typed env hn ⟨s, f, code⟩)
    (hs : SStep env (configV hn ⟨s, f, code⟩) w) : BwdUpTo hn P host ⟨s, f, code⟩ w := by
  obtain ⟨t, rules, hrel⟩ := findRel_of_ruleAt R.pure
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact bwd_pure Bk hP hc (inv_pure R.pure hf)
  | 1, hf => exact bwd_read Bk hR hc (inv_read R.read hf)
  | 2, hf => exact bwd_ctxtInstrs D T ih hlt hc (inv_ctxtInstrs R.ctxtInstrs hf)
  | 3, hf => exact bwd_ctxtLabel D T ih hlt hc (inv_ctxtLabel R.ctxtLabel hf)
  | 4, hf => exact bwd_ctxtHandler D T ih hlt hc (inv_ctxtHandler R.ctxtHandler hf)
  | 5, hf => exact bwd_ctxtFrame D T ih hlt hc (inv_ctxtFrame R.ctxtFrame hf)
  | k + 6, hf => exact Bk.step (k + 6) (by omega) _ w hc hf

/-- The generic backward proof, by recursion on the size of the code. -/
theorem bwd_all (Bk : BackwardUpTo env hn P host) (D : StructDecode env)
    (T : TypingFacts env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules)) :
    ∀ n, IH env hn P host n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨_, _, _⟩ _ hlt hc hs => bwd_dispatch Bk D T R hP hR (bwd_all Bk D T R hP hR n) hlt hc hs

end Ctxt

/-- **The backward simulation, assembled** (SpecTec → Core, up to `ConfigEq`). Given the
per-rule obligations `BackwardUpTo`, the decoders `StructDecode`, the encoding's `TypingFacts`
and the provenance of `Step`'s rules, every SpecTec step from the image of a typed configuration
lands on the image of a configuration equivalent to a Core successor. -/
theorem backward_upTo {env : Env} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (Bk : BackwardUpTo env hn P host) (D : StructDecode env)
    (T : TypingFacts env hn) (R : HasStepRules env)
    (hP : ∃ t rules, env.findRel? "Step_pure" = some ([], "%~>%", t, rules))
    (hR : ∃ t rules, env.findRel? "Step_read" = some ([], "%~>%", t, rules))
    (c : Config H) (w : Value) (hc : Typed env hn c) (hs : SStep env (configV hn c) w) :
    ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  bwd_all Bk D T R hP hR (codeSize c.code + 1) c w (Nat.lt_succ_self _) hc hs

end Silmaril.Wasm.SpecTec.Sim.Bwd
