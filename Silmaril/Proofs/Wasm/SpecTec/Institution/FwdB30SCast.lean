module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact
public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Thms

/-!
# The cast rules of `Step_read` at `Wasm30.builtins`

At a cast redex `[ref r, cast]` the `Step` facts of `stepModel builtins` are those of the
backend reading (`Round6.Reading.SStepB`), which `Round6.Transfer` relates to the declarative
reading only away from cast redexes. So the inversion of `FwdB30X` is redone here under the
backend reading, with round 6's inversions of `Step` rules 1–5 (`Round6.Casts.inv_*B`):

* `Step/pure` and the rules from 6 on agree with the declarative reading
  (`Reading.firesB_step_iff`), and every row of `Step_pure` and of `Step` from rule 6 on names a
  constructor that is neither a reference's nor a cast's (`pair_rows`, kernel `decide`);
* `ctxt-instrs` steps a proper infix of at most one instruction, on which nothing fires
  (`not_sstepB_small`): the non-cast rules of `Step_read` are dead by their constructors
  (`Round6.Casts.readCheck_at`, `Reading.deadAt_of_tags`), the cast rules fire only at a cast
  pair (`Round6.Casts.deadAt_castRule`), and `ctxt-label`, `ctxt-handler`, `ctxt-frame` name a
  context;
* the three other context rules name a context.

What is left is `Step/read` at the whole redex (`sreadB_of_sstepB_pair`). No law of the
primitives is used.

* `castRead_builtins`, `castRead_two_sided`: on `DomDet`, at every `FwdX30Fin.CastRead` redex,
  a `Step_read` fact of `stepModel builtins` exists to Core's successor up to `CfgRel`, and every
  such fact to typed code is that successor up to `CfgRel`.
* `castRead_exact`: the successors (`[i32.const 0/1]`, `[ref r]`, `[TRAP]`, `[ref r, br l]`)
  are rigid, so the fact is to the image of Core's successor itself.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure cfgV_inj)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB SStepB SReadB)
open Silmaril.Wasm.SpecTec.Sim.Round6.Casts (CastPair pairTags)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

variable {H : Type} {hn : H → String}

/-! ## Refutations by constructor -/

/-- Every row of `Step_pure`, and of `Step` from rule 6 on, names a constructor that is neither
a reference's nor a cast's. -/
theorem pair_rows :
    (pureInfoT.all (outside pairTags) && (stepInfoT.drop 6).all (outside pairTags)) = true := by
  decide +kernel

/-- No `Step_pure` rule fires on a code of references and casts. -/
theorem not_fires_pure_pair (B : Builtins) {l : List Value} (hl : TagsIn pairTags l) (j : Nat)
    (v : Value) : ¬ Fires (simEnv B) "Step_pure" j (.tuple [.list l, v]) := by
  have hp := pair_rows
  simp only [Bool.and_eq_true] at hp
  exact not_fires_of_blk (tables_simEnv B).pureT (Nat.zero_le j) fun row hrow =>
    ⟨pairTags, l.length, .inl ⟨l, rfl, hl, rfl⟩,
      .inl (outside_spec (List.all_eq_true.1 hp.1 row (by simpa using hrow)))⟩

/-- No `Step` rule from rule 6 on fires on a code of references and casts. -/
theorem not_fires_step_pair (B : Builtins) {l : List Value} (hl : TagsIn pairTags l) {i : Nat}
    (hi : 6 ≤ i) (z v : Value) : ¬ Fires (simEnv B) "Step" i (.tuple [cfgV z l, v]) := by
  have hp := pair_rows
  simp only [Bool.and_eq_true] at hp
  exact not_fires_of_blk (tables_simEnv B).stepT hi fun row hrow =>
    ⟨pairTags, l.length, .inr ⟨z, l, rfl, hl, rfl⟩,
      .inl (outside_spec (List.all_eq_true.1 hp.2 row hrow))⟩

/-- **No `Step_read` rule fires under the backend reading** at a code of references and casts
that is not a cast pair. -/
theorem not_firesB_read_small (B : Builtins) {s : Store H} {f : Frame} {code : List Admin}
    (ht : TagsIn pairTags (adminsToV code)) (hnp : ¬ CastPair code) (j : Nat) (b : Value) :
    ¬ FiresB (simEnv B) "Step_read" j (.tuple [configV hn ⟨s, f, code⟩, b]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  by_cases hk : j ∈ Round5.Read.readDoneK
  · exact Round6.Casts.deadAt_castRule hrel hk hr hnp _ _ _ hb
  · obtain ⟨-, hno, op, hop, hS⟩ := Round6.Casts.readCheck_at hrel hr hk
    exact Round6.Reading.deadAt_of_tags (.inr ⟨_, _, rfl, ht⟩) hno hop hS _ _ _ hb

/-- A one-instruction code naming `op` is not a code whose constructors avoid `op`. -/
theorem not_ctx_one {l : List Value} {S : List MixopS} (ht : TagsIn S l) {z z' x : Value}
    {op : MixopS} (hop : op ∉ S) (h : cfgV z l = cfgV z' [.case op x]) : False :=
  hop (ht _ ((cfgV_inj h).2 ▸ List.mem_singleton_self _) op x rfl)

/-- The context constructors are not references or casts. -/
theorem ctx_not_pair : "LABEL_%{%}%" ∉ pairTags ∧ "HANDLER_%{%}%" ∉ pairTags ∧
    "FRAME_%{%}%" ∉ pairTags := by
  simp [pairTags, Round6.Casts.refTags, Round6.Reading.castTags]

/-! ## Rules other than `Step/read` and `ctxt-instrs` -/

/-- `Step/pure` does not fire, under the backend reading, at a code of references and casts. -/
theorem not_firesB0_pair (B : Builtins) {z : Value} {l : List Value} (ht : TagsIn pairTags l)
    (w : Value) : ¬ FiresB (simEnv B) "Step" 0 (.tuple [cfgV z l, w]) := by
  intro hf
  have hf' : Fires (simEnv B) "Step" 0 (.tuple [cfgV z l, w]) :=
    (Round6.Reading.firesB_step_iff B (.inl rfl)).1 hf
  obtain ⟨z', is, js, h₁, -, hq⟩ := inv_pure (tables_simEnv B).rules.pure hf'
  obtain ⟨tp, rp, hrelp⟩ := (tables_simEnv B).pure
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
  have hl : l = is := (cfgV_inj h₁).2
  exact not_fires_pure_pair B ht j _ (hl ▸ hj)

/-- `ctxt-label`, `ctxt-handler` and `ctxt-frame` do not fire, under the backend reading, at a
code of references and casts. -/
theorem not_firesB_ctx_pair (B : Builtins) {z : Value} {l : List Value} (ht : TagsIn pairTags l)
    {i : Nat} (hi3 : 3 ≤ i) (hi : i < 6) (w : Value) :
    ¬ FiresB (simEnv B) "Step" i (.tuple [cfgV z l, w]) := by
  intro hf
  have R := (tables_simEnv B).rules
  rcases (show i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl
  · obtain ⟨z₁, z₁', n, cont, is, is', h₁, -, -⟩ := Round6.Casts.inv_ctxtLabelB R.ctxtLabel hf
    exact not_ctx_one ht ctx_not_pair.1 h₁
  · obtain ⟨z₁, z₁', n, cs, is, is', h₁, -, -⟩ := Round6.Casts.inv_ctxtHandlerB R.ctxtHandler hf
    exact not_ctx_one ht ctx_not_pair.2.1 h₁
  · obtain ⟨s₁, s₁', f₁, fr, fr', n, is, is', h₁, -, -⟩ := Round6.Casts.inv_ctxtFrameB R.ctxtFrame hf
    exact not_ctx_one ht ctx_not_pair.2.2 h₁

/-- **No `Step` rule but `Step/read` and `ctxt-instrs` fires**, under the backend reading, at a
code of references and casts. -/
theorem not_firesB_pair_rest (B : Builtins) {z : Value} {l : List Value} (ht : TagsIn pairTags l)
    {i : Nat} (h1 : i ≠ 1) (h2 : i ≠ 2) (w : Value) :
    ¬ FiresB (simEnv B) "Step" i (.tuple [cfgV z l, w]) := by
  rcases Nat.lt_or_ge i 6 with hi | hi
  · rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · have h0 : i = 0 := by omega
      exact h0 ▸ not_firesB0_pair B ht w
    · exact not_firesB_ctx_pair B ht hi3 hi w
  · exact fun hf => not_fires_step_pair B ht hi z w
      ((Round6.Reading.firesB_step_iff B (.inr hi)).1 hf)

/-- `Step/read` does not fire, under the backend reading, at a code of references and casts that
is not a cast pair. -/
theorem not_firesB1_small (B : Builtins) {s : Store H} {f : Frame} {code : List Admin}
    (ht : TagsIn pairTags (adminsToV code)) (hnp : ¬ CastPair code) (w : Value) :
    ¬ FiresB (simEnv B) "Step" 1 (.tuple [configV hn ⟨s, f, code⟩, w]) := by
  intro hf
  obtain ⟨z, is, js, h₁, -, hq⟩ := Round6.Casts.inv_readB (tables_simEnv B).rules.read hf
  obtain ⟨tr, rr, hrelr⟩ := Round6.Reading.findRel_read B
  obtain ⟨j, hj⟩ := (Round6.Reading.dderivesB_iff_firesB hrelr).1 hq
  exact not_firesB_read_small B ht hnp j _ (h₁ ▸ hj)

/-- A `Step` fact of the backend reading fires some rule of `Step`. -/
theorem firesB_of_sstepB (B : Builtins) {v w : Value} (hs : SStepB (simEnv B) v w) :
    ∃ i, FiresB (simEnv B) "Step" i (.tuple [v, w]) := by
  obtain ⟨tt, rules, hrel⟩ := (tables_simEnv B).step
  exact (Round6.Reading.dderivesB_iff_firesB hrel).1 hs

/-! ## Short codes take no step -/

/-- **No `Step` rule but `ctxt-instrs` fires under the backend reading** at a code of at most
one reference or cast. -/
theorem not_firesB_small (B : Builtins) {s : Store H} {f : Frame} {code : List Admin}
    (hlen : code.length ≤ 1) (ht : TagsIn pairTags (adminsToV code)) {i : Nat} (hi : i ≠ 2)
    (w : Value) : ¬ FiresB (simEnv B) "Step" i (.tuple [configV hn ⟨s, f, code⟩, w]) := by
  have hnp : ¬ CastPair code := fun ⟨r, i', he, _⟩ => by
    have h2 : code.length = 2 := by rw [he]; rfl
    omega
  by_cases h1 : i = 1
  · exact h1 ▸ not_firesB1_small B ht hnp w
  · exact not_firesB_pair_rest B ht h1 hi w

/-- The middle of a split of a code of at most one instruction, with a non-empty side, is
empty. -/
theorem infix_nil {l : List Value} (hlen : l.length ≤ 1) {vs is rest : List Value}
    (hne : vs ≠ [] ∨ rest ≠ []) (hl : l = vs ++ is ++ rest) : is = [] := by
  have e : l.length = vs.length + is.length + rest.length := by
    rw [hl]
    simp only [List.length_append]
  rcases hne with h | h
  · have := List.length_pos_iff.2 h
    exact List.eq_nil_of_length_eq_zero (by omega)
  · have := List.length_pos_iff.2 h
    exact List.eq_nil_of_length_eq_zero (by omega)

/-- The empty code takes no step under the backend reading. -/
theorem not_sstepB_nil (B : Builtins) {s : Store H} {f : Frame} (w : Value) :
    ¬ SStepB (simEnv B) (configV hn ⟨s, f, []⟩) w := by
  intro hs
  obtain ⟨i, hf⟩ := firesB_of_sstepB B hs
  by_cases hi : i = 2
  · obtain ⟨z, z', vs, is, is', rest, -, hne, h₁, -, -⟩ :=
      Round6.Casts.inv_ctxtInstrsB (tables_simEnv B).rules.ctxtInstrs (hi ▸ hf)
    have hl : ([] : List Value) = vs ++ is ++ rest := (cfgV_inj h₁).2
    rcases hne with h | h <;> exact h (by simp_all)
  · exact not_firesB_small B (by simp) (fun x hx => absurd hx (by simp [adminsToV_eq_map])) hi
      w hf

/-- **A code of at most one reference or cast takes no step** under the backend reading. -/
theorem not_sstepB_small (B : Builtins) {s : Store H} {f : Frame} {code : List Admin}
    (hlen : code.length ≤ 1) (ht : TagsIn pairTags (adminsToV code)) (w : Value) :
    ¬ SStepB (simEnv B) (configV hn ⟨s, f, code⟩) w := by
  intro hs
  obtain ⟨i, hf⟩ := firesB_of_sstepB B hs
  by_cases hi : i = 2
  · obtain ⟨z, z', vs, is, is', rest, -, hne, h₁, -, hs'⟩ :=
      Round6.Casts.inv_ctxtInstrsB (tables_simEnv B).rules.ctxtInstrs (hi ▸ hf)
    have hz : stateV hn s f = z := (cfgV_inj h₁).1
    have his : is = [] :=
      infix_nil (by rw [adminsToV_length]; exact hlen) hne (cfgV_inj h₁).2
    have hs'' : SStepB (simEnv B) (configV hn ⟨s, f, []⟩) (cfgV z' is') := by
      have e : cfgV z is = configV hn ⟨s, f, []⟩ := by rw [Bwd.configV_eq, hz, his]; rfl
      exact e ▸ hs'
    exact not_sstepB_nil B _ hs''
  · exact not_firesB_small B hlen ht hi w hf

/-! ## The inversion at a cast pair -/

/-- The image of a cast pair names references and casts only. -/
theorem tagsIn_pair {r : Ref} {i : Instr} (hi : Round6.Target.castInstr i = true) :
    TagsIn pairTags (adminsToV [.ref r, .plain i]) := by
  intro x hx op w hxe
  have hx' : x = adminToV (.ref r) ∨ x = adminToV (.plain i) := by simpa [adminsToV] using hx
  rcases hx' with rfl | rfl
  · rw [Typing.adminToV_case hxe]
    exact List.mem_append_left _ (Round6.Casts.refHead_mem r)
  · rw [Typing.adminToV_case hxe]
    exact List.mem_append_right _ (Round6.Casts.castHead_mem hi)

/-- A proper infix of a cast pair is the image of a code of at most one reference or cast. -/
theorem pair_infix {r : Ref} {i : Instr} (hi : Round6.Target.castInstr i = true)
    {vs is rest : List Value} (hne : vs ≠ [] ∨ rest ≠ [])
    (hl : adminsToV [.ref r, .plain i] = vs ++ is ++ rest) :
    ∃ code : List Admin, is = adminsToV code ∧ code.length ≤ 1 ∧
      TagsIn pairTags (adminsToV code) := by
  have hlen : is.length ≤ 1 := by
    have e := congrArg List.length hl
    simp only [adminsToV_length, List.length_append, List.length_cons, List.length_nil] at e
    rcases hne with h | h
    · have := List.length_pos_iff.2 h
      omega
    · have := List.length_pos_iff.2 h
      omega
  have hsub : ∀ x ∈ is, x ∈ adminsToV [.ref r, .plain i] := fun x hx => by
    rw [hl]
    simp [hx]
  match is, hlen, hsub with
  | [], _, _ => exact ⟨[], rfl, by simp, fun x hx => absurd hx (by simp [adminsToV_eq_map])⟩
  | [x], _, hsub =>
    have hx : x ∈ List.map adminToV [.ref r, .plain i] := by
      rw [← adminsToV_eq_map]
      exact hsub x (List.mem_singleton_self _)
    obtain ⟨a, -, ha⟩ := List.mem_map.1 hx
    refine ⟨[a], by rw [← ha]; rfl, by simp, tagsIn_of_subset (tagsIn_pair (r := r) hi) fun y hy => ?_⟩
    have hy' : y = x := by simpa [← ha, adminsToV] using hy
    exact hy' ▸ hsub x (List.mem_singleton_self _)

/-- `ctxt-instrs` does not fire, under the backend reading, at a cast pair. -/
theorem not_firesB2_pair (B : Builtins) {s : Store H} {f : Frame} {r : Ref} {i : Instr}
    (hi : Round6.Target.castInstr i = true) (w : Value) :
    ¬ FiresB (simEnv B) "Step" 2 (.tuple [configV hn ⟨s, f, [.ref r, .plain i]⟩, w]) := by
  intro hf
  obtain ⟨z, z', vs, is, is', rest, -, hne, h₁, -, hs'⟩ :=
    Round6.Casts.inv_ctxtInstrsB (tables_simEnv B).rules.ctxtInstrs hf
  have hz : stateV hn s f = z := (cfgV_inj h₁).1
  obtain ⟨code, hcode, hcl, htc⟩ : ∃ code : List Admin, is = adminsToV code ∧ code.length ≤ 1 ∧
      TagsIn pairTags (adminsToV code) := pair_infix hi hne (cfgV_inj h₁).2
  have hs'' : SStepB (simEnv B) (configV hn ⟨s, f, code⟩) (cfgV z' is') := by
    rw [Bwd.configV_eq, hz, ← hcode]
    exact hs'
  exact not_sstepB_small B hcl htc _ hs''

/-- **Inversion at a cast pair, under the backend reading**: at every `simEnv B`, a `Step`
fact from the image of `[ref r, cast]` is `Step/read` at the whole pair. -/
theorem sreadB_of_sstepB_pair (B : Builtins) {s : Store H} {f : Frame} {r : Ref} {i : Instr}
    (hi : Round6.Target.castInstr i = true) {w : Value}
    (hs : SStepB (simEnv B) (configV hn ⟨s, f, [.ref r, .plain i]⟩) w) :
    ∃ js, w = cfgV (stateV hn s f) js ∧
      SReadB (simEnv B) (configV hn ⟨s, f, [.ref r, .plain i]⟩) js := by
  obtain ⟨n, hf⟩ := firesB_of_sstepB B hs
  by_cases h1 : n = 1
  · obtain ⟨z, is, js, h₁, h₂, hq⟩ := Round6.Casts.inv_readB (tables_simEnv B).rules.read (h1 ▸ hf)
    have hz : stateV hn s f = z := (cfgV_inj h₁).1
    exact ⟨js, hz ▸ h₂, h₁ ▸ hq⟩
  by_cases h2 : n = 2
  · exact (not_firesB2_pair B hi w (h2 ▸ hf)).elim
  · exact (not_firesB_pair_rest B (tagsIn_pair hi) h1 h2 w hf).elim

/-! ## At `Wasm30.builtins` -/

/-- A cast redex is a cast pair. -/
theorem castTop_pair {c c' : Config H} (h : Round6.Casts.CastTop c c') :
    ∃ rf i, c.code = [.ref rf, .plain i] ∧ Round6.Target.castInstr i = true := by
  cases h <;> exact ⟨_, _, rfl, rfl⟩

/-- **The successors of the cast rules are rigid.** -/
theorem castRead_rigid {c : Config H} {is' : List Admin} (h : FwdX30Fin.CastRead c is') :
    RigidV (adminsToV is') := by
  unfold FwdX30Fin.CastRead at h
  generalize hc' : (⟨c.store, c.frame, is'⟩ : Config H) = c' at h
  have e : is' = c'.code := by rw [← hc']
  rw [e]
  cases h <;> rigid_tac

section Builtins

variable {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- **The cast rules at `builtins`**: on `DomDet`, at a `CastRead` redex, a `Step_read` fact
of `stepModel builtins` exists to Core's successor up to `CfgRel`. -/
theorem castRead_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : FwdX30Fin.CastRead c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨w, hw, hrel⟩, -⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h.step
  obtain ⟨rf, i, hcode, hi⟩ := castTop_pair h
  obtain ⟨s, f, code⟩ := c
  simp only at hcode
  subst hcode
  obtain ⟨js, rfl, hq⟩ := sreadB_of_sstepB_pair _ hi hw
  exact ⟨js, hq, hrel⟩

/-- **The cast rules at `builtins`, two-sided**: the fact exists, and every `Step_read` fact of
`stepModel builtins` from the configuration to typed code is Core's successor up to
`CfgRel`. -/
theorem castRead_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : FwdX30Fin.CastRead c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
          (cfgV (stateV hn c.store c.frame) js) :=
  ⟨castRead_builtins hc h, fun _ hjs hq => FwdX30Fin.readFact_unique_builtins hc h.step hjs hq⟩

/-- **The cast rules at `builtins`, exactly**: on `DomDet`, the image of Core's successor code
is a `Step_read` fact of `stepModel builtins`. -/
theorem castRead_exact {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : FwdX30Fin.CastRead c is') :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) :=
  exact_of_cfgRel (Q := fun js => (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]))
    (castRead_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h) (castRead_rigid h)

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
