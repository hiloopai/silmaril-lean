module

public import Silmaril.Proofs.Wasm.Det.NaN.Frag

/-!
# One step of the fragment, canonicalised, is a step of the deterministic profile (proofs)

**`step_good`**: for every Core 3.0 host-free step `Step P Det.noHost c c'` at an **arbitrary**
profile `P` from a configuration of the fragment (`NCfg set c`):

* `c'` is in the fragment (`Good.inv`);
* the canonicalised configuration `canonCfg c` takes a step of silmaril-lean's deterministic
  profile `Pc = profile neverFail` to a configuration with the same canonical image as `c'`
  (`Good.proj`): the profile's choices (NaN payloads and signs) are invisible after
  canonicalisation, and every other rule of the fragment is profile-independent;
* without `global.set` (`set = false`) the store does not change (`Good.store`).

The proof is by induction on the step, one lemma per rule family. Rules of excluded
instructions (vector, table, memory, reference and aggregate families, `throw`, `try_table`,
handlers, `call_ref`, `call_indirect`, tail calls, branch-on-null/cast) contradict `NCfg`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.NaN
open Silmaril.Wasm.Numerics (Profile floatBinOp floatUnOp floatRelOp)

/-- The deterministic profile of the canonical runs. -/
abbrev Pc : Profile := profile neverFail

/-- What one step of the fragment gives. -/
structure Good (set : Bool) (c c' : Config Nat) : Prop where
  inv : NCfg set c'
  proj : ∃ e, Step Pc Det.noHost (canonCfg c) e ∧ canonCfg e = canonCfg c'
  store : set = false → c'.store = c.store

variable {set : Bool}

/-- A step that keeps the store and the frame. -/
theorem good_pure {s : Store Nat} {f : Frame} {L L' R R' : List Admin}
    (hc : NCfg set ⟨s, f, L⟩) (hinv : NAdms set R) (hL : canonAdmins L = L')
    (hstep : Step Pc Det.noHost ⟨canonStore s, canonFrame f, L'⟩ ⟨canonStore s, canonFrame f, R'⟩)
    (hR : canonAdmins R' = canonAdmins R) : Good set ⟨s, f, L⟩ ⟨s, f, R⟩ where
  inv := ⟨hinv, hc.2⟩
  proj := ⟨⟨canonStore s, canonFrame f, R'⟩, by subst hL; exact hstep, by
    simp only [canonCfg, canonStore_idem, canonFrame_idem, hR]⟩
  store := fun _ => rfl

/-- The code of a configuration in the fragment is in the fragment. -/
theorem NCfg.code {s : Store Nat} {f : Frame} {L : List Admin} (hc : NCfg set ⟨s, f, L⟩) :
    NAdms set L := hc.1

theorem canonAdmin_of_isCallRef {c : Admin} (hc : c.IsCallRef) : canonAdmin c = c := by
  cases c with
  | plain i => cases i <;> first | rfl | exact hc.elim
  | _ => first | rfl | exact hc.elim

theorem not_nAdm_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : ¬ NAdm set c := by
  cases c with
  | plain i => cases i <;> first | exact hc.elim | simp [NAdm, nanInstr, floatOk]
  | _ => first | exact hc.elim | simp [NAdm]

/-! ## Rule families -/

theorem good_parametric {s : Store Nat} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') (hc : NCfg set ⟨s, f, is⟩) : Good set ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | unreachable => exact good_pure hc (by simp [NAdm]) rfl (.parametric .unreachable) rfl
  | nop => exact good_pure hc trivial rfl (.parametric .nop) rfl
  | drop v =>
    exact good_pure hc trivial (by simp [canonInstr]) (.parametric (.drop (canonVal v))) rfl
  | @selectTrue v₁ v₂ c ts hc' =>
    exact good_pure hc (by simp) (by simp [canonInstr])
      (.parametric (.selectTrue (v₁ := canonVal v₁) (v₂ := canonVal v₂) (ts := ts) hc'))
      (by simp)
  | selectFalse v₁ v₂ ts =>
    exact good_pure hc (by simp) (by simp [canonInstr])
      (.parametric (.selectFalse (canonVal v₁) (canonVal v₂) ts)) (by simp)

theorem convOk_of {op : ConvertOp} (h : nanInstr set (.convert op) = true) : ConvOk op := by
  intro t ht
  subst ht
  simp [nanInstr, floatOk] at h

theorem good_floatBinOp {P : Profile} {s : Store Nat} {f : Frame} {t : FloatType}
    {op : FloatBinOp} {x y z : BitVec t.width} (hz : Numerics.floatBinOpP P t op x y z)
    (hc : NCfg set ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)]⟩) :
    Good set ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)]⟩ ⟨s, f, [.plain (.floatConst t z)]⟩ := by
  have hop : op ≠ .copysign := by simpa [NAdm, nanInstr, floatOk] using hc.1
  have hz' : canonBits (.float t) (floatBinOp t op (canonBits (.float t) x)
      (canonBits (.float t) y)) = canonBits (.float t) z := by
    rw [binOp_canon hop x y]
    exact (canon_floatBinOpP hop hz).symm
  exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl
    (.numeric (.floatBinOp (t := t) (op := op) (x := canonBits (.float t) x)
      (y := canonBits (.float t) y) rfl))
    (congrArg (fun b => [Admin.plain (Instr.floatConst t b)]) hz')

/-- The canonicalised operand of a conversion. -/
theorem canon_convert_lhs (op : ConvertOp) (x : BitVec op.source.width) :
    canonAdmins [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)] =
      [(Val.num ⟨op.source, canonBits op.source x⟩).toAdmin, .plain (.convert op)] := by
  simp only [canonAdmins_cons, canonAdmins_nil, canonAdmin_toAdmin, canonVal_num]
  rfl

theorem good_convert {P : Profile} {s : Store Nat} {f : Frame} {op : ConvertOp}
    {x : BitVec op.source.width} {z : BitVec op.target.width}
    (hz : Numerics.convertP P op x (.ok z))
    (hc : NCfg set ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩) :
    Good set ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩
      ⟨s, f, [(Val.num ⟨op.target, z⟩).toAdmin]⟩ := by
  have hr : RelC op.target (.ok z) (Numerics.convert op (canonBits op.source x)) :=
    convertP_canon (convOk_of hc.1.2.1) hz
  rcases hcv : Numerics.convert op (canonBits op.source x) with e | z'
  · exact absurd hr (by simp [hcv, RelC])
  · have hrz : canonBits op.target z = canonBits op.target z' := by simpa [hcv, RelC] using hr
    have hst : Step Pc Det.noHost
        ⟨canonStore s, canonFrame f,
          [(Val.num ⟨op.source, canonBits op.source x⟩).toAdmin, .plain (.convert op)]⟩
        ⟨canonStore s, canonFrame f, [(Val.num ⟨op.target, z'⟩).toAdmin]⟩ :=
      .numeric (.convert hcv.symm)
    have hR : canonAdmins [(Val.num ⟨op.target, z'⟩).toAdmin] =
        canonAdmins [(Val.num ⟨op.target, z⟩).toAdmin] := by
      simp only [canonAdmins_cons, canonAdmins_nil, canonAdmin_toAdmin, canonVal_num, hrz]
    exact good_pure hc (by simp) (canon_convert_lhs op x) hst hR

theorem good_convertTrap {P : Profile} {s : Store Nat} {f : Frame} {op : ConvertOp}
    {x : BitVec op.source.width} {e : Numerics.FloatTrap}
    (hz : Numerics.convertP P op x (.error e))
    (hc : NCfg set ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩) :
    Good set ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩ ⟨s, f, [.trap]⟩ := by
  have hr : RelC op.target (.error e) (Numerics.convert op (canonBits op.source x)) :=
    convertP_canon (convOk_of hc.1.2.1) hz
  rcases hcv : Numerics.convert op (canonBits op.source x) with e' | z'
  · have he : e = e' := by simpa [hcv, RelC] using hr
    have hst : Step Pc Det.noHost
        ⟨canonStore s, canonFrame f,
          [(Val.num ⟨op.source, canonBits op.source x⟩).toAdmin, .plain (.convert op)]⟩
        ⟨canonStore s, canonFrame f, [.trap]⟩ :=
      .numeric (.convertTrap (e := e) (show Except.error e = Numerics.convert op
        (canonBits op.source x) by rw [hcv, he]))
    exact good_pure hc (by simp [NAdm]) (canon_convert_lhs op x) hst rfl
  · exact absurd hr (by simp [hcv, RelC])

theorem good_numeric {P : Profile} {s : Store Nat} {f : Frame} {is is' : List Admin}
    (h : NumericStep P is is') (hc : NCfg set ⟨s, f, is⟩) : Good set ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | @intUnOp t op x =>
    exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl
      (.numeric (.intUnOp (t := t) (op := op) (x := x))) rfl
  | @floatUnOp t op x z hz =>
    exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl
      (.numeric (.floatUnOp (t := t) (op := op) (x := canonBits (.float t) x)
        (z := floatUnOp t op (canonBits (.float t) x)) rfl))
      (congrArg (fun b => [Admin.plain (Instr.floatConst t b)]) (canon_floatUnOpP hz).symm)
  | @intBinOp t op x y z hz =>
    exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl
      (.numeric (.intBinOp (t := t) (op := op) hz)) rfl
  | @intBinOpTrap t op x y e hz =>
    exact good_pure hc (by simp [NAdm]) rfl (.numeric (.intBinOpTrap (t := t) (op := op) hz)) rfl
  | floatBinOp hz => exact good_floatBinOp hz hc
  | @intTestOp t op x =>
    exact good_pure hc (by simp) rfl
      (.numeric (.intTestOp (t := t) (op := op) (x := x))) rfl
  | @intRelOp t op x y =>
    exact good_pure hc (by simp) rfl
      (.numeric (.intRelOp (t := t) (op := op) (x := x) (y := y))) rfl
  | @floatRelOp t op x y =>
    exact good_pure hc (by simp) rfl
      (.numeric (.floatRelOp (t := t) (op := op) (x := canonBits (.float t) x)
        (y := canonBits (.float t) y)))
      (congrArg (fun b => [constI32 b]) (relOp_canon op x y))
  | convert hz => exact good_convert hz hc
  | convertTrap hz => exact good_convertTrap hz hc

theorem vector_absurd {P : Profile} {is is' : List Admin} (h : VectorStep P is is')
    (hc : NAdms set is) : False := by
  cases h <;> simp [NAdm, nanInstr, floatOk] at hc

theorem table_absurd {P : Profile} {c c' : Config Nat} (h : TableStep P c c')
    (hc : NAdms set c.code) : False := by
  cases h <;> simp [NAdm, nanInstr, floatOk] at hc

theorem memory_absurd {P : Profile} {c c' : Config Nat} (h : MemoryStep P c c')
    (hc : NAdms set c.code) : False := by
  cases h <;> simp [NAdm, nanInstr, floatOk] at hc

theorem reference_absurd {c c' : Config Nat} (h : RefStep c c') (hc : NAdms set c.code) :
    False := by
  cases h <;> simp [NAdm, nanInstr, floatOk] at hc

theorem aggregate_absurd {c c' : Config Nat} (h : AggregateStep c c') (hc : NAdms set c.code) :
    False := by
  cases h <;> simp [NAdm, nanInstr, floatOk] at hc

theorem good_localSet {s : Store Nat} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) (hc : NCfg set ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩) :
    Good set ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩ := by
  have hx' : x.toNat < (canonFrame f).locals.length := by simpa using hx
  have hst : Step Pc Det.noHost (canonCfg ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩)
      ⟨canonStore s, (canonFrame f).setLocal x (canonVal v), []⟩ := by
    simpa [canonCfg, canonInstr] using
      (Step.variable (P := Pc) (host := Det.noHost) (VariableStep.localSet (s := canonStore s)
        (v := canonVal v) hx'))
  refine ⟨⟨trivial, hc.2⟩, ⟨_, hst, ?_⟩, fun _ => rfl⟩
  simp only [canonCfg, canonStore_idem, canonFrame_setLocal, canonFrame_idem, canonVal_idem]

theorem canonStore_global?' {s : Store Nat} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hg : s.global? f x = some (a, g)) :
    (canonStore s).global? (canonFrame f) x = some (a, { g with value := canonVal g.value }) := by
  rw [canonStore_global?]
  exact congrArg (Option.map _) hg

theorem good_globalSet {s : Store Nat} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    {v : Val} (hg : s.global? f x = some (a, g))
    (hc : NCfg set ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩) :
    Good set ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩ := by
  have hset : set = true := by simpa [NAdm, nanInstr] using hc.1.2.1
  have hst : Step Pc Det.noHost (canonCfg ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩)
      ⟨(canonStore s).setGlobal a (canonVal v), canonFrame f, []⟩ := by
    simpa [canonCfg, canonInstr] using
      (Step.variable (P := Pc) (host := Det.noHost)
        (VariableStep.globalSet (v := canonVal v) (canonStore_global?' hg)))
  refine ⟨⟨trivial, hc.2⟩, ⟨_, hst, ?_⟩, fun h₀ => absurd hset (by simp [h₀])⟩
  simp only [canonCfg, canonStore_setGlobal, canonStore_idem, canonFrame_idem, canonVal_idem]

theorem good_variable {c c' : Config Nat} (h : VariableStep c c') (hc : NCfg set c) :
    Good set c c' := by
  cases h with
  | @localGet s f x v hv =>
    have hv' : (canonFrame f).local? x = some (some (canonVal v)) := by
      rw [canonFrame_local?, hv]
      rfl
    exact good_pure hc (by simp) rfl (.variable (.localGet hv')) (by simp)
  | localSet hx => exact good_localSet hx hc
  | @localTee s f x v =>
    exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) (by simp [canonInstr])
      (.variable (.localTee (x := x) (v := canonVal v))) (by simp [canonInstr])
  | globalGet hg =>
    exact good_pure hc (by simp) rfl (.variable (.globalGet (canonStore_global?' hg))) (by simp)
  | globalSet hg => exact good_globalSet hg hc

/-! ## Context rules -/

theorem good_ctxtInstrs {s s' : Store Nat} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : Good set ⟨s, f, is⟩ ⟨s', f', is'⟩) (hc : NCfg set ⟨s, f, vals vs ++ is ++ rest⟩) :
    Good set ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  obtain ⟨⟨hi, hF⟩, ⟨⟨es, ef, ecode⟩, hst, he⟩, hstore⟩ := ih
  have hcode : NAdms set (vals vs ++ is ++ rest) := hc.1
  have hrest : NAdms set rest := (nAdms_append.mp hcode).2
  have hne' : vs.map canonVal ≠ [] ∨ canonAdmins rest ≠ [] := by
    rcases hne with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa [canonAdmins_eq_map] using h)
  have hst' : Step Pc Det.noHost (canonCfg ⟨s, f, vals vs ++ is ++ rest⟩)
      ⟨es, ef, vals (vs.map canonVal) ++ ecode ++ canonAdmins rest⟩ := by
    simpa [canonCfg] using Step.ctxtInstrs (vs := vs.map canonVal) (rest := canonAdmins rest) hst hne'
  have he' : canonStore es = canonStore s' ∧ canonFrame ef = canonFrame f' ∧
      canonAdmins ecode = canonAdmins is' := by
    simpa [canonCfg] using he
  refine ⟨⟨by simp [hi, hrest], hF⟩, ⟨_, hst', ?_⟩, hstore⟩
  simp only [canonCfg, canonAdmins_append, canonAdmins_vals, List.map_map, canonVal_comp,
    canonAdmins_idem, he'.1, he'.2.1, he'.2.2]

theorem good_ctxtLabel {s s' : Store Nat} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : Good set ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hc : NCfg set ⟨s, f, [.label n cont is]⟩) :
    Good set ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨⟨hi, hF⟩, ⟨⟨es, ef, ecode⟩, hst, he⟩, hstore⟩ := ih
  have hcont : nanInstrs set cont = true := hc.1.1.1
  have hst' : Step Pc Det.noHost (canonCfg ⟨s, f, [.label n cont is]⟩)
      ⟨es, ef, [.label n cont ecode]⟩ := by
    simpa [canonCfg] using Step.ctxtLabel (n := n) (cont := cont) hst
  have he' : canonStore es = canonStore s' ∧ canonFrame ef = canonFrame f' ∧
      canonAdmins ecode = canonAdmins is' := by
    simpa [canonCfg] using he
  refine ⟨⟨⟨⟨hcont, hi⟩, trivial⟩, hF⟩, ⟨_, hst', ?_⟩, hstore⟩
  simp only [canonCfg, canonAdmins_cons, canonAdmins_nil, canonAdmin_label, he'.1, he'.2.1,
    he'.2.2]

theorem good_ctxtFrame {s s' : Store Nat} {f fi fi' : Frame} {n : Nat}
    {is is' : List Admin} (ih : Good set ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Good set ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨⟨hi, hF⟩, ⟨⟨es, ef, ecode⟩, hst, he⟩, hstore⟩ := ih
  have hst' : Step Pc Det.noHost (canonCfg ⟨s, f, [.frame n fi is]⟩)
      ⟨es, canonFrame f, [.frame n ef ecode]⟩ := by
    simpa [canonCfg] using Step.ctxtFrame (f := canonFrame f) (n := n) hst
  have he' : canonStore es = canonStore s' ∧ canonFrame ef = canonFrame fi' ∧
      canonAdmins ecode = canonAdmins is' := by
    simpa [canonCfg] using he
  refine ⟨⟨⟨hi, trivial⟩, hF⟩, ⟨_, hst', ?_⟩, hstore⟩
  simp only [canonCfg, canonAdmins_cons, canonAdmins_nil, canonAdmin_frame, canonFrame_idem,
    he'.1, he'.2.1, he'.2.2]


/-! ## Other rules -/

/-- A handler is not in the fragment. -/
theorem handler_absurd {s : Store Nat} {f : Frame} {n : Nat} {cs : List Catch}
    {body rest : List Admin} (hc : NCfg set ⟨s, f, .handler n cs body :: rest⟩) : False :=
  hc.1.1

/-- Every administrative instruction of fragment code is in the fragment. -/
theorem nAdm_of_mem : ∀ {L : List Admin}, NAdms set L → ∀ {a : Admin}, a ∈ L → NAdm set a
  | [], _, _, ha => by cases ha
  | b :: L, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact nAdm_of_mem h.2 ha'

theorem good_callRefFunc {s : Store Nat} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst Nat} {ps rs : Validation.Ty (.list .val)} {code : Func}
    (hc' : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code)
    (hc : NCfg set ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    Good set ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  have hbody : NAdms set (expression code.body) := nFuncs_body hc.2 hf hcode
  have hn' : (vs.map canonVal).length = ps.length := by simpa using hn
  have hst : Step Pc Det.noHost ⟨canonStore s, canonFrame f, vals (vs.map canonVal) ++
      [.ref (.func a), c]⟩ ⟨canonStore s, canonFrame f, [.frame rs.length
        (Frame.forCall fi.module (vs.map canonVal) code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
    Step.callRefFunc hc' hf he hn' hcode
  refine good_pure hc ⟨⟨⟨by simp [nanInstrs], hbody⟩, trivial⟩, trivial⟩ ?_ hst ?_
  · simp [canonAdmin_of_isCallRef hc']
  · simp [canonFrame_forCall, List.map_map]

/-- **One step of the fragment**, at an arbitrary profile. -/
theorem step_good {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c') :
    NCfg set c → Good set c c' := by
  induction h with
  | parametric h => exact good_parametric h
  | numeric h => exact good_numeric h
  | vector h => exact fun hc => (vector_absurd h hc.1).elim
  | «variable» h => exact good_variable h
  | table h => exact fun hc => (table_absurd h hc.1).elim
  | memory h => exact fun hc => (memory_absurd h hc.1).elim
  | reference h => exact fun hc => (reference_absurd h hc.1).elim
  | aggregate h => exact fun hc => (aggregate_absurd h hc.1).elim
  | ctxtInstrs _ hne ih =>
    exact fun hc => good_ctxtInstrs hne (ih ⟨(nAdms_append.mp (nAdms_append.mp hc.1).1).2, hc.2⟩) hc
  | ctxtLabel _ ih => exact fun hc => good_ctxtLabel (ih ⟨hc.1.1.2, hc.2⟩) hc
  | ctxtHandler _ _ => exact fun hc => (handler_absurd hc).elim
  | ctxtFrame _ ih => exact fun hc => good_ctxtFrame (ih ⟨hc.1.1, hc.2⟩)
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro hc
    have hb : nanInstrs set body = true := by
      simpa [NAdm, nanInstr] using (nAdms_append.mp hc.1).2.1
    exact good_pure hc ⟨⟨by simp [nanInstrs], by simp [nAdms_expression.mpr hb]⟩, trivial⟩
      (by simp [canonInstr]) (.block (bt := bt) (body := body) (vs := vs.map canonVal) hbt
        (by simpa using hm)) (by simp)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro hc
    have hb : nanInstrs set body = true := by
      simpa [NAdm, nanInstr] using (nAdms_append.mp hc.1).2.1
    exact good_pure hc ⟨⟨by simp [nanInstrs, nanInstr, hb], by simp [nAdms_expression.mpr hb]⟩,
      trivial⟩ (by simp [canonInstr]) (.loop (bt := bt) (body := body) (vs := vs.map canonVal) hbt
        (by simpa using hm)) (by simp)
  | @ifTrue s f c bt b₁ b₂ hc' =>
    intro hc
    have hb : nanInstrs set b₁ = true ∧ nanInstrs set b₂ = true := by
      simpa [NAdm, nanInstr] using hc.1.2.1
    exact good_pure hc ⟨by simpa [NAdm, nanInstr] using hb.1, trivial⟩ rfl
      (.ifTrue (bt := bt) (b₁ := b₁) (b₂ := b₂) hc') rfl
  | @ifFalse s f bt b₁ b₂ =>
    intro hc
    have hb : nanInstrs set b₁ = true ∧ nanInstrs set b₂ = true := by
      simpa [NAdm, nanInstr] using hc.1.2.1
    exact good_pure hc ⟨by simpa [NAdm, nanInstr] using hb.2, trivial⟩ rfl
      (.ifFalse (bt := bt) (b₁ := b₁) (b₂ := b₂)) rfl
  | @labelVals s f n cont vs =>
    exact fun hc => good_pure hc (by simp) (by simp) (.labelVals (n := n) (cont := cont)
      (vs := vs.map canonVal)) (by simp)
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro hc
    have hcont : NAdms set (expression cont) := nAdms_expression.mpr hc.1.1.1
    exact good_pure hc (by simp [hcont]) (by simp [canonInstr])
      (.brLabelZero (n := n) (l := l) (vs' := vs'.map canonVal) (vs := vs.map canonVal) (cont := cont)
        (rest := canonAdmins rest) hl (by simpa using hn)) (by simp)
  | @brLabelSucc s f n cont vs l rest hl =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) (by simp [canonInstr])
      (.brLabelSucc (n := n) (cont := cont) (vs := vs.map canonVal) (rest := canonAdmins rest) hl)
      (by simp [canonInstr])
  | brHandler => exact fun hc => (handler_absurd hc).elim
  | @brIfTrue s f c l hc' =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl (.brIfTrue (l := l) hc')
      rfl
  | @brIfFalse s f l => exact fun hc => good_pure hc trivial rfl (.brIfFalse (l := l)) rfl
  | @brTableLt s f i ls l' l hi =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl
      (.brTableLt (l' := l') hi) rfl
  | @brTableGe s f i ls l' hi =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl (.brTableGe hi) rfl
  | brOnNullNull => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnNullAddr _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnNonNullNull => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnNonNullAddr _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnCastSucceed _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnCastFail _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnCastFailSucceed _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | brOnCastFailFail _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | @call s f x a fi hx hf =>
    exact fun hc => good_pure hc ⟨trivial, trivial, trivial⟩ rfl (.call hx hf) rfl
  | @callRefNull s f c hc' =>
    exact fun hc => good_pure hc (by simp [NAdm]) (by simp [canonAdmin_of_isCallRef hc'])
      (.callRefNull hc') rfl
  | callRefFunc hc' hf he hn hcode => exact good_callRefFunc hc' hf he hn hcode
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall _ _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | returnCallRefLabel hc' =>
    exact fun hc => (not_nAdm_returnCallRef hc' (nAdm_of_mem hc.1.1.2 (by simp))).elim
  | returnCallRefHandler _ => exact fun hc => (handler_absurd hc).elim
  | returnCallRefFrameNull hc' =>
    exact fun hc => (not_nAdm_returnCallRef hc' (nAdm_of_mem hc.1.1 (by simp))).elim
  | returnCallRefFrameAddr hc' _ _ _ =>
    exact fun hc => (not_nAdm_returnCallRef hc' (nAdm_of_mem hc.1.1 (by simp))).elim
  | callIndirect => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | returnCallIndirect => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | @frameVals s f fi n vs hn =>
    exact fun hc => good_pure hc (by simp) (by simp) (.frameVals (n := n) (fi := canonFrame fi)
      (vs := vs.map canonVal) (by simpa using hn)) (by simp)
  | @returnFrame s f fi n vs' vs rest hn =>
    exact fun hc => good_pure hc (by simp) (by simp [canonInstr])
      (.returnFrame (n := n) (fi := canonFrame fi) (vs' := vs'.map canonVal) (vs := vs.map canonVal)
        (rest := canonAdmins rest) (by simpa using hn)) (by simp)
  | @returnLabel s f n cont vs rest =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) (by simp [canonInstr])
      (.returnLabel (n := n) (cont := cont) (vs := vs.map canonVal) (rest := canonAdmins rest))
      (by simp [canonInstr])
  | returnHandler => exact fun hc => (handler_absurd hc).elim
  | throw _ _ _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | @throwRefNull s f =>
    exact fun hc => good_pure hc (by simp [NAdm]) rfl .throwRefNull rfl
  | @throwRefInstrs s f vs a rest hne =>
    intro hc
    have hne' : vs.map canonVal ≠ [] ∨ canonAdmins rest ≠ [] := by
      rcases hne with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa [canonAdmins_eq_map] using h)
    exact good_pure hc (by simp [NAdm, nanInstr, floatOk]) (by simp [canonInstr])
      (.throwRefInstrs (a := a) hne') rfl
  | @throwRefLabel s f n cont a =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl .throwRefLabel rfl
  | @throwRefFrame s f fi n a =>
    exact fun hc => good_pure hc (by simp [NAdm, nanInstr, floatOk]) rfl .throwRefFrame rfl
  | throwRefHandlerEmpty => exact fun hc => (handler_absurd hc).elim
  | throwRefHandlerCatch _ _ => exact fun hc => (handler_absurd hc).elim
  | throwRefHandlerCatchRef _ _ => exact fun hc => (handler_absurd hc).elim
  | throwRefHandlerCatchAll => exact fun hc => (handler_absurd hc).elim
  | throwRefHandlerCatchAllRef => exact fun hc => (handler_absurd hc).elim
  | throwRefHandlerNext _ => exact fun hc => (handler_absurd hc).elim
  | tryTable _ _ => exact fun hc => absurd hc.1 (by simp [NAdm, nanInstr, floatOk])
  | handlerVals => exact fun hc => (handler_absurd hc).elim
  | @trapInstrs s f vs rest hne =>
    intro hc
    have hne' : vs.map canonVal ≠ [] ∨ canonAdmins rest ≠ [] := by
      rcases hne with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa [canonAdmins_eq_map] using h)
    exact good_pure hc (by simp [NAdm]) (by simp) (.trapInstrs hne') rfl
  | @trapLabel s f n cont => exact fun hc => good_pure hc (by simp [NAdm]) rfl .trapLabel rfl
  | trapHandler => exact fun hc => (handler_absurd hc).elim
  | @trapFrame s f fi n => exact fun hc => good_pure hc (by simp [NAdm]) rfl .trapFrame rfl

end Silmaril.Proofs.Wasm.Det.NaN
