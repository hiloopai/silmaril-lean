module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatSeq

/-!
# Soundness of the component IR for sequences of calls with floats

* `seq_refToSpecF` (the reference half): every behaviour of a sequence of calls
  (`seqBehaviours`) on reference images of well-typed IR values is a chain of returned calls of
  the specification on admissible lowerings `calls'` of the calls (`NanCalls`), threading the
  Core store (`SeqSpec`), whose results the reference reports canonicalised (`canonResults`),
  followed by an outcome of the canonicalised specification (`specAtF`) of the last call on an
  admissible lowering `vs'`, at the store reached;
* `Simple.sound_seq_float`: with `seqSpecToIR` on `calls'` and `vs'`, the IR denotation plays
  `seqMoves c calls' wss` and matches the last outcome as `SeqIRObsF` prescribes;
* `Simple.sound_seq_float_deterministic`: under the deterministic component profile the
  lowerings are the canonicalisations (`canonCalls`, `canonAtList`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy)

local notation "IVal" => Silmaril.Wasm.Component.Val

export Silmaril.Wasm.Component.Reference (NanCalls canonResults canonCalls SeqIRObsF)

section Sound

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- One resolved call between calls, with floats. -/
theorem seq_stepF (hc : c.Good) (hf : SimpleFloatOk c) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {k : Nat}
    (R : ReadyAt I cs ι G k) (j : Fin c.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {m₁ : Machine.Config (E3 P) Unit}
    {rs : List Silmaril.Wasm.Component.Reference.Val}
    (hcall : Calls prof (refHost P).hr (D P)
      (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) ⟨k⟩ ⟨j⟩
      (vs.map toRefVal) m₁ (.resolved (some rs))) :
    ∃ vs' cs' ι' G' ws, NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      rs = (canonAtList c.exports[j].ty.results ws).map toRefVal ∧
      RetAt P c I c.exports[j] vs' (Store.mapH (fun _ => 0) cs) ws
        (Store.mapH (fun _ => 0) cs') ∧
      m₁ = readyCfg cs' ι' (liftedFuncs P (fun k => I.addrs.getD k 0) c) G' ∧
      ReadyAt I cs' ι' G' (k + 1) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have ht := trunK_of (prof := prof) R hff hvs hmax hres hmaxr hffr
    (liftedFuncs_get? c (fun k => I.addrs.getD k 0) j.isLt)
  obtain ⟨vs', hn, hck, hF⟩ := calls_factsF hI R (hc.core _ hx) ht hcall
  obtain ⟨cs', ws, rfl, hret, rfl⟩ := hF.2 _ rfl
  exact ⟨vs', cs', _, _, ws, hn, hck, rfl, hret, rfl,
    ⟨hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _, fresh_next R.fresh _ _ _ _ _⟩⟩

/-- **Sequences of resolved calls between calls with floats** are sequences of returned calls
of the specification on admissible lowerings. -/
theorem seq_invF (hc : c.Good) (hf : SimpleFloatOk c) (ha : c.Arity) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List IVal))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (rss : List (List Silmaril.Wasm.Component.Reference.Val)) (mₙ : Machine.Config (E3 P) Unit),
      ReadyAt I cs ι G k → TypedCalls c calls →
      SeqCalls prof (refHost P) (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k
        (callArgs c calls) rss mₙ →
      ∃ calls' cs' ι' G' wss, NanCalls prof c calls calls' ∧ TypedCalls c calls' ∧
        SeqSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls') wss
          (Store.mapH (fun _ => 0) cs') ∧ rss = canonResults c calls' wss ∧
        mₙ = readyCfg cs' ι' (liftedFuncs P (fun k => I.addrs.getD k 0) c) G' ∧
        ReadyAt I cs' ι' G' (k + calls.length)
  | [], cs, ι, G, k, rss, mₙ, R, _, hS => by
    cases hS
    refine ⟨[], cs, ι, G, [], List.Forall₂.nil, ?_, .nil _, rfl, rfl, R⟩
    intro _ h
    cases h
  | (j, vs) :: calls, cs, ι, G, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨vs', cs₁, ι₁, G₁, ws, hn, hck, rfl, hret, rfl, R₁⟩ :=
        seq_stepF hc hf ha hI R j hvs hcall
      obtain ⟨calls', cs', ι', G', wss, hN, ht', hseq, rfl, rfl, R'⟩ :=
        seq_invF hc hf ha hI calls cs₁ ι₁ G₁ (k + 1) _ _ R₁
          (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS'
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      refine ⟨(j, vs') :: calls', cs', ι', G', ws :: wss, .cons ⟨rfl, hn⟩ hN, ?_, .cons hret hseq,
        rfl, rfl, hk ▸ R'⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hck
      · exact ht' q hq

/-- The last call of a sequence, with floats. -/
theorem last_callF (hc : c.Good) (hf : SimpleFloatOk c) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {n : Nat}
    (R : ReadyAt I cs ι G n) (j : Fin c.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ callBehaviours prof (refHost P)
      (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) ⟨n⟩ ⟨j⟩ (vs.map toRefVal)) :
    ∃ vs', NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      b ∈ specAtF P c I c.exports[j] vs' (Store.mapH (fun _ => 0) cs) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have ht := trunK_of (prof := prof) R hff hvs hmax hres hmaxr hffr
    (liftedFuncs_get? c (fun k => I.addrs.getD k 0) j.isLt)
  rcases hb with ⟨m', out, hcalls, hpo⟩ | ⟨hpo, hd⟩
  · obtain ⟨vs', hn, hck, hF⟩ := calls_factsF hI R (hc.core _ hx) ht hcalls
    exact ⟨vs', hn, hck, hpo ▸ hF.1⟩
  · obtain ⟨vs', hn, hck, hF⟩ := diverges_factsF hI R (hc.core _ hx) ht hd
    exact ⟨vs', hn, hck, hpo ▸ hF⟩

/-- **The reference-machine half for sequences of calls with floats** (every profile, every
component choice profile). -/
theorem seq_refToSpecF (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List IVal))
    (j : Fin c.exports.length) (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (calls' : List (Fin c.exports.length × List IVal))
      (wss : List (List IVal)) (s : Silmaril.Wasm.Execution.Core.Store Nat) (vs' : List IVal),
      c.mod.IsInst I ∧ NanCalls prof c calls calls' ∧ TypedCalls c calls' ∧
      SeqSpec P c I I.store (specCalls c calls') wss s ∧ p.1 = canonResults c calls' wss ∧
      NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      p.2 ∈ specAtF P c I c.exports[j] vs' s := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P prof c hc hi
  rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · show ∃ (I' : Silmaril.Wasm.Game.ScalarInstance)
      (calls' : List (Fin c.exports.length × List IVal)) (wss : List (List IVal))
      (s : Silmaril.Wasm.Execution.Core.Store Nat) (vs' : List IVal),
      c.mod.IsInst I' ∧ NanCalls prof c calls calls' ∧ TypedCalls c calls' ∧
      SeqSpec P c I' I'.store (specCalls c calls') wss s ∧ p.1 = canonResults c calls' wss ∧
      NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      p.2 ∈ specAtF P c I' c.exports[j] vs' s
    have he : m₀ = afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c) ∧
        inst = ⟨0⟩ ∧ es = exportMap c := by
      simpa only [InstResult.instance.injEq] using hinst _ hr
    have hfs' : fs = calls.map fun q => (⟨q.1⟩ : FuncId) :=
      Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookup hc calls))
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMap_lookup hc j j.isLt))
    have hS₁ : SeqCalls prof (refHost P) (readyCfg cs {}
        (liftedFuncs P (fun k => I.addrs.getD k 0) c) ⟨[], [], [], [], [], [], []⟩) 0
        (callArgs c calls) p.1 mₙ := by
      have hS₀ : SeqCalls prof (refHost P) (afterInst P cs (liftedFuncs P
          (fun k => I.addrs.getD k 0) c)) 0 (fs.zip ((calls.map fun q =>
            (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd)) p.1 mₙ := he.1 ▸ hS
      rw [← zip_callArgs, ← hfs']
      exact hS₀
    obtain ⟨calls', cs', ι', G', wss, hN, ht', hseq, hrss, hmₙ, R'⟩ :=
      seq_invF hc hf ha hI calls cs {} _ 0 _ _ (ready_afterInst hI hcs) ht hS₁
    have hb' : p.2 ∈ callBehaviours prof (refHost P)
        (readyCfg cs' ι' (liftedFuncs P (fun k => I.addrs.getD k 0) c) G')
        ⟨0 + calls.length⟩ ⟨j⟩ (vs.map toRefVal) := by
      rw [← hmₙ, ← hf', Nat.zero_add, ← List.length_map (f := fun q =>
        (c.exports[q.1].name, q.2.map toRefVal))]
      exact hb
    obtain ⟨vs', hn, hck, hb''⟩ := last_callF hc hf ha hI R' j hvs hb'
    exact ⟨I, calls', wss, _, vs', hI, hN, ht', hcs ▸ hseq, hrss, hn, hck, hb''⟩
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

/-- **Soundness of the component IR for sequences of calls with floats** (outside variant
payloads; every profile, every component choice profile): every behaviour `p` of instantiating
`c.toRef`, calling its exports `calls` in order, each resolving, then export `j`, on reference
images of well-typed IR values, is the IR play of admissible lowerings `calls'` of the calls
(`NanCalls`), with IR results `wss` reported canonicalised (`p.1 = canonResults c calls' wss`),
and the last outcome is matched on an admissible lowering `vs'` of `vs` as `SeqIRObsF`
prescribes. -/
theorem Simple.sound_seq_float (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List IVal))
    (j : Fin c.exports.length) (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (calls' : List (Fin c.exports.length × List IVal)) (wss : List (List IVal))
      (vs' : List IVal), NanCalls prof c calls calls' ∧ TypedCalls c calls' ∧
      NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      p.1 = canonResults c calls' wss ∧ seqMoves c calls' wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsF c (c.toComp.den (modSem P)) calls' wss j vs' p.2 := by
  obtain ⟨I, calls', wss, s, vs', hI, hN, ht', hseq, hp1, hn, hck, hp2⟩ :=
    seq_refToSpecF P prof c hc hf hi ha calls j vs ht hvs p hp
  refine ⟨calls', wss, vs', hN, ht', hn, hck, hp1, seq_prefix hc hI hseq, ?_⟩
  rcases specAtF_cases hp2 with ⟨e, htr⟩ | e | ⟨ws, e, hr⟩
  · rw [e]
    exact seqSpecToIR P c hc I hI calls' wss s j vs' .traps hseq htr
  · rw [e]
    trivial
  · rw [e]
    obtain ⟨ws', e', hplay⟩ := seqSpecToIR P c hc I hI calls' wss s j vs' _ hseq hr
    obtain rfl := map_toRefVal_inj e'
    exact ⟨ws, rfl, hplay⟩

/-- Under the deterministic component profile the admissible lowerings of calls are their
canonicalisations. -/
theorem nanCalls_deterministic (c : Simple) :
    ∀ {calls calls' : List (Fin c.exports.length × List IVal)},
      NanCalls .deterministic c calls calls' → calls' = canonCalls c calls
  | [], [], .nil => rfl
  | (j, vs) :: _, (j', vs') :: _, .cons ⟨e, hn⟩ h => by
    obtain rfl : j' = j := e
    have hv : vs' = canonAtList c.exports[j'].ty.params vs := nanAtList_deterministic _ _ _ hn
    rw [nanCalls_deterministic c h, hv]
    rfl

/-- **Sequences with floats under the deterministic component profile**: the IR is called on
the canonicalised arguments. -/
theorem Simple.sound_seq_float_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List IVal))
    (j : Fin c.exports.length) (vs : List IVal) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Reference.Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours .deterministic (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List IVal), p.1 = canonResults c (canonCalls c calls) wss ∧
      seqMoves c (canonCalls c calls) wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsF c (c.toComp.den (modSem P)) (canonCalls c calls) wss j
        (canonAtList c.exports[j].ty.params vs) p.2 := by
  obtain ⟨calls', wss, vs', hN, -, hn, -, hp1, hpre, hobs⟩ :=
    Simple.sound_seq_float P .deterministic c hc hf hi ha calls j vs ht hvs p hp
  rw [nanCalls_deterministic c hN] at hp1 hpre hobs
  rw [nanAtList_deterministic _ _ _ hn] at hobs
  exact ⟨wss, hp1, hpre, hobs⟩

end Sound

end Silmaril.Proofs.Wasm.Component.Reference
