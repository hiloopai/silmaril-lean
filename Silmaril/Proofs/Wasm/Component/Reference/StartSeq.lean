module

public import Silmaril.Proofs.Wasm.Component.Reference.StartPhase

/-!
# The reference half with a start function

`seq_refToSpecS`: for a simple component whose module may have a start function, every
behaviour of a sequence of calls (`seqBehaviours`) is a chain of returned canonical-ABI calls
from a store the start phase returns at (well formed), followed by an outcome of the last call's
specification; or a trap of the instantiation, where the start phase fails; or divergence.

The calls after the start function are the calls between calls of `MultiCall` (`calls_facts`,
`diverges_facts`) with the functions `startFn a :: liftedFuncs` (`seq_stepP`, `seq_invP`,
`last_callP`, generalising `MultiSeq` to a prefix of functions before the lifts), at the module
without its start function (`NumModule.IsInstS.noStart`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy)

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Calls after a prefix of functions -/

theorem liftedFuncs_get?P (pre : List (CFuncInst (core3P P))) (c : Simple) (addr : Nat → Nat)
    {j : Nat} (hj : j < c.exports.length) :
    (pre ++ liftedFuncs P addr c)[pre.length + j]? =
      some (.lifted (addr c.exports[j].core) (liftedFt c.exports[j]) {} ⟨0⟩) := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact liftedFuncs_get? c addr hj

/-- One resolved call between calls, the lifts after `pre`. -/
theorem seq_stepP (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    (pre : List (CFuncInst (core3P P)))
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {k : Nat}
    (R : ReadyAt I cs ι G k) (j : Fin c.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {m₁ : Machine.Config (E3 P) Unit}
    {rs : List Val}
    (hcall : Calls prof (refHost P).hr (D P)
      (readyCfg cs ι (pre ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) G) ⟨k⟩
      ⟨pre.length + j⟩ (vs.map toRefVal) m₁ (.resolved (some rs))) :
    ∃ cs' ι' G' ws, rs = ws.map toRefVal ∧
      RetAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) ws (Store.mapH (fun _ => 0) cs') ∧
      m₁ = readyCfg cs' ι' (pre ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) G' ∧
      ReadyAt I cs' ι' G' (k + 1) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have hF := calls_facts (prof := prof) C R hff hmax hres hmaxr hffr
    (liftedFuncs_get?P pre c (fun k => I.addrs.getD k 0) j.isLt) hcall
  obtain ⟨cs', ws, rfl, hret, rfl⟩ := hF.2 rs rfl
  exact ⟨cs', _, _, ws, rfl, hret, rfl,
    ⟨hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _, fresh_next R.fresh _ _ _ _ _⟩⟩

/-- The calls of `calls` as reference calls after the prefix `pre`. -/
def callArgsP (c : Simple) (n : Nat)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (FuncId × List Val) :=
  calls.map fun q => (⟨n + q.1⟩, q.2.map toRefVal)

/-- **Sequences of resolved calls between calls**, the lifts after `pre`. -/
theorem seq_invP (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    (pre : List (CFuncInst (core3P P))) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (rss : List (List Val)) (mₙ : Machine.Config (E3 P) Unit),
      ReadyAt I cs ι G k → TypedCalls c calls →
      SeqCalls prof (refHost P) (readyCfg cs ι (pre ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) G)
        k (callArgsP c pre.length calls) rss mₙ →
      ∃ cs' ι' G' wss, SeqSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) wss
          (Store.mapH (fun _ => 0) cs') ∧ rss = wss.map (·.map toRefVal) ∧
        mₙ = readyCfg cs' ι' (pre ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) G' ∧
        ReadyAt I cs' ι' G' (k + calls.length)
  | [], cs, ι, G, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨cs, ι, G, [], .nil _, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ι, G, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨cs₁, ι₁, G₁, ws, rfl, hret, rfl, R₁⟩ := seq_stepP hc hf ha hI pre R j hvs hcall
      obtain ⟨cs', ι', G', wss, hseq, rfl, rfl, R'⟩ := seq_invP hc hf ha hI pre calls cs₁ ι₁ G₁
        (k + 1) _ _ R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS'
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      exact ⟨cs', ι', G', ws :: wss, .cons hret hseq, rfl, rfl, hk ▸ R'⟩

/-- The last call of a sequence, the lifts after `pre`. -/
theorem last_callP (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    (pre : List (CFuncInst (core3P P)))
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {n : Nat}
    (R : ReadyAt I cs ι G n) (j : Fin c.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ callBehaviours prof (refHost P)
      (readyCfg cs ι (pre ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) G) ⟨n⟩
      ⟨pre.length + j⟩ (vs.map toRefVal)) :
    b ∈ specAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have hget := liftedFuncs_get?P (P := P) pre c (fun k => I.addrs.getD k 0) j.isLt
  rcases hb with ⟨m', out, hcalls, hpo⟩ | ⟨hpo, hd⟩
  · exact hpo ▸ (calls_facts C R hff hmax hres hmaxr hffr hget hcalls).1
  · exact hpo ▸ diverges_facts C R hff hmax hres hmaxr hffr hget hd

/-! ## Assembly -/

/-- `SeqSpec` does not depend on the component's module. -/
theorem seqSpec_noStart {c : Simple} {s s' : Silmaril.Wasm.Execution.Core.Store Nat}
    {calls : List (SimpleExport × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} (h : SeqSpec P c I s calls wss s') :
    SeqSpec P c.noStart I s calls wss s' := by
  induction h with
  | nil s => exact .nil s
  | cons h _ ih => exact .cons ⟨h.typed, h.run⟩ ih

theorem mapM_lookupS (hc : c.Good) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)),
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).mapM
          (fun q => (exportMapS c).lookup q.1) = some (calls.map fun q => (⟨1 + q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    have hq : (exportMapS c).lookup c.exports[q.1].name = some ⟨1 + q.1⟩ :=
      lookup_mapIdx_name (·.name) 1 c.exports q.1 q.1.isLt hc.names
    simp only [List.map_cons, List.mapM_cons, hq, mapM_lookupS hc calls]
    rfl

theorem zip_callArgsP (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    (calls.map fun q => (⟨1 + q.1⟩ : FuncId)).zip
        ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
      callArgsP c 1 calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

/-- The configuration after the start function is between calls. -/
theorem ready_afterStart {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P P).Store (CanonHost (core3P P))} (a : Nat)
    (hw : I.WellFormed (Store.mapH (fun _ => 0) cs)) :
    ReadyAt I cs instAfterStart (startGarb P a) 0 where
  wf := hw
  threads := threadsOk_after _ _
  fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) }

/-- **The reference half with a start function** (every profile, every component choice
profile): a behaviour of a sequence of calls is a chain of returned calls of the specification
from a store the start phase returns at, and an outcome of the last call; a trap of the
instantiation where the start phase fails; or divergence. -/
theorem seq_refToSpecS (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.InstS) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    (∃ (I : Silmaril.Wasm.Game.ScalarInstance) (st : Option Nat)
        (s₀ : Silmaril.Wasm.Execution.Core.Store Nat) (wss : List (List Silmaril.Wasm.Component.Val))
        (s : Silmaril.Wasm.Execution.Core.Store Nat), c.mod.IsInstS I st ∧
        Silmaril.Wasm.Game.StartsTo P Silmaril.Wasm.SingleThreaded.Det.noHost I.store st s₀ ∧
        I.WellFormed s₀ ∧ SeqSpec P c.noStart I s₀ (specCalls c calls) wss s ∧
        p.1 = wss.map (·.map toRefVal) ∧ p.2 ∈ specAt P c I c.exports[j] vs s) ∨
      (p = ([], .traps) ∧ c.mod.StartFails P) ∨ p = ([], .diverges) := by
  obtain ⟨I, st, cs, ci, hF⟩ := coreFactsS (Pf := P) hc hi
  cases st with
  | none =>
    have hi' : c.Inst := ⟨⟨I, hF.isInst.isInst_none⟩, hi.names⟩
    obtain ⟨I', wss, s, hI', hseq, h1, h2⟩ := seq_refToSpec P prof c hc hf hi' ha calls j vs ht hvs p hp
    refine .inl ⟨I', none, I'.store, wss, s, ⟨hI'.1.elim fun mt h => ⟨mt,
      Silmaril.Wasm.Game.isInstanceStart_none_iff.2 h⟩, hI'.2⟩,
      Silmaril.Wasm.Game.startsTo_none.2 rfl, hI'.1.choose_spec.ok, seqSpec_noStart hseq, h1, h2⟩
  | some a =>
    show _ ∨ _
    have hI₀ : c.noStart.mod.IsInst I := hF.isInst.noStart
    have hc₀ : c.noStart.Good := ⟨hc.names, hc.core⟩
    rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨hpe, hr⟩ | ⟨hpe, hr⟩
    · show _ ∨ _
      rcases instBehaviours_start hF prof _ hr with ⟨y, hy, ⟨ys, hst⟩, he⟩ | ⟨-, -, -, he⟩ | he
      · show _ ∨ _
        obtain ⟨rfl, -, rfl⟩ : m₀ = afterStartCfg P y.1 a (fun k => I.addrs.getD k 0) c ∧
            inst = ⟨0⟩ ∧ es = exportMapS c := by
          simpa only [InstResult.instance.injEq] using he
        obtain ⟨hstart, hw⟩ := start_returns hF hy hst
        have hfs' : fs = calls.map fun q => (⟨1 + q.1⟩ : FuncId) :=
          Option.some.inj (hfs.symm.trans (mapM_lookupS hc calls))
        have hf' : f = ⟨1 + j⟩ := Option.some.inj (hl.symm.trans
          (lookup_mapIdx_name (·.name) 1 c.exports j j.isLt hc.names))
        have hS₁ : SeqCalls prof (refHost P) (readyCfg y.1 instAfterStart
            ([startFn a] ++ liftedFuncs P (fun k => I.addrs.getD k 0) c) (startGarb P a)) 0
            (callArgsP c 1 calls) p.1 mₙ := by
          rw [← zip_callArgsP, ← hfs']
          exact hS
        obtain ⟨cs', ι', G', wss, hseq, hrss, hmₙ, R'⟩ := seq_invP (c := c.noStart) hc₀ hf ha hI₀
          [startFn a] calls y.1 instAfterStart (startGarb P a) 0 _ _
          (ready_afterStart a hw) ht hS₁
        have hb' : p.2 ∈ callBehaviours prof (refHost P)
            (readyCfg cs' ι' ([startFn a] ++ liftedFuncs P (fun k => I.addrs.getD k 0) c.noStart) G')
            ⟨0 + calls.length⟩ ⟨[startFn (P := P) a].length + j⟩ (vs.map toRefVal) := by
          rw [← hmₙ, Nat.zero_add, ← List.length_map (f := fun q =>
            (c.exports[q.1].name, q.2.map toRefVal))]
          exact hf' ▸ hb
        exact .inl ⟨I, some a, _, wss, _, hF.isInst, hstart, hw, hseq, hrss,
          last_callP (c := c.noStart) hc₀ hf ha hI₀ [startFn a] R' j hvs hb'⟩
      · cases he
      · cases he
    · rcases instBehaviours_start hF prof _ hr with ⟨_, _, _, he⟩ | ⟨y, hy, hst, -⟩ | he
      · cases he
      · exact .inr (.inl ⟨hpe, start_fails hF hy hst⟩)
      · cases he
    · exact .inr (.inr hpe)

end Silmaril.Proofs.Wasm.Component.Reference
