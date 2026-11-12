module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq

/-!
# Sequences of calls over `core3R P V IR`: the sequence half

A copy of section `Sound` of `Silmaril.Proofs.Wasm.Component.Reference.MultiSeq` with `core3P P`
replaced by `core3R P V IR` (provenance: copy). The lemmas that build a call context take
`Sub P IR` (`seq_step`, `seq_inv`, `last_call`, `seq_refToSpec`); otherwise the proofs are
unchanged.

* `seq_refToSpec`: the statement of `Reference.seq_refToSpec` over `core3R P V IR`;
* `seqRefToSpec_core3R`, `seqRefToSpec_restrict_core3P`: `SeqRefToSpec` for `core3R P V IR`
  (with `Sub P IR`) and for every restriction of `core3P P`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy)

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

section Sound

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}


/-- One resolved call between calls. -/
theorem seq_step (hIR : Sub P IR) (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {ι : InstState} {G : Garb P V IR} {k : Nat}
    (R : ReadyAt I cs ι G k) (j : Fin c.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {m₁ : Machine.Config (E3 P V IR) Unit}
    {rs : List Val}
    (hcall : Calls prof (refHostR P V IR).hr (D P V IR)
      (readyCfg cs ι (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G) ⟨k⟩ ⟨j⟩
      (vs.map toRefVal) m₁ (.resolved (some rs))) :
    ∃ cs' ι' G' ws, rs = ws.map toRefVal ∧
      RetAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) ws (Store.mapH (fun _ => 0) cs') ∧
      m₁ = readyCfg cs' ι' (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G' ∧
      ReadyAt I cs' ι' G' (k + 1) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs, hIR⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have hF := calls_facts (prof := prof) C R hff hmax hres hmaxr hffr
    (liftedFuncs_get? c (fun k => I.addrs.getD k 0) j.isLt) hcall
  obtain ⟨cs', ws, rfl, hret, rfl⟩ := hF.2 rs rfl
  exact ⟨cs', _, _, ws, rfl, hret, rfl,
    ⟨hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _, fresh_next R.fresh _ _ _ _ _⟩⟩

/-- **Sequences of resolved calls between calls** are sequences of returned calls of the
specification. -/
theorem seq_inv (hIR : Sub P IR) (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ι : InstState) (G : Garb P V IR) (k : Nat)
      (rss : List (List Val)) (mₙ : Machine.Config (E3 P V IR) Unit),
      ReadyAt I cs ι G k → TypedCalls c calls →
      SeqCalls prof (refHostR P V IR) (readyCfg cs ι (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G) k
        (callArgs c calls) rss mₙ →
      ∃ cs' ι' G' wss, SeqSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) wss
          (Store.mapH (fun _ => 0) cs') ∧ rss = wss.map (·.map toRefVal) ∧
        mₙ = readyCfg cs' ι' (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G' ∧
        ReadyAt I cs' ι' G' (k + calls.length)
  | [], cs, ι, G, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨cs, ι, G, [], .nil _, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ι, G, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨cs₁, ι₁, G₁, ws, rfl, hret, rfl, R₁⟩ := seq_step hIR hc hf ha hI R j hvs hcall
      obtain ⟨cs', ι', G', wss, hseq, rfl, rfl, R'⟩ := seq_inv hIR hc hf ha hI calls cs₁ ι₁ G₁ (k + 1)
        _ _ R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS'
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      exact ⟨cs', ι', G', ws :: wss, .cons hret hseq, rfl, rfl, hk ▸ R'⟩

/-- The export map finds the calls. -/
theorem mapM_lookup (hc : c.Good) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)),
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).mapM
          (fun q => (exportMap c).lookup q.1) = some (calls.map fun q => (⟨q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    have hq : (exportMap c).lookup c.exports[q.1].name = some ⟨q.1⟩ :=
      exportMap_lookup hc q.1 q.1.isLt
    simp only [List.map_cons, List.mapM_cons, hq, mapM_lookup hc calls]
    rfl

theorem zip_callArgs (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    (calls.map fun q => (⟨q.1⟩ : FuncId)).zip
        ((calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
      callArgs c calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

/-- The configuration after instantiation is between calls, with nothing left over. -/
theorem ready_afterInst (hI : c.mod.IsInst I) {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))}
    (hcs : Store.mapH (fun _ => 0) cs = I.store) :
    ReadyAt I cs {} ⟨[], [], [], [], [], [], []⟩ 0 where
  wf := hcs ▸ hI.1.choose_spec.ok
  threads := .inl rfl
  fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) }

/-- The last call of a sequence. -/
theorem last_call (hIR : Sub P IR) (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {ι : InstState} {G : Garb P V IR} {n : Nat}
    (R : ReadyAt I cs ι G n) (j : Fin c.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ callBehaviours prof (refHostR P V IR)
      (readyCfg cs ι (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G) ⟨n⟩ ⟨j⟩ (vs.map toRefVal)) :
    b ∈ specAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs, hIR⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have hget := liftedFuncs_get? (P := P) (V := V) (IR := IR) c (fun k => I.addrs.getD k 0) j.isLt
  rcases hb with ⟨m', out, hcalls, hpo⟩ | ⟨hpo, hd⟩
  · exact hpo ▸ (calls_facts C R hff hmax hres hmaxr hffr hget hcalls).1
  · exact hpo ▸ diverges_facts C R hff hmax hres hmaxr hffr hget hd

/-- **The reference-machine half for sequences of calls** (every profile, every component
choice profile). -/
theorem seq_refToSpec (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (hIR : Sub P IR) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (refHostR P V IR) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (wss : List (List Silmaril.Wasm.Component.Val))
      (s : Silmaril.Wasm.Execution.Core.Store Nat), c.mod.IsInst I ∧
      SeqSpec P c I I.store (specCalls c calls) wss s ∧ p.1 = wss.map (·.map toRefVal) ∧
      p.2 ∈ specAt P c I c.exports[j] vs s := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P V IR prof c hc hi
  rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hS, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · show ∃ (I' : Silmaril.Wasm.Game.ScalarInstance) (wss : List (List Silmaril.Wasm.Component.Val))
      (s : Silmaril.Wasm.Execution.Core.Store Nat), c.mod.IsInst I' ∧
      SeqSpec P c I' I'.store (specCalls c calls) wss s ∧ p.1 = wss.map (·.map toRefVal) ∧
      p.2 ∈ specAt P c I' c.exports[j] vs s
    have he : m₀ = afterInst P V IR cs (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) ∧
        inst = ⟨0⟩ ∧ es = exportMap c := by
      simpa only [InstResult.instance.injEq] using hinst _ hr
    have hfs' : fs = calls.map fun q => (⟨q.1⟩ : FuncId) :=
      Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookup hc calls))
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMap_lookup hc j j.isLt))
    have hS₁ : SeqCalls prof (refHostR P V IR) (readyCfg cs {}
        (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) ⟨[], [], [], [], [], [], []⟩) 0
        (callArgs c calls) p.1 mₙ := by
      have hS₀ : SeqCalls prof (refHostR P V IR) (afterInst P V IR cs (liftedFuncs P V IR
          (fun k => I.addrs.getD k 0) c)) 0 (fs.zip ((calls.map fun q =>
            (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd)) p.1 mₙ := he.1 ▸ hS
      rw [← zip_callArgs, ← hfs']
      exact hS₀
    obtain ⟨cs', ι', G', wss, hseq, hrss, hmₙ, R'⟩ :=
      seq_inv hIR hc hf ha hI calls cs {} _ 0 _ _ (ready_afterInst hI hcs) ht hS₁
    have hb' : p.2 ∈ callBehaviours prof (refHostR P V IR)
        (readyCfg cs' ι' (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) G')
        ⟨0 + calls.length⟩ ⟨j⟩ (vs.map toRefVal) := by
      rw [← hmₙ, ← hf', Nat.zero_add, ← List.length_map (f := fun q =>
        (c.exports[q.1].name, q.2.map toRefVal))]
      exact hb
    exact ⟨I, wss, _, hI, hcs ▸ hseq, hrss, last_call hIR hc hf ha hI R' j hvs hb'⟩
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

/-! ## The IR side, stated (in the `Sound` header) -/

end Sound

/-- **The sequence half over `core3R P V IR`**, for an internal step contained in
`InternalP P`. -/
theorem seqRefToSpec_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (hIR : Sub P IR) :
    SeqRefToSpec (core3R P V IR) id P := by
  intro prof c hc hf hi ha calls j vs ht hvs p hp
  have hm : Silmaril.Wasm.Component.Syntax.Component.map (N := (core3R P V IR).Module) id
      c.toRef = c.toRef := Silmaril.Wasm.Component.Syntax.Component.map_id _
  erw [hm] at hp
  exact seq_refToSpec P V IR hIR prof c hc hf hi ha calls j vs ht hvs p hp

/-- **The sequence half for every restriction of the Core 3.0 engine.** -/
theorem seqRefToSpec_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    SeqRefToSpec (restrict (core3P P) r) id P :=
  seqRefToSpec_core3R P (fun m => (core3P P).Valid m ∧ r.Mod m)
    (fun c c' => (core3P P).Internal c c' ∧ r.Rt c') (sub_restrict P r)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
