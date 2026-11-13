module

public import Silmaril.Proofs.Wasm.Component.Reference.StartSeq
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# The IR side with a start function, and soundness

* `sem_roundsS`: rounds of the instance played from a store the start phase returns at are
  rounds of `modSemS P`; `trap_mem`: when the start phase may fail, `modSemS P` contains the
  strategy trapping on every question;
* `seqSpecToIRS`: a chain of returned calls of the specification from such a store, followed by a
  terminating outcome of the last call, is a play of `c.toComp.den (modSemS P)`;
* `trap_den`: when the start phase may fail, the IR traps on every export call;
* `simple_sound_seq_start`, `simple_sound_start`: soundness of the IR over `modSemS P` against the
  reference machine for simple components whose module may have a start function.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ## The core semantics -/

/-- **`modSemS` on rounds of the instance from a store the start phase returns at.** -/
theorem sem_roundsS {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} {st : Option Nat}
    {s₀ : Store Nat} (hI : m.IsInstS I st)
    (h₀ : Silmaril.Wasm.Game.StartsTo P Det.noHost I.store st s₀)
    {lc : List (Round (CoreIface.sig (CoreModule.exports m)))} {li : List (Round I.F)}
    (H : HRounds (exportH (instNum hI.noStart)) lc li) (h : twos li ∈ I.strategy P s₀) :
    twos lc ∈ (modSemS P).sem m := by
  show twos lc ∈ sSup (startStrategies P m)
  rw [Strategy.mem_sSup]
  exact .inr ⟨_, .inl ⟨I, st, s₀, hI, h₀, rfl⟩, twos_comp_upper (twos_comp_ofHandler H h)⟩

/-- **`modSemS` traps on every question when the start phase may fail** (or there is no
instance). -/
theorem trap_mem {m : NumModule}
    (hfail : (¬ ∃ I st, m.IsInstS I st) ∨ m.StartFails P)
    (q : (CoreIface.sig (CoreModule.exports m)).Op) :
    twos (E := CoreIface.sig (CoreModule.imports m)) [⟨q, none⟩] ∈ (modSemS P).sem m := by
  show twos [⟨q, none⟩] ∈ sSup (startStrategies P m)
  rw [Strategy.mem_sSup]
  refine .inr ⟨trapAll _ _, .inr ⟨rfl, hfail⟩, ?_⟩
  have hr : (Handler.toReduction (fun _ => (.pure none : Prog (CoreIface.sig (CoreModule.imports m))
      (Option Payload)) : Handler (CoreIface.sig (CoreModule.imports m))
        (CoreIface.sig (CoreModule.exports m)))).toLTS.Run .idle (twos [⟨q, none⟩]) .idle :=
    .vis (.ask q) (.vis (.ret (show _ = Prog.pure none from rfl)) (.nil _))
  exact Strategy.mem_ofHandler.mpr ⟨_, hr⟩

/-! ## The layers -/

theorem seqRounds_noStart (c : Simple) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)),
      seqRounds c.noStart calls wss = seqRounds c calls wss
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, ws :: wss => by
    show _ :: seqRounds c.noStart cs wss = _ :: seqRounds c cs wss
    rw [seqRounds_noStart c cs wss]
    rfl

/-- The IR rounds of a sequence and of further rounds `U`, over `modSemS P`. -/
theorem seq_denS {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {st : Option Nat}
    {s₀ : Store Nat} (hI : c.mod.IsInstS I st)
    (h₀ : Silmaril.Wasm.Game.StartsTo P Det.noHost I.store st s₀)
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} {s : Store Nat}
    {U : List (Round (sigN c.toComp.exports.length))} {li₀ li : List (Round I.F)}
    {lc₀ lc : List (Round (CoreIface.sig (CoreModule.exports c.mod)))}
    (hact : I.Activation P s₀ (twos li₀) s) (hli : twos li ∈ I.strategy P s)
    (H₀ : HRounds (exportH (instNum hI.noStart)) lc₀ li₀)
    (H : HRounds (exportH (instNum hI.noStart)) lc li)
    (X₀ : HRounds (exportsH c.mod.exports.length c.toComp.exports)
      ((seqRounds c calls wss).map Round.forget) (lc₀.map Round.forget))
    (X : HRounds (exportsH c.mod.exports.length c.toComp.exports)
      (U.map Round.forget) (lc.map Round.forget)) :
    twos (seqRounds c calls wss ++ U) ∈ c.toComp.den (modSemS P) := by
  have hinst : twos (li₀ ++ li) ∈ I.strategy P s₀ := by
    rw [twos_append]
    exact Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact hli
  have hsem : twos (lc₀ ++ lc) ∈ (modSemS P).sem c.mod := sem_roundsS hI h₀ (H₀.append H) hinst
  have henv : twos (lc₀.map Round.forget ++ lc.map Round.forget) ∈ envS (modSemS P) c :=
    List.map_append ▸ envS_rounds (modSemS P) c hsem
  refine den_rounds (modSemS P) c.toComp ?_
  rw [denU_toComp, List.map_append]
  exact twos_comp_ofHandler (X₀.append X) henv

/-- The observation of the last call, from the rounds, over `modSemS P`. -/
theorem seq_obsS {c : Simple}
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)}
    {wss : List (List Silmaril.Wasm.Component.Val)} (hlen : calls.length = wss.length)
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} :
    ∀ (b : Outcome) (A : Option Payload), ObsAns b A →
      twos (seqRounds c calls wss ++ [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), A⟩]) ∈
        c.toComp.den (modSemS P) →
      SeqIRObs c (c.toComp.den (modSemS P)) calls wss j vs b
  | .returns (some _), _, ⟨ws, hrs, hAw⟩, hden => ⟨ws, hrs, by
      rw [seqMoves_eq, seqRounds_append c j vs ws calls wss hlen]
      exact hAw ▸ hden⟩
  | .traps, _, hAn, hden => by
      show seqMoves c calls wss ++ twos [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), none⟩] ∈ _
      rw [seqMoves_eq, ← twos_append]
      exact hAn ▸ hden
  | .returns none, _, _, _ => trivial
  | .deadlocks, _, _, _ => trivial
  | .diverges, _, _, _ => trivial

/-- **The IR side with a start function**: returned calls of the specification from a store the
start phase returns at, and a terminating outcome of the last call, are a play of
`c.toComp.den (modSemS P)`; the returned calls alone are one too. -/
theorem seqSpecToIRS {c : Simple} (hc : c.Good) {I : Silmaril.Wasm.Game.ScalarInstance}
    {st : Option Nat} {s₀ : Store Nat} (hI : c.mod.IsInstS I st)
    (h₀ : Silmaril.Wasm.Game.StartsTo P Det.noHost I.store st s₀) (hw : I.WellFormed s₀)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (s : Store Nat) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (b : Outcome)
    (hseq : SeqSpec P c.noStart I s₀ (specCalls c calls) wss s)
    (hb : b ∈ specAt P c I c.exports[j] vs s) :
    seqMoves c calls wss ∈ c.toComp.den (modSemS P) ∧
      SeqIRObs c (c.toComp.den (modSemS P)) calls wss j vs b := by
  have hc₀ : c.noStart.Good := ⟨hc.names, hc.core⟩
  have hI₀ : c.noStart.mod.IsInst I := hI.noStart
  obtain ⟨hw', hlen, li₀, lc₀, hact, H₀, X₀⟩ :=
    seq_rounds (c := c.noStart) hc₀ hI₀ calls wss s₀ s hw hseq
  rw [seqRounds_noStart] at X₀
  refine ⟨?_, ?_⟩
  · have h : twos (seqRounds c calls wss ++ []) ∈ c.toComp.den (modSemS P) :=
      seq_denS (U := []) (li := []) (lc := []) hI h₀ hact (I.strategy P s).nil_mem H₀ .nil X₀ .nil
    rw [List.append_nil] at h
    rw [seqMoves_eq]
    exact h
  · rcases last_rounds (c := c.noStart) hc₀ hI₀ hw' hb with hd | ⟨A, li, lc, hA, hli, H, X⟩
    · subst hd
      trivial
    · exact seq_obsS hlen b A hA (seq_denS (U := [_]) hI h₀ hact hli H₀ H X₀ X)

/-- **When the start phase may fail, the IR traps on every export call.** -/
theorem trap_den {c : Simple} (hc : c.Good) (hfail : c.mod.StartFails P)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) :
    [.inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)),
      .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) none)] ∈
      c.toComp.den (modSemS P) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  have h : twos [(⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), none⟩ :
      Round (sigN c.toComp.exports.length))] ∈ c.toComp.den (modSemS P) := by
    refine den_rounds (modSemS P) c.toComp ?_
    rw [denU_toComp]
    cases hl : checkLower c.exports[j].ty.params vs with
    | none =>
      have henv : twos (([] : List (Round (CoreIface.sig (CoreModule.exports c.mod)))).map
          Round.forget) ∈ envS (modSemS P) c :=
        envS_rounds (modSemS P) c ((modSemS P).sem c.mod).nil_mem
      exact twos_comp_ofHandler (exportsH_trap c j.isLt vs hk hl) henv
    | some xs =>
      have henv := envS_rounds (modSemS P) c (trap_mem (.inr hfail) (⟨c.exports[j].core, hk⟩, .flat xs))
      exact twos_comp_ofHandler (exportsH_call c j.isLt vs hk hl none none rfl) henv
  exact h

/-! ## Soundness -/

/-- **`modSemS` extends `modSem`** on modules with an instance (no start function). -/
theorem modSem_le_modSemS {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : (modSem P).sem m ≤ (modSemS P).sem m := by
  rw [modSem_sem hI]
  refine le_sSup (.inl ⟨I, none, I.store, ⟨hI.1.elim fun mt h => ⟨mt,
    Silmaril.Wasm.Game.isInstanceStart_none_iff.2 h⟩, hI.2⟩,
    Silmaril.Wasm.Game.startsTo_none.2 rfl, rfl⟩)

theorem seqMoves_nil (c : Simple) :
    ∀ calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val),
      seqMoves c calls [] = []
  | [] => rfl
  | _ :: _ => rfl

/-- **Soundness of the IR for sequences of calls, with a start function** (every profile, every
component choice profile). -/
theorem simple_sound_seq_start (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.InstS) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSemS P) ∧
      SeqIRObs c (c.toComp.den (modSemS P)) calls wss j vs p.2 := by
  rcases seq_refToSpecS P prof c hc hf hi ha calls j vs ht hvs p hp with
    ⟨I, st, s₀, wss, s, hI, h₀, hw, hseq, h1, h2⟩ | ⟨rfl, hfail⟩ | rfl
  · exact ⟨wss, h1, seqSpecToIRS hc hI h₀ hw calls wss s j vs p.2 hseq h2⟩
  · refine ⟨[], rfl, by rw [seqMoves_nil]; exact (c.toComp.den (modSemS P)).nil_mem, ?_⟩
    show seqMoves c calls [] ++ _ ∈ _
    rw [seqMoves_nil, List.nil_append]
    exact trap_den hc hfail j vs
  · exact ⟨[], rfl, by rw [seqMoves_nil]; exact (c.toComp.den (modSemS P)).nil_mem, trivial⟩

/-- A behaviour of an export call is a behaviour of the sequence without earlier calls. -/
theorem seqBehaviours_of_export {prof : Silmaril.Wasm.Component.ProfileKind} {c : Simple}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {b : Outcome}
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    (([] : List (List Silmaril.Wasm.Component.Value.Val)), b) ∈ seqBehaviours prof
      (refHost P) () c.toRef
      (([] : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)).map fun q =>
        (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name (vs.map toRefVal) := by
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩
  · exact .inl ⟨m₁, inst, es, [], m₁, f, hr, rfl, .nil _ _, hl, hb⟩
  · exact .inr (.inl ⟨rfl, hr⟩)
  · exact .inr (.inr ⟨rfl, hr⟩)

/-- The observation of a sequence without earlier calls is that of a single call. -/
theorem irObs_of_seqIRObs {c : Simple}
    {σ : Strategy (sigN 0) (sigN c.toComp.exports.length)} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} :
    ∀ b : Outcome, SeqIRObs c σ [] [] j vs b → IRObs σ ⟨j, by simp [Simple.toComp]⟩ vs b
  | .returns (some _), h => h
  | .returns none, _ => trivial
  | .traps, h => h
  | .deadlocks, _ => trivial
  | .diverges, _ => trivial

/-- **Soundness of the IR with a start function** (every profile, every component choice
profile): every behaviour of calling export `j` of `c.toRef` on the reference images of
well-typed IR values is matched by the IR denotation over `modSemS P`. -/
theorem simple_sound_start (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.InstS) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal),
      IRObs (c.toComp.den (modSemS P)) ⟨j, by simp [Simple.toComp]⟩ vs b := by
  intro b hb
  obtain ⟨wss, h1, -, hobs⟩ := simple_sound_seq_start P prof c hc hf hi ha [] j vs
    (fun _ h => nomatch h) hvs _ (seqBehaviours_of_export hb)
  have hw : wss = [] := List.map_eq_nil_iff.1 h1.symm
  exact irObs_of_seqIRObs b (hw ▸ hobs)

end Silmaril.Proofs.Wasm.Component.Reference
