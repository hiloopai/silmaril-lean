module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Otherwise

/-!
# Family X, forward: the `Forward` fields

Each theorem's type is the corresponding field of `Forward (simEnv B) hn P host`. The
hypotheses are the encoding's `TypingFacts`, the family's `Typing` and, for the rules that call
store helpers, `Helpers`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

variable {H : Type} {hn : H → String} (B : Builtins)

/-- The image of `vals vs ++ rest`, typed as `instr*`, gives `vs` typed as `val*` and `rest`
typed as `instr*`. -/
theorem typed_vals_append (T : TypingFacts (simEnv B) hn) {vs : List Val} {rest : List Admin}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs ++ rest)))) :
    TypedV (simEnv B) valsT (.list (vs.map valV)) ∧
      TypedV (simEnv B) instrsT (.list (adminsToV rest)) := by
  rw [adminsToV_append] at h
  obtain ⟨hv, hr⟩ := (T.append _ _).1 h
  have := T.vals vs hv
  rw [adminsToV_vals] at this
  exact ⟨this, hr⟩

/-- `Step.throwRefNull`, forward. -/
theorem fwd_throwRefNull (T : TypingFacts (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame},
      FwdP (simEnv B) hn ⟨s, f, [.ref .null, .plain .throwRef]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_read T (hasStepRules_simEnv B).read fun hz _ _ =>
    sread_throwRefNull (hasReadRules_simEnv B).throwRefNull hz

/-- `Step.throwRefLabel`, forward. -/
theorem fwd_throwRefLabel (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat},
      FwdP (simEnv B) hn ⟨s, f, [.label n cont (throwing a)]⟩ ⟨s, f, throwing a⟩ :=
  fun {_ _ n cont a} => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefLabel (hasReadRules_simEnv B).throwRefLabel hz
      (T.label n cont _ his).1 (T.label n cont _ his).2.1 (X.addr a)

/-- `Step.throwRefFrame`, forward. -/
theorem fwd_throwRefFrame (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f fi : Frame} {n : Nat} {a : Nat},
      FwdP (simEnv B) hn ⟨s, f, [.frame n fi (throwing a)]⟩ ⟨s, f, throwing a⟩ :=
  fun {_ _ fi n a} => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefFrame (hasReadRules_simEnv B).throwRefFrame hz
      (T.frame n fi _ his).1 (T.frame n fi _ his).2.1 (X.addr a)

/-- `Step.throwRefHandlerEmpty`, forward. -/
theorem fwd_throwRefHandlerEmpty (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {a : Nat},
      FwdP (simEnv B) hn ⟨s, f, [.handler n [] (throwing a)]⟩ ⟨s, f, throwing a⟩ :=
  fun {_ _ n a} => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefHandlerEmpty (hasReadRules_simEnv B).throwRefHandlerEmpty hz
      (T.handler n [] _ his).1 (X.addr a)

/-- `Step.throwRefHandlerCatchAll`, forward. -/
theorem fwd_throwRefHandlerCatchAll (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat},
      FwdP (simEnv B) hn ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩
        ⟨s, f, [.plain (.br l)]⟩ :=
  fun {_ _ n l cs a} => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefHandlerCatchAll (hasReadRules_simEnv B).throwRefHandlerCatchAll hz
      (T.handler n _ _ his).1 (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2
      (X.addr a)

/-- `Step.throwRefHandlerCatchAllRef`, forward. -/
theorem fwd_throwRefHandlerCatchAllRef (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat},
      FwdP (simEnv B) hn ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
        ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩ :=
  fun {_ _ n l cs a} => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefHandlerCatchAllRef (hasReadRules_simEnv B).throwRefHandlerCatchAllRef hz
      (T.handler n _ _ his).1 (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2
      (X.addr a)

/-- `Step.throwRefHandlerCatch`, forward. -/
theorem fwd_throwRefHandlerCatch (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B))
    (Hp : Helpers (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat}
      {e : ExnInst} (_ : s.exns[a]? = some e) (_ : f.module.tags[x.toNat]? = some e.tag),
      FwdP (simEnv B) hn ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩ :=
  fun {_ _ n x l cs a _} he ht => fwd_of_read T (hasStepRules_simEnv B).read fun hz his his' =>
    sread_throwRefHandlerCatch Hp (hasReadRules_simEnv B).throwRefHandlerCatch he ht hz
      (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
      (typed_vals_append B T his').1

/-- `Step.throwRefHandlerCatchRef`, forward. -/
theorem fwd_throwRefHandlerCatchRef (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B))
    (Hp : Helpers (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat}
      {e : ExnInst} (_ : s.exns[a]? = some e) (_ : f.module.tags[x.toNat]? = some e.tag),
      FwdP (simEnv B) hn ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩ :=
  fun {_ _ n x l cs a _} he ht => fwd_of_read T (hasStepRules_simEnv B).read fun hz his his' =>
    sread_throwRefHandlerCatchRef Hp (hasReadRules_simEnv B).throwRefHandlerCatchRef he ht hz
      (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
      (typed_vals_append B T his').1

/-- `Step.throwRefInstrs`, forward. -/
theorem fwd_throwRefInstrs (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B)) :
    ∀ {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (_ : vs ≠ [] ∨ rest ≠ []),
      FwdP (simEnv B) hn ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩ := by
  intro s f vs a rest hne
  refine fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ => ?_
  rw [List.append_assoc] at his
  obtain ⟨hvs, htr⟩ := typed_vals_append B T his
  rw [adminsToV_append] at htr
  obtain ⟨-, hrest⟩ := (T.append _ _).1 htr
  have hne' : vs.map valV ≠ [] ∨ adminsToV rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (by simpa using h)
    · exact .inr (adminsToV_ne_nil h)
  have h := sread_throwRefInstrs (hasReadRules_simEnv B).throwRefInstrs hz hvs (X.addr a) hrest hne'
  rwa [adminsToV_append, adminsToV_append, adminsToV_vals]

/-- `Step.handlerVals`, forward. -/
theorem fwd_handlerVals (T : TypingFacts (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val},
      FwdP (simEnv B) hn ⟨s, f, [.handler n cs (vals vs)]⟩ ⟨s, f, vals vs⟩ := by
  intro s f n cs vs
  refine fwd_of_pure T (hasStepRules_simEnv B).pure fun his _ => ?_
  obtain ⟨hn₀, hcs, hb⟩ := T.handler n cs _ his
  have hvs := T.vals vs hb
  rw [adminsToV_vals] at hvs
  have h := spure_handlerVals (hasPureRules_simEnv B).handlerVals hn₀ hcs hvs
  rw [adminsToV_vals]
  simpa only [adminsToV, adminToV, adminsToV_vals] using h

/-- `Step.tryTable`, forward. -/
theorem fwd_tryTable (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B))
    (Hp : Helpers (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
      (_ : vs.length = t₁.length),
      FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
        ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩ := by
  intro s f bt cs body vs t₁ t₂ hbt hm
  refine fwd_of_read T (hasStepRules_simEnv B).read fun hz his his' => ?_
  obtain ⟨hvs, -⟩ := typed_vals_append B T his
  obtain ⟨hn₀, hcs, hb⟩ := T.handler _ cs _ his'
  obtain ⟨-, -, hl⟩ := T.label _ [] _ hb
  obtain ⟨-, hbody⟩ := typed_vals_append B T hl
  rw [adminsToV_expression] at hbody
  have h := sread_tryTable Hp (hasReadRules_simEnv B).tryTable hbt hm hz (X.m _) hvs
    (X.blocktype bt) hcs hbody hn₀
  rw [adminsToV_append, adminsToV_vals]
  simpa [adminsToV, adminToV, instrsToV, adminsToV_append, adminsToV_vals,
    adminsToV_expression] using h

/-- `Step.throw`, forward. -/
theorem fwd_throw (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B))
    (Hp : Helpers (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} (_ : s.tag? f x = some (ta, ti))
      (_ : Expand ti.type (.func ts .nil)) (_ : vs.length = ts.length),
      FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
        ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩ := by
  intro s f x vs ta ti ts htag hex hlen hc _
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨hvs, -⟩ := typed_vals_append B T his
  have h := sstep_throw Hp (hasStepRules_simEnv B).throw htag hex hlen hz (X.n _) hvs (X.idx x)
    (X.exninst ⟨ta, vs⟩ hvs) (X.addr _)
  show SStep (simEnv B) (cfgV _ (adminsToV (vals vs ++ [.plain (.throw x)]))) _
  rw [adminsToV_append, adminsToV_vals]
  exact h

/-- `Step.throwRefHandlerNext`, forward. The rule's `otherwise` premise is discharged by
`otherwiseAt_handlerNext`. -/
theorem fwd_throwRefHandlerNext (T : TypingFacts (simEnv B) hn) (X : Typing (simEnv B))
    (Hp : Helpers (simEnv B) hn) :
    ∀ {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (_ : ¬ CatchMatches s f a c),
      FwdP (simEnv B) hn ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩
        ⟨s, f, [.handler n cs (throwing a)]⟩ :=
  fun {_ _ n c cs a} hnm => fwd_of_read T (hasStepRules_simEnv B).read fun hz his _ =>
    sread_throwRefHandlerNext (hasReadRules_simEnv B) Hp
      (hasReadRules_simEnv B).throwRefHandlerNext hnm hz (T.handler n _ _ his).1
      (X.catch_ c cs (T.handler n _ _ his).2.1).1 (X.catch_ c cs (T.handler n _ _ his).2.1).2
      (X.addr a)

end Silmaril.Wasm.SpecTec.Sim.Exn
