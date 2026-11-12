module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.ExnCopy

/-!
# Round 5: the exception rules from bounded type typing

`throw`, `try_table` and `throw_ref` caught by `catch`/`catch_ref` or passing a non-matching
clause, forward, for the concrete `B`, from `HelpersC` (proved, `helpersC_builtins`) and, for
`throw` and `try_table`, `TypesB` and the bounds of `Round4.Bounded`: the thrown tag's type
(`StoreBnd.tags`) and the frame's module (`ModuleBnd`). The statements match the fields of
`Obl`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded tyBnd ModuleBnd)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- `HelpersC` for the concrete `B`. -/
theorem helpersC_builtins (hn : H → String) (host : HostSemantics H) :
    HelpersC (simEnv (BI P hn host)) hn :=
  have Pd := Prims.projDefs_simEnv (BI P hn host)
  have S := State.stateDefs_simEnv (BI P hn host)
  ⟨Prims.applies_exninst Pd hn, Prims.applies_tagaddr Pd hn, Prims.applies_tag Pd S hn,
    Prims.applies_asDeftype _, Prims.applies_addExn Pd S hn⟩

/-- The tag instance `Store.tag?` finds is one of the store's. -/
theorem mem_tags_of_tag? {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (h : s.tag? f x = some (ta, ti)) : ti ∈ s.tags := by
  unfold Store.tag? at h
  cases ht : f.module.tags[x.toNat]? with
  | none => simp [ht] at h
  | some a =>
    cases hs : s.tags[a]? with
    | none => simp [ht, hs] at h
    | some t =>
      simp only [ht, hs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact List.mem_of_getElem? hs

/-- `throw`, from a bounded store. -/
theorem fwd_throw5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H} {f : Frame} {x : TagIdx}
    {vs : List Val} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)}
    (htag : s.tag? f x = some (ta, ti)) (hex : Expand ti.type (.func ts .nil))
    (hlen : vs.length = ts.length) (hs : Round4.StoreBnd s) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
      ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩ := by
  intro hc _
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing (simEnv (BI P hn host)) := Typing.exnTyping_simEnv' _
  have hd : tyBnd ti.type = true := hs.tags ti (mem_tags_of_tag? htag)
  have hts : tyBnd ts = true := (tyBnd_func (tyBnd_of_expand hd hex)).1
  have hE : ∃ tvs : List Value, tvs.length = ts.length ∧
      TypedV (simEnv (BI P hn host)) Exn.valtypesT (.list tvs) ∧
      DDerives (simEnv (BI P hn host)) (otherwise (simEnv (BI P hn host))) "Expand" "%~~%" []
        (.tuple [CT.defType ti.type, Exn.funcTypeV tvs []]) :=
    ⟨ts.toList.map tyV, List.length_map _, TB.valtypes ts hts, by
      rw [Prims.exnFuncTypeV_eq]
      exact dderives_expandB TB _ hd hex⟩
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨hvs, -⟩ := Exn.typed_vals_append _ T his
  have h := sstep_throwC (helpersC_builtins hn host) (hasStepRules_simEnv _).throw htag hex hlen
    hz (X.n _) hvs (X.idx x) (X.exninst ⟨ta, vs⟩ hvs) (X.addr _) hE
  show SStep (simEnv (BI P hn host)) (cfgV _ (adminsToV (vals vs ++ [.plain (.throw x)]))) _
  rw [adminsToV_append, adminsToV_vals]
  exact h

/-- `try_table`, from a bounded frame module. -/
theorem fwd_tryTable5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {bt : BlockType} {cs : List Catch} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) (hM : ModuleBnd f.module) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
      ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing (simEnv (BI P hn host)) := Typing.exnTyping_simEnv' _
  refine Exn.fwd_of_read T (hasStepRules_simEnv _).read fun hz his his' => ?_
  obtain ⟨hvs, -⟩ := Exn.typed_vals_append _ T his
  obtain ⟨hn₀, hcs, hb⟩ := T.handler _ cs _ his'
  obtain ⟨-, -, hl⟩ := T.label _ [] _ hb
  obtain ⟨-, hbody⟩ := Exn.typed_vals_append _ T hl
  rw [adminsToV_expression] at hbody
  have h := sread_tryTableC (helpersC_builtins hn host) (Exn.hasReadRules_simEnv _).tryTable hbt
    hm hz (X.m _) hvs (X.blocktype bt) hcs hbody hn₀ (blocktypeB TB s f hM bt t₁ t₂ hbt)
  rw [adminsToV_append, adminsToV_vals]
  simpa [adminsToV, adminToV, instrsToV, adminsToV_append, adminsToV_vals,
    adminsToV_expression] using h

/-- `throw_ref` caught by `catch`. -/
theorem fwd_throwRefHandlerCatch5 {s : Store H} {f : Frame} {n : Nat} {x : TagIdx}
    {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
    (ht : f.module.tags[x.toNat]? = some e.tag) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing (simEnv (BI P hn host)) := Typing.exnTyping_simEnv' _
  exact Exn.fwd_of_read T (hasStepRules_simEnv _).read fun hz his his' =>
    sread_throwRefHandlerCatchC (helpersC_builtins hn host)
      (Exn.hasReadRules_simEnv _).throwRefHandlerCatch he ht hz
      (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
      (Exn.typed_vals_append _ T his').1

/-- `throw_ref` caught by `catch_ref`. -/
theorem fwd_throwRefHandlerCatchRef5 {s : Store H} {f : Frame} {n : Nat} {x : TagIdx}
    {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
    (ht : f.module.tags[x.toNat]? = some e.tag) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing (simEnv (BI P hn host)) := Typing.exnTyping_simEnv' _
  exact Exn.fwd_of_read T (hasStepRules_simEnv _).read fun hz his his' =>
    sread_throwRefHandlerCatchRefC (helpersC_builtins hn host)
      (Exn.hasReadRules_simEnv _).throwRefHandlerCatchRef he ht hz
      (T.handler n _ _ his).1 (X.idx x) (X.labelidx l)
      (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
      (Exn.typed_vals_append _ T his').1

/-- `throw_ref` past a non-matching catch clause. -/
theorem fwd_throwRefHandlerNext5 {s : Store H} {f : Frame} {n : Nat} {c : Catch}
    {cs : List Catch} {a : Nat} (hnm : ¬ CatchMatches s f a c) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩
      ⟨s, f, [.handler n cs (throwing a)]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have X : Exn.Typing (simEnv (BI P hn host)) := Typing.exnTyping_simEnv' _
  exact Exn.fwd_of_read T (hasStepRules_simEnv _).read fun hz his _ =>
    sread_throwRefHandlerNextC (Exn.hasReadRules_simEnv _) (helpersC_builtins hn host)
      (Exn.hasReadRules_simEnv _).throwRefHandlerNext hnm hz (T.handler n _ _ his).1
      (X.catch_ c cs (T.handler n _ _ his).2.1).1 (X.catch_ c cs (T.handler n _ _ his).2.1).2
      (X.addr a)

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
