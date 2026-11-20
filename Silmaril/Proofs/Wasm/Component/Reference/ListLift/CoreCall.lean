module

public import Silmaril.Proofs.Wasm.Component.Reference.CallRun
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs

/-!
# Typed core calls of a well-formed instance from any store

The core activations of a list call (the allocator's, then the lifted export's) start from the
reference engine's core store `cs` *after* earlier allocator runs and memory writes, not from
the instance store. By type soundness at every well-formed store (`ScalarInstance.answer_of_run`,
`progress_hostOf`, `wellFormed_after_run`), a run of function export `k` of an import-free
instance `I` whose renamed store `Store.mapH (fun _ => 0) cs` is well formed, on flat arguments
of the export's parameter types:

* never reaches a host call (`core_no_callout`);
* when it returns, is a Core run of the renamed store returning values of the export's result
  types, into a store that is again well formed (`core_returned`).

`WellFormed` survives memory writes (`wellFormed_memWrite?`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store Steps invoke vals)

variable {P : Profile} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {k : Nat} {xs : List Flat}

/-- The export question `k` on the flat arguments `xs` of its parameter types. -/
def typedOp (I : Silmaril.Wasm.Game.ScalarInstance) (k : Nat) (hk : k < I.exports.length)
    (xs : List Flat)
    (hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params) :
    I.F.Op :=
  ⟨⟨k, hk⟩, ⟨xs.map Silmaril.Wasm.SingleThreaded.ofFlat, by
    have h := forall₂_hasVal_ofFlat xs
    rw [hxs] at h
    exact h⟩⟩

/-- Its invocation. -/
theorem typedOp_invoke (hk : k < I.exports.length)
    (hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params)
    (s : Store Nat) :
    invoke s (I.addr (typedOp I k hk xs hxs).1) (typedOp I k hk xs hxs).2.1 =
      invoke s (I.addrs.getD k 0) (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) := rfl

/-- **No callout** from a typed core call at a well-formed store. -/
theorem core_no_callout (hI : I.imports = []) (hw : I.WellFormed (Store.mapH (fun _ => 0) cs))
    (hk : k < I.exports.length)
    (hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params)
    (y : CoreSt (E3 P))
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD k 0) xs) y)
    (h : CanonHost (E3 P)) (args : List FlatValue) :
    (E3 P).status y.1 y.2 ≠ .callout h args := by
  intro hs
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => (0 : Nat)) hd
  have run := coreSteps_run hy
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke (Store.mapH (fun _ => 0) cs) (I.addr (typedOp I k hk xs hxs).1)
        (typedOp I k hk xs hxs).2.1) (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)) := by
    rw [hostOf_nil hI, typedOp_invoke]
    exact run
  have hn : Silmaril.Wasm.SingleThreaded.decompose?
      (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store
      (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).code = none := by
    rcases Silmaril.Wasm.Game.ScalarInstance.progress_hostOf hw (throwsBelow_silent I _) run'
      with ⟨r, hr⟩ | ⟨c'', hs'⟩
    · rw [hr]
      exact Silmaril.Wasm.Binaryen.LinkBehaviours.decompose?_result r
    · rw [hostOf_nil hI] at hs'
      exact Silmaril.Wasm.SingleThreaded.decompose?_none_of_noRedex
        (Silmaril.Wasm.SingleThreaded.Step.noRedex hs')
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

/-- `toFlat?` inverts `ofFlat`. -/
theorem eq_map_ofFlat : ∀ {cvs : List Silmaril.Wasm.Execution.Core.Val} {vs : List Flat},
    cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some vs →
      cvs = vs.map Silmaril.Wasm.SingleThreaded.ofFlat
  | [], vs, h => by
    cases (Option.some.inj h).symm
    rfl
  | c :: cvs, vs, h => by
    cases c with
    | num v =>
      cases hm : cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | none => simp [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?, hm] at h
      | some ws =>
        simp only [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?, hm, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rw [eq_map_ofFlat hm]
        rfl
    | _ => simp [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?] at h

/-- **A returned typed core call** at a well-formed store is a Core run of the renamed store,
returning values of the export's result types into a well-formed store. -/
theorem core_returned (hI : I.imports = []) (hw : I.WellFormed (Store.mapH (fun _ => 0) cs))
    (hk : k < I.exports.length)
    (hxs : xs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params)
    (y : CoreSt (E3 P))
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD k 0) xs) y)
    {vs : List FlatValue} (hs : (E3 P).status y.1 y.2 = .returned (.values vs)) :
    (∃ f', Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD k 0)
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))
      ⟨Store.mapH (fun _ => 0) y.1, f', vals (vs.map Silmaril.Wasm.SingleThreaded.ofFlat)⟩) ∧
    vs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].results ∧
    I.WellFormed (Store.mapH (fun _ => 0) y.1) := by
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have run := coreSteps_run hy
  have hcode : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).code = vals cvs := hc
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  have run' : Steps P (Silmaril.Wasm.Game.hostOf I.imports (Silmaril.Wasm.Game.Env.silent _))
      (invoke (Store.mapH (fun _ => 0) cs) (I.addr (typedOp I k hk xs hxs).1)
        (typedOp I k hk xs hxs).2.1) (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)) := by
    rw [hostOf_nil hI, typedOp_invoke]
    exact run
  obtain ⟨w, hw', -⟩ := Silmaril.Wasm.Game.ScalarInstance.answer_of_run hw
    (throwsBelow_silent I _) run' (r := .values cvs) hcode
  have hwf := (Silmaril.Wasm.Game.ScalarInstance.wellFormed_after_run hw
    (throwsBelow_silent I _) run' (r := .values cvs) hcode).1
  rw [hstore] at hwf
  have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
      (I.exports.get ⟨k, hk⟩).results cvs := by
    unfold Silmaril.Wasm.Game.Answer.ofResult? at hw'
    dsimp only at hw'
    split_ifs at hw' with ht
    exact ht
  have hty := toFlat?_types' (I.exports.get ⟨k, hk⟩).results cvs vs ht hm
  refine ⟨⟨(y.2.config y.1).frame, ?_⟩, hty, hwf⟩
  have e := eq_map_ofFlat hm
  subst e
  have hc' : Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1) =
      ⟨Store.mapH (fun _ => 0) y.1, (y.2.config y.1).frame,
        vals (vs.map Silmaril.Wasm.SingleThreaded.ofFlat)⟩ := by
    rw [← hstore, ← hcode]
    rfl
  rw [← hc']
  exact run
where
  /-- Typed values have flat views of their types. -/
  toFlat?_types' : ∀ (ts : List Silmaril.Wasm.Game.ScalarType)
      (cvs : List Silmaril.Wasm.Execution.Core.Val) (fvs : List Flat),
      List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal ts cvs →
      cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fvs →
      fvs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = ts
  | [], [], fvs, _, h => by
    cases (Option.some.inj h).symm
    rfl
  | t :: ts, c :: cvs, fvs, .cons ht hr, h => by
    cases c with
    | num v =>
      cases hm : cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | none => simp [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?, hm] at h
      | some ws =>
        simp only [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?, hm, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [List.map_cons, toFlat?_types' ts cvs ws hr hm, List.cons.injEq, and_true]
        cases t with
        | num t' =>
          obtain ⟨bits, hb⟩ := ht
          cases hb
          rfl
        | v128 =>
          obtain ⟨b, hb⟩ := ht
          cases hb
        | i31 n => rcases ht with ⟨b, hb⟩ | ⟨-, hb⟩ <;> cases hb
    | _ => simp [List.mapM_cons, Silmaril.Wasm.SingleThreaded.toFlat?] at h
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h

/-! ## Memory writes -/

/-- A byte write commutes with renaming the host. -/
theorem memWrite?_mapH {H H' : Type} (g : H → H') (s : Store H) (a st : Nat) (bs : ByteArray) :
    Silmaril.Wasm.SingleThreaded.memWrite? (Store.mapH g s) a st bs =
      (Silmaril.Wasm.SingleThreaded.memWrite? s a st bs).map (Store.mapH g) := by
  unfold Silmaril.Wasm.SingleThreaded.memWrite?
  show (do
      let mi ← s.mems[a]?
      let b ← Silmaril.Wasm.Execution.MemRep.writeBytes mi.bytes st bs
      return (Store.mapH g s).setMem a { mi with bytes := b }) = _
  cases s.mems[a]? with
  | none => rfl
  | some mi =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases Silmaril.Wasm.Execution.MemRep.writeBytes mi.bytes st bs with
    | none => rfl
    | some b => rfl

/-- A byte write keeps an instance well formed. -/
theorem wellFormed_memWrite? {I : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    {a st : Nat} {bs : ByteArray} (hw : I.WellFormed s)
    (h : Silmaril.Wasm.SingleThreaded.memWrite? s a st bs = some s') : I.WellFormed s' := by
  obtain ⟨hok, -, hf⟩ := Silmaril.Wasm.Component.Engine.Core3.Typed.memWrite?_storeOk hw.storeOk h
  refine ⟨hok, hw.addrs_length, fun j => ?_, fun a fi h' hfi hc => ?_⟩
  · rw [hf]
    exact hw.export_type j
  · rw [hf] at hfi
    exact hw.host_type a fi h' hfi hc

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
