module

public import Silmaril.Wasm.Logic.GameLink.Examples.Defs
public import Silmaril.Proofs.Wasm.Logic.GameLink.Link
public import Silmaril.Wasm.Logic.OpenExamples.Thms

/-!
# The logic and the Wasm game: a worked two-module example

* `incProvider_sat`: an instance all of whose exports are the increment
  function meets `incISpec` with the invariant "the function is in the store",
  under any import specification;
* `client_sat`: an instance all of whose exports are the client function, with
  import `0` of type `[i32] → …`, meets `incISpec` under the import
  specification `incISpec` (its stub call is proved with `Open.FSpecAt.stub`);
* `inc_link_sound`, `inc_link_answer`: for every static link (`Setup`) whose
  provider and consumer have these functions at their export addresses, the
  linked module's strategy refines `agStrat Ii (incISpec _)`, and every
  terminating host-free run of an export call of the linked module on `m`
  returns `m + 1`.

The proofs of the bodies follow `Silmaril.Proofs.Wasm.Logic.OpenExamples.Link`
(the provider's body is `OpenExamples.inc_body`). A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink.Examples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome agStrat)
open Silmaril.Wasm.Logic.OpenExamples (incBody clientBody incSpec inc_body)
open Silmaril.Wasm.Logic.HoareExamples (x0 forCall_local0)

variable {P : Profile}

/-! ## Consequence -/

/-- The call postcondition is monotone in the callee's postcondition. -/
theorem callPost_mono {f F : Frame} {vs₀ : List Val} {R R' : Store Nat → Outcome → Prop}
    (hR : ∀ s o, R s o → R' s o) {s : Store Nat} {o : Outcome} (h : callPost f vs₀ R s F o) :
    callPost f vs₀ R' s F o := by
  rcases h with ⟨hf, ⟨res, ho, hr⟩ | ⟨ho, hr⟩ | ⟨a, ho, hr⟩⟩
  · exact ⟨hf, .inl ⟨res, ho, hR _ _ hr⟩⟩
  · exact ⟨hf, .inr (.inl ⟨ho, hR _ _ hr⟩)⟩
  · exact ⟨hf, .inr (.inr ⟨a, ho, hR _ _ hr⟩)⟩

/-- **The rule of consequence** for function specifications. -/
theorem FSpecValid.conseq {host : HostSemantics Nat} {a : Nat} {S S' : FSpec Nat}
    (h : FSpecValid P host a S) (hpre : ∀ s args, S'.pre s args → S.pre s args)
    (hpost : ∀ s args s' o, S'.pre s args → S.post s args s' o → S'.post s args s' o) :
    FSpecValid P host a S' := fun n s args hp f vs₀ c hc =>
  Safe.post_mono (fun _ _ _ hq => callPost_mono (hpost s args · · hp) hq)
    (h n s args (hpre s args hp) f vs₀ c hc)

/-- An outcome `normal vs` comes from the result `values vs`. -/
theorem result_of_normal {r : Result} {vs : List Val} (h : resultOutcome r = .normal vs) :
    r = .values vs := by
  cases r with
  | values ws => cases h; rfl
  | throw a => cases h
  | trap => cases h

/-- A specification that returns `m + 1` on `[i32 m]` and keeps the store implies the
export specification of `incISpec`, for an invariant that it assumes. -/
theorem exportSpec_of_inc {I : ScalarInstance} {Inv : Store Nat → Prop}
    {host : HostSemantics Nat} {a : Nat} {S : FSpec Nat}
    (h : FSpecValid P host a S)
    (hpre : ∀ s (m : BitVec 32), Inv s → S.pre s [.i32 m])
    (hpost : ∀ s args s' o, S.post s args s' o →
      s' = s ∧ ∃ m : BitVec 32, args = [.i32 m] ∧ o = .normal [.i32 (m + 1)])
    (j : Fin I.exports.length) :
    FSpecValid P host a (exportSpec I Inv (incISpec I.exports) j) := by
  refine FSpecValid.conseq h (fun s args ⟨hs, _, m, hm⟩ => by
    have hm' : args = [.i32 m] := hm
    rw [hm']
    exact hpre s m hs) ?_
  rintro s args s' o ⟨hs, -⟩ hp
  obtain ⟨rfl, m, rfl, rfl⟩ := hpost s args s' o hp
  refine ⟨hs, fun _ v hv m' hm' => ?_⟩
  have hmm : m' = m := Hoare.i32_inj (List.cons.inj hm').1
  rw [hmm]
  exact result_of_normal hv

/-! ## The provider -/

section

variable {a₁ : Nat} {fi₁ : FuncInst Nat} {code : Func} {ps rs : Ty (.list .val)}

/-- The increment function meets `incSpec` under every host. -/
theorem inc_valid (host : HostSemantics Nat) (hcode : fi₁.code = .wasm code)
    (hbody : code.body = incBody) (he : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) : FSpecValid P host a₁ (incSpec a₁ fi₁)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he (fun _ _ ⟨_, _, h⟩ => by simp [h, hps]) ?_
    rintro s args ⟨-, m, rfl⟩ f vs₀
    rw [hbody]
    exact inc_body hrs (forCall_local0 _ _ _) n

/-- **The provider meets the increment interface** with the invariant "the increment
function is at `a₁`", under any import specification. -/
theorem incProvider_sat {I : ScalarInstance} (Ii : ISpec I.E) (haddr : ∀ j, I.addr j = a₁)
    (hcode : fi₁.code = .wasm code) (hbody : code.body = incBody)
    (he : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1) :
    GameSat P I (fun s => s.funcs[a₁]? = some fi₁) Ii (incISpec I.exports) := by
  intro j
  rw [haddr j]
  exact exportSpec_of_inc (inc_valid _ hcode hbody he hps hrs) (fun _ m hs => ⟨hs, m, rfl⟩)
    (fun _ _ _ _ h => h) j

end

/-! ## The consumer -/

section

variable {I : ScalarInstance} {a₂ b : Nat} {fi₂ fib : FuncInst Nat} {x : FuncIdx}
  {code : Func} {ps rs ps' rs' : Ty (.list .val)}

/-- With an import `0` of parameter type `[i32]`, the call `[i32 m]` of host code `0` is an
import question with arguments `[i32 m]`. -/
theorem importOp?_i32 (hti : I.imports[0]?.map FnType.params = some [i32T]) (m : BitVec 32) :
    ∃ e, I.importOp? 0 [.i32 m] = some e ∧ e.2.1 = [.i32 m] := by
  obtain ⟨ft, hft, hps⟩ := Option.map_eq_some_iff.1 hti
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hft
  have hty : List.Forall₂ ScalarType.HasVal (I.imports.get ⟨0, hlt⟩).params [.i32 m] := by
    have hft' : I.imports.get ⟨0, hlt⟩ = ft := hget
    rw [hft', hps]
    exact .cons ⟨m, rfl⟩ .nil
  refine ⟨⟨⟨0, hlt⟩, ⟨[.i32 m], hty⟩⟩, ?_, rfl⟩
  simp only [ScalarInstance.importOp?, ifaceOp?, dite_eq_left hlt, dite_eq_left hty]

/-- What the import specification gives back for the call `[i32 m]`. -/
theorem import_inc_post (hti : I.imports[0]?.map FnType.params = some [i32T]) {s s' : Store Nat}
    {m : BitVec 32} {o : Outcome}
    (h : (importSpec I (incISpec I.imports) 0).post s [.i32 m] s' o) :
    s' = s ∧ o = .normal [.i32 (m + 1)] := by
  obtain ⟨e, hop, he⟩ := importOp?_i32 hti m
  obtain ⟨v, hv, ho⟩ := h.2 e hop
  have hr : Answer.toResult (ft := I.imports.get e.1) v = .values [.i32 (m + 1)] := hv m he
  rw [hr] at ho
  exact ⟨h.1, ho.symm⟩

/-- After the import returns, the client returns its result. -/
theorem client_after (hti : I.imports[0]?.map FnType.params = some [i32T]) {n k : Nat}
    {s s' : Store Nat} {F f : Frame} {vs₀ : List Val} {m : BitVec 32} {o : Outcome}
    (hrs : rs.length = 1) (hc : callPost F [] ((importSpec I (incISpec I.imports) 0).post s
      [.i32 m]) s' F o) :
    seqPostK P (gameHost I (incISpec I.imports)) []
      (bodyPostK P (gameHost I (incISpec I.imports)) rs.length f vs₀
        (callPost f vs₀ ((clientFSpec a₂ fi₂ b fib).post s [.i32 m])) k) n s' F o := by
  rcases hc with ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨a, rfl, hR⟩⟩
  · obtain ⟨rfl, hres⟩ := import_inc_post hti hR
    cases hres
    exact Safe.of_exits (o := .normal [.i32 (m + 1)]) rfl
      ⟨by simp [hrs], rfl, .inl ⟨[.i32 (m + 1)], rfl, rfl, m, rfl, rfl⟩⟩
  · cases (import_inc_post hti hR).2
  · cases (import_inc_post hti hR).2

/-- The client's call of the import stub. -/
theorem client_call (hti : I.imports[0]?.map FnType.params = some [i32T]) {k : Nat}
    {s : Store Nat} {F f : Frame} {vs₀ : List Val} {m : BitVec 32}
    (hx : F.module.funcs[x.toNat]? = some b) (hfb : s.funcs[b]? = some fib)
    (hcodeb : fib.code = .host 0) (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1)
    (hrs : rs.length = 1) :
    HWP P (gameHost I (incISpec I.imports)) s F (vals ([] ++ [.i32 m]) ++ .plain (.call x) :: [])
      (bodyPostK P (gameHost I (incISpec I.imports)) rs.length f vs₀
        (callPost f vs₀ ((clientFSpec a₂ fi₂ b fib).post s [.i32 m])) k)
  | 0 => trivial
  | n + 1 => by
    have hS : importCtx I (incISpec I.imports) (id 0) = some (importSpec I (incISpec I.imports) 0) :=
      rfl
    obtain ⟨e, hop, he⟩ := importOp?_i32 hti m
    have hpre : (Open.stubSpec b 0 (importSpec I (incISpec I.imports) 0)).pre s [.i32 m] :=
      ⟨⟨fib, ps', rs', hfb, hcodeb, heb, by simp [hps']⟩, e, hop, m, he⟩
    exact Safe.callIdx hx hfb (Open.FSpecAt.stub hS n) hpre fun _ _ hc => client_after hti hrs hc

/-- The client function meets `clientFSpec` under the game's environment for `incISpec`. -/
theorem client_valid (hti : I.imports[0]?.map FnType.params = some [i32T])
    (hcode : fi₂.code = .wasm code) (hbody : code.body = clientBody x)
    (he : Expand fi₂.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (hx : fi₂.module.funcs[x.toNat]? = some b) (hcodeb : fib.code = .host 0)
    (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1) :
    FSpecValid P (gameHost I (incISpec I.imports)) a₂ (clientFSpec a₂ fi₂ b fib)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he
      (fun _ _ ⟨_, _, _, h⟩ => by simp [h, hps]) ?_
    rintro s args ⟨-, hfb, m, rfl⟩ f vs₀
    rw [hbody]
    exact HWP.localGet (vs := []) (forCall_local0 _ _ _)
      (client_call (F := Frame.forCall fi₂.module [.i32 m] code.locals) hti hx hfb hcodeb heb hps'
        hrs) n

/-- **The consumer meets the increment interface under the increment interface**, with the
invariant "the client function and the stub are in the store". -/
theorem client_sat (haddr : ∀ j, I.addr j = a₂)
    (hti : I.imports[0]?.map FnType.params = some [i32T])
    (hcode : fi₂.code = .wasm code) (hbody : code.body = clientBody x)
    (he : Expand fi₂.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (hx : fi₂.module.funcs[x.toNat]? = some b) (hcodeb : fib.code = .host 0)
    (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1) :
    GameSat P I (fun s => s.funcs[a₂]? = some fi₂ ∧ s.funcs[b]? = some fib) (incISpec I.imports)
      (incISpec I.exports) := by
  intro j
  rw [haddr j]
  exact exportSpec_of_inc (client_valid hti hcode hbody he hps hrs hx hcodeb heb hps')
    (fun _ m hs => ⟨hs.1, hs.2, m, rfl⟩) (fun _ _ _ _ h => h) j

end

/-! ## The static link -/

section

variable {a₁ a₂ b : Nat} {fi₁ fi₂ fib : FuncInst Nat} {code₁ code₂ : Func} {x : FuncIdx}
  {ps rs ps' rs' : Ty (.list .val)}

/-- **The verified link of the example.** For every static link whose provider exports the
increment function at `a₁` and whose consumer (with host stubs) exports the client
function at `a₂`, calling import `0` through the stub `fib` at `b`, the strategy of the
linked module refines `agStrat Ii (incISpec S.exportTypes)`. -/
theorem inc_link_sound (S : Setup) (hS : S.Scalar) (P : Profile) (Ii : ISpec (ifaceSig []))
    (hpa : ∀ j, S.providerI.addr j = a₁) (hp₁ : S.sp.funcs[a₁]? = some fi₁)
    (hcode₁ : fi₁.code = .wasm code₁) (hbody₁ : code₁.body = incBody)
    (he₁ : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (hca : ∀ j, S.consumerI.addr j = a₂) (hc₂ : S.scs.funcs[a₂]? = some fi₂)
    (hcode₂ : fi₂.code = .wasm code₂) (hbody₂ : code₂.body = clientBody x)
    (he₂ : Expand fi₂.type (.func ps rs)) (hx : fi₂.module.funcs[x.toNat]? = some b)
    (hfb : S.scs.funcs[b]? = some fib) (hcodeb : fib.code = .host 0)
    (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1)
    (hti : S.stubTypes[0]?.map FnType.params = some [i32T]) :
    S.linkedI.σ P ≤ agStrat Ii (incISpec S.exportTypes) :=
  linked_sound S hS P (incProvider_sat Ii hpa hcode₁ hbody₁ he₁ hps hrs) hp₁
    (client_sat (I := S.consumerI) hca hti hcode₂ hbody₂ he₂ hps hrs hx hcodeb heb hps')
    ⟨hc₂, hfb⟩

/-- **The example in the closed world.** Under the hypotheses of `inc_link_sound`, every
host-free Core run of an export call of the linked module on `[i32 m]` that ends in a result
returns `m + 1`. -/
theorem inc_link_answer (S : Setup) (hS : S.Scalar) (P : Profile)
    (hpa : ∀ j, S.providerI.addr j = a₁) (hp₁ : S.sp.funcs[a₁]? = some fi₁)
    (hcode₁ : fi₁.code = .wasm code₁) (hbody₁ : code₁.body = incBody)
    (he₁ : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (hca : ∀ j, S.consumerI.addr j = a₂) (hc₂ : S.scs.funcs[a₂]? = some fi₂)
    (hcode₂ : fi₂.code = .wasm code₂) (hbody₂ : code₂.body = clientBody x)
    (he₂ : Expand fi₂.type (.func ps rs)) (hx : fi₂.module.funcs[x.toNat]? = some b)
    (hfb : S.scs.funcs[b]? = some fib) (hcodeb : fib.code = .host 0)
    (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1)
    (hti : S.stubTypes[0]?.map FnType.params = some [i32T])
    {f : (ifaceSig S.exportTypes).Op} {m : BitVec 32} (hf : f.2.1 = [.i32 m]) {d : Config Nat}
    {r : Result} {w : (ifaceSig S.exportTypes).Ar f}
    (hrun : Steps P (SingleThreaded.Det.noHost : HostSemantics Nat)
      (invoke S.sl (S.linkedI.addr f.1) f.2.1) d)
    (hd : d.code = r.toAdmin) (hw : Answer.ofResult? (S.exportTypes.get f.1) r = some w) :
    Answer.toResult (ft := S.exportTypes.get f.1) w = .values [.i32 (m + 1)] :=
  ag_answer (inc_link_sound S hS P ⟨fun _ => True, fun _ _ => True⟩ hpa hp₁ hcode₁ hbody₁ he₁ hps hrs hca hc₂
      hcode₂ hbody₂ he₂ hx hfb hcodeb heb hps' hti) ⟨m, hf⟩
    (ScalarInstance.ask_ans_iff (I := S.linkedI).2 ⟨d, r, hrun, hd, hw⟩) m hf

end

end Silmaril.Wasm.Logic.GameLink.Examples
