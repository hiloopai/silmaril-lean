module

public import Silmaril.Wasm.Logic.OpenExamples.Defs

/-!
# Example: a module calling an import, and its link with a provider

* `incMod_sat`: the provider meets `incSpec` with no imports;
* `clientMod_sat`: the client meets `clientSpec` under the import specification
  `incSpec` (its call of the import stub is proved with `Open.FSpecAt.stub` and
  `Hoare.Safe.callIdx`; nothing about the import's code is assumed);
* `link_example`: linked, the two modules' strategies refine the assume/guarantee
  strategy of no imports and the client's export (`Open.link_refines`).

Every profile, partial correctness. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Games
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Strategy (ctxSpec agStrat)
open Silmaril.Wasm.Logic.HoareExamples (x0 forCall_local0)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Single modules and contexts -/

theorem OMod.single_has {a : Nat} {fi : FuncInst H} {s : Store H} (h : s.funcs[a]? = some fi) :
    (OMod.single a fi).Has s := fun a' fi' h' => by
  by_cases ha : a' = a
  · subst ha
    have hfi : fi = fi' := by simpa [OMod.single] using h'
    exact hfi ▸ h
  · simp [OMod.single, ha] at h'

theorem ctxSingle_some {a a' : Nat} {S S' : FSpec H} (h : ctxSingle a S a' = some S') :
    a' = a ∧ S' = S := by
  by_cases ha : a' = a
  · exact ⟨ha, by simpa [ctxSingle, ha] using h.symm⟩
  · simp [ctxSingle, ha] at h

theorem ctxSingle_self (a : Nat) (S : FSpec H) : ctxSingle a S a = some S := by
  simp [ctxSingle]

/-- The shape condition of `ModuleSat` for a single function. -/
theorem single_shape {a : Nat} {fi : FuncInst H} {S : FSpec H}
    (hpre : ∀ s args, S.pre s args → s.funcs[a]? = some fi) :
    ∀ a' S', ctxSingle a S a' = some S' →
      ((OMod.single a fi).funcs a').isSome ∧ ∀ s args, S'.pre s args → (OMod.single a fi).Has s :=
  fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := ctxSingle_some h
    exact ⟨by simp [OMod.single], fun s args hp => OMod.single_has (hpre s args hp)⟩

/-! ## The provider -/

section

variable {a₁ : Nat} {fi₁ : FuncInst H} {ps rs : Ty (.list .val)}

/-- Returning `m + 1` meets the provider's body postcondition. -/
theorem inc_ret {k : Nat} {s : Store H} {F f : Frame} {vs₀ : List Val} {m : BitVec 32}
    (hrs : rs.length = 1) :
    bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((incSpec a₁ fi₁).post s [.i32 m])) k
      s F (.normal [.i32 (m + 1)]) :=
  ⟨by simp [hrs], rfl, .inl ⟨[.i32 (m + 1)], rfl, rfl, m, rfl, rfl⟩⟩

/-- The provider's body. -/
theorem inc_body {k : Nat} {s : Store H} {F f : Frame} {vs₀ : List Val} {m : BitVec 32}
    (hrs : rs.length = 1) (hloc : F.local? x0 = some (some (.i32 m))) :
    HWP P host s F (expression incBody)
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((incSpec a₁ fi₁).post s [.i32 m])) k) := by
  have hadd : HWP P host s F
      (vals ([] ++ [Val.num ⟨.int .i32, m⟩, .num ⟨.int .i32, 1⟩]) ++ .plain (.intBinOp .i32 .add) :: [])
      (bodyPostK P host rs.length f vs₀ (callPost f vs₀ ((incSpec a₁ fi₁).post s [.i32 m])) k) :=
    HWP.intBinOp (fun z hz => by cases hz; exact HWP.of_vals (vs := [.i32 (m + 1)]) (inc_ret hrs))
      fun e he => by cases he
  exact HWP.localGet (vs := []) hloc hadd

/-- **The provider meets its specification**, importing nothing. -/
theorem incMod_sat {code : Func} (bind : H → Nat) (hcode : fi₁.code = .wasm code)
    (hbody : code.body = incBody) (he : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) :
    ModuleSat P (OMod.single a₁ fi₁) bind (fun _ => none) (ctxSingle a₁ (incSpec a₁ fi₁)) := by
  refine ⟨single_shape fun _ _ h => h.1, fun n a S hS => ?_⟩
  obtain ⟨rfl, rfl⟩ := ctxSingle_some hS
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he (fun _ _ ⟨_, _, h⟩ => by simp [h, hps]) ?_
    rintro s args ⟨-, m, rfl⟩ f vs₀
    rw [hbody]
    exact inc_body hrs (forCall_local0 _ _ _) n

end

/-! ## The client -/

section

variable {a₁ a₂ b : Nat} {fi₁ fi₂ fib : FuncInst H} {h : H} {bind : H → Nat} {x : FuncIdx}
  {ps rs ps' rs' : Ty (.list .val)}

/-- What the import's specification gives back. -/
theorem inc_post_inv {s s' : Store H} {m : BitVec 32} {o : Outcome}
    (h : (incSpec a₁ fi₁).post s [.i32 m] s' o) : s' = s ∧ o = .normal [.i32 (m + 1)] := by
  obtain ⟨hs, m', hm, ho⟩ := h
  have hm' : m = m' := (i32_inj (List.cons.inj hm).1).symm
  exact ⟨hs, hm' ▸ ho⟩

/-- After the import returns, the client returns its result. -/
theorem client_after {n k : Nat} {s s' : Store H} {F f : Frame} {vs₀ : List Val} {m : BitVec 32}
    {o : Outcome} (hrs : rs.length = 1)
    (hc : callPost F [] ((incSpec a₁ fi₁).post s [.i32 m]) s' F o) :
    seqPostK P (specHost bind (ctxSingle a₁ (incSpec a₁ fi₁))) []
      (bodyPostK P (specHost bind (ctxSingle a₁ (incSpec a₁ fi₁))) rs.length f vs₀
        (callPost f vs₀ ((clientSpec a₂ fi₂ b fib a₁ fi₁).post s [.i32 m])) k) n s' F o := by
  rcases hc with ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨a, rfl, hR⟩⟩
  · obtain ⟨rfl, hres⟩ := inc_post_inv hR
    cases hres
    exact Safe.of_exits (o := .normal [.i32 (m + 1)]) rfl
      ⟨by simp [hrs], rfl, .inl ⟨[.i32 (m + 1)], rfl, rfl, m, rfl, rfl⟩⟩
  · cases (inc_post_inv hR).2
  · cases (inc_post_inv hR).2

/-- The client's call of the import stub. -/
theorem client_call {k : Nat} {s : Store H} {F f : Frame} {vs₀ : List Val} {m : BitVec 32}
    (hx : F.module.funcs[x.toNat]? = some b) (hfb : s.funcs[b]? = some fib)
    (hcodeb : fib.code = .host h) (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1)
    (hbind : bind h = a₁) (hf₁ : s.funcs[a₁]? = some fi₁) (hrs : rs.length = 1) :
    HWP P (specHost bind (ctxSingle a₁ (incSpec a₁ fi₁))) s F
      (vals ([] ++ [.i32 m]) ++ .plain (.call x) :: [])
      (bodyPostK P (specHost bind (ctxSingle a₁ (incSpec a₁ fi₁))) rs.length f vs₀
        (callPost f vs₀ ((clientSpec a₂ fi₂ b fib a₁ fi₁).post s [.i32 m])) k)
  | 0 => trivial
  | n + 1 => by
    have hS : ctxSingle a₁ (incSpec a₁ fi₁) (bind h) = some (incSpec a₁ fi₁) :=
      hbind ▸ ctxSingle_self a₁ _
    have hpre : (stubSpec b h (incSpec a₁ fi₁)).pre s [.i32 m] :=
      ⟨⟨fib, ps', rs', hfb, hcodeb, heb, by simp [hps']⟩, hf₁, m, rfl⟩
    exact Safe.callIdx hx hfb (FSpecAt.stub hS n) hpre fun _ _ hc => client_after hrs hc

/-- **The client meets its specification under the import specification.** -/
theorem clientMod_sat {code : Func} (hcode : fi₂.code = .wasm code) (hbody : code.body = clientBody x)
    (he : Expand fi₂.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1)
    (hx : fi₂.module.funcs[x.toNat]? = some b) (hcodeb : fib.code = .host h)
    (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1) (hbind : bind h = a₁) :
    ModuleSat P (OMod.single a₂ fi₂) bind (ctxSingle a₁ (incSpec a₁ fi₁))
      (ctxSingle a₂ (clientSpec a₂ fi₂ b fib a₁ fi₁)) := by
  refine ⟨single_shape fun _ _ h => h.1, fun n a S hS => ?_⟩
  obtain ⟨rfl, rfl⟩ := ctxSingle_some hS
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he
      (fun _ _ ⟨_, _, _, _, h⟩ => by simp [h, hps]) ?_
    rintro s args ⟨-, hfb, hf₁, m, rfl⟩ f vs₀
    rw [hbody]
    exact HWP.localGet (vs := []) (forCall_local0 _ _ _)
      (client_call (F := Frame.forCall fi₂.module [.i32 m] code.locals) hx hfb hcodeb heb hps'
        hbind hf₁ hrs) n

/-- **Linking.** The provider's strategy composed with the client's (the client's
import calls answered by the provider) refines the assume/guarantee strategy of
no imports and the client's export specification. -/
theorem link_example {code₁ code₂ : Func} {bind₁ : H → Nat} (hcode₁ : fi₁.code = .wasm code₁)
    (hbody₁ : code₁.body = incBody) (he₁ : Expand fi₁.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) (hcode₂ : fi₂.code = .wasm code₂) (hbody₂ : code₂.body = clientBody x)
    (he₂ : Expand fi₂.type (.func ps rs)) (hx : fi₂.module.funcs[x.toNat]? = some b)
    (hcodeb : fib.code = .host h) (heb : Expand fib.type (.func ps' rs')) (hps' : ps'.length = 1)
    (hbind : bind h = a₁) :
    (modStrat P (OMod.single a₁ fi₁) bind₁).comp (modStrat P (OMod.single a₂ fi₂) bind) ≤
      agStrat (ctxSpec (fun _ => none)) (ctxSpec (ctxSingle a₂ (clientSpec a₂ fi₂ b fib a₁ fi₁))) :=
  link_refines (incMod_sat bind₁ hcode₁ hbody₁ he₁ hps hrs)
    (clientMod_sat hcode₂ hbody₂ he₂ hps hrs hx hcodeb heb hps' hbind)

end

end Silmaril.Wasm.Logic.OpenExamples
