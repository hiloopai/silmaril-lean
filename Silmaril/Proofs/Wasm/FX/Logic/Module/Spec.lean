module

public import Silmaril.Wasm.FX.Logic.EveryRun.Instr.Thms
public import Silmaril.Wasm.FX.Logic.Module.Defs

/-!
# Function specifications for WasmFX functions: proofs

The module rules of `Silmaril.Wasm.FX.Logic.Module.Defs`, ported from
`Silmaril.Proofs.Wasm.Logic.Hoare.{Call,Module}` to `StepFX'` (no host calls):

* `inv_callPost`: the call postcondition is invariant when the specification's is;
* **`fspecAt_of_body`**: a specification of an FX function from its body (one step enters the
  frame and the label); **`fspecT_of_body`**, the total version;
* **`safe_call_spec`** / **`tsafe_call_spec`**: the call rule through a `CALL_REF` form, then
  code; **`safe_callIdx_spec`** / **`tsafe_callIdx_spec`**: the same for `call x`;
* **`Ctx.valid_of_step`** (mutual recursion, Löb induction on the index), `CtxSat.valid`,
  `CtxSat.weaken`, **`CtxSat.link`** (two groups of functions that call each other).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.Module

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Safe TSafe Inv seqPost safeJ totJ)
open Silmaril.Wasm.FX.Logic.Module
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

theorem liftV_inj' : ∀ {vs ws : List Val}, liftV vs = liftV ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [liftV] at h
  | _ :: _, [], h => by simp [liftV] at h
  | v :: vs, w :: ws, h => by
    simp only [liftV, List.map_cons, List.cons.injEq, FVal.val.injEq] at h
    rw [h.1, liftV_inj' (vs := vs) (ws := ws) (by simpa [liftV] using h.2)]

/-- The arguments of a call are its last values. -/
theorem split_args {vs₀ V₁ : List FVal} {args vs : List Val}
    (hV : vs₀ ++ liftV args = V₁ ++ liftV vs) (hn : vs.length = args.length) :
    V₁ = vs₀ ∧ vs = args := by
  obtain ⟨h1, h2⟩ := List.append_inj' hV (by simp [liftV, hn])
  exact ⟨h1.symm, (liftV_inj' h2).symm⟩

theorem inv_callPost {f : Frame} {vs₀ : List FVal} {R : Store H → Conts → OutcomeFX → Prop}
    (hR : InvO R) : Inv (callPost f vs₀ R) :=
  ⟨fun s K f' E E' vs x hp h => ⟨h.1, hR.1 s K f' E E' vs x hp h.2⟩,
    fun s K f' E E' vs k ct x hp h => ⟨h.1, hR.2 s K f' E E' vs k ct x hp h.2⟩⟩

/-! ## Specifications from bodies -/

/-- **A specification from the body**: one step enters the frame and the label, after which
the body must be safe for `n` steps. -/
theorem fspecAt_of_body {n a : Nat} {S : FSpec H} {fi : FuncInst H} {hh : H} {F : FuncFX}
    (hfi : ∀ s K args, S.pre s K args → s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hfx : fx hh = some F)
    (hlen : ∀ s K args, S.pre s K args → args.length = F.nparams)
    (hinv : ∀ s K args, S.pre s K args → InvO (S.post s K args))
    (hbody : ∀ s K args, S.pre s K args → ∀ (f : Frame) (vs₀ : List FVal),
      Safe P fx (bodyPost P fx F.nresults f vs₀ (callPost f vs₀ (S.post s K args)) n) n
        ⟨s, K, Frame.forCall F.module args F.locals, F.body.map InstrFX.toAdmin⟩) :
    FSpecAt P fx (n + 1) a S := by
  intro s K args hpre f vs₀ c hc
  have hQ := inv_callPost (f := f) (vs₀ := vs₀) (hinv s K args hpre)
  refine safe_invoke hc (hfi s K args hpre) hcode hfx fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ := split_args hV (by rw [hn, hlen s K args hpre])
  have h1 := safe_label (k := n) (us := []) (inv_framePost hQ _ _ _) (by omega)
    (hbody s K vs hpre f V₁)
  exact safe_frame (c := ⟨s, K, Frame.forCall F.module vs F.locals,
    [.label F.nresults [] (F.body.map InstrFX.toAdmin)]⟩) hQ (by simpa using h1)

/-- **A total specification from the body.** -/
theorem fspecT_of_body {a : Nat} {S : FSpec H} {fi : FuncInst H} {hh : H} {F : FuncFX}
    (hfi : ∀ s K args, S.pre s K args → s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hfx : fx hh = some F)
    (hlen : ∀ s K args, S.pre s K args → args.length = F.nparams)
    (hinv : ∀ s K args, S.pre s K args → InvO (S.post s K args))
    (hbody : ∀ s K args, S.pre s K args → ∀ (f : Frame) (vs₀ : List FVal),
      TSafe P fx (bodyPostT P fx F.nresults f vs₀ (callPost f vs₀ (S.post s K args)))
        ⟨s, K, Frame.forCall F.module args F.locals, F.body.map InstrFX.toAdmin⟩) :
    FSpecT P fx a S := by
  intro s K args hpre f vs₀ c hc
  have hQ := inv_callPost (f := f) (vs₀ := vs₀) (hinv s K args hpre)
  refine tsafe_invoke hc (hfi s K args hpre) hcode hfx fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ := split_args hV (by rw [hn, hlen s K args hpre])
  exact tsafe_frame' hQ (tsafe_label' (us := []) (inv_framePost hQ _ _ _) (hbody s K vs hpre f V₁))

/-! ## The call rules -/

section Call

variable {Q : PostFX H} {s : Store H} {K : Conts} {f : Frame} {vs₀ : List FVal} {args : List Val}
  {rest : List AdminFX} {S : FSpec H}

/-- **The call rule** through a `CALL_REF` form, then code. -/
theorem safe_call_spec {n a : Nat} {c : Admin} (hQ : Inv Q) (hS : FSpecAt P fx n a S)
    (hpre : S.pre s K args) (hc : c.IsCallRef)
    (hpost : ∀ s' K' o, callPost f vs₀ (S.post s K args) s' K' f o →
      seqPost (safeJ P fx Q n) rest Q s' K' f o) :
    Safe P fx Q n ⟨s, K, f, callCode vs₀ args a c ++ rest⟩ :=
  safe_seq (c := ⟨s, K, f, callCode vs₀ args a c⟩) hQ le_rfl
    (safe_post_mono (fun s' K' f' o h => by
      have hf : f' = f := h.1
      subst hf
      exact hpost s' K' o h) (hS s K args hpre f vs₀ c hc))

/-- **The call rule**, total correctness. -/
theorem tsafe_call_spec {a : Nat} {c : Admin} (hQ : Inv Q) (hS : FSpecT P fx a S)
    (hpre : S.pre s K args) (hc : c.IsCallRef)
    (hpost : ∀ s' K' o, callPost f vs₀ (S.post s K args) s' K' f o →
      seqPost (totJ P fx Q) rest Q s' K' f o) :
    TSafe P fx Q ⟨s, K, f, callCode vs₀ args a c ++ rest⟩ :=
  tsafe_seq' hQ (tsafe_mono (fun s' K' f' o h => by
      have hf : f' = f := h.1
      subst hf
      exact hpost s' K' o h) (hS s K args hpre f vs₀ c hc))

theorem call_code_eq {V₁ : List FVal} {vs : List Val} {a : Nat} {fi : FuncInst H}
    (hV : vs₀ ++ liftV args = V₁ ++ liftV (vs ++ [])) :
    fvals V₁ ++ (fvals (liftV vs) ++
        [Admin.ref (.func a), Admin.callRefType fi.type].map AdminFX.core) ++ rest =
      callCode vs₀ args a (.callRefType fi.type) ++ rest := by
  have hV' : vs₀ ++ liftV args = V₁ ++ liftV vs := by simpa using hV
  simp only [callCode, hV']
  simp [fvals, liftV, FVal.toAdmin, Val.toAdmin]

/-- **The call rule for `call x`.** -/
theorem safe_callIdx_spec {n a : Nat} {x : FuncIdx} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) (hQ : Inv Q)
    (hS : FSpecAt P fx n a S) (hpre : S.pre s K args)
    (hpost : ∀ s' K' o, callPost f vs₀ (S.post s K args) s' K' f o →
      seqPost (safeJ P fx Q n) rest Q s' K' f o) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (vs₀ ++ liftV args) ++ .core (.plain
        (.call x)) :: rest⟩ := by
  refine safe_last_seq (notStop_core_plain rfl (by simp) (by simp) (by simp))
    fun V₁ V₂ y' hV hroot => ?_
  obtain ⟨vs, args', c₀, rfl, hh, rfl⟩ := inert_root ⟨rfl, by simp, rfl⟩ (by simp) hroot
  obtain ⟨rfl, a', fi', ha', hf', rfl⟩ := Silmaril.Wasm.Logic.Hoare.head_call hh
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  show Safe P fx Q n ⟨s, K, f, fvals V₁ ++ (fvals (liftV vs) ++
    [Admin.ref (.func a'), Admin.callRefType fi'.type].map AdminFX.core) ++ rest⟩
  rw [call_code_eq hV]
  exact safe_call_spec hQ hS hpre trivial hpost

/-- **The call rule for `call x`**, total correctness. -/
theorem tsafe_callIdx_spec {a : Nat} {x : FuncIdx} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) (hQ : Inv Q)
    (hS : FSpecT P fx a S) (hpre : S.pre s K args)
    (hpost : ∀ s' K' o, callPost f vs₀ (S.post s K args) s' K' f o →
      seqPost (totJ P fx Q) rest Q s' K' f o) :
    TSafe P fx Q ⟨s, K, f, fvals (vs₀ ++ liftV args) ++ .core (.plain (.call x)) :: rest⟩ := by
  refine tsafe_last_seq (notStop_core_plain rfl (by simp) (by simp) (by simp))
    fun V₁ V₂ y' hV hroot => ?_
  obtain ⟨vs, args', c₀, rfl, hh, rfl⟩ := inert_root ⟨rfl, by simp, rfl⟩ (by simp) hroot
  obtain ⟨rfl, a', fi', ha', hf', rfl⟩ := Silmaril.Wasm.Logic.Hoare.head_call hh
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  show TSafe P fx Q ⟨s, K, f, fvals V₁ ++ (fvals (liftV vs) ++
    [Admin.ref (.func a'), Admin.callRefType fi'.type].map AdminFX.core) ++ rest⟩
  rw [call_code_eq hV]
  exact tsafe_call_spec hQ hS hpre trivial hpost

end Call

/-! ## Contexts and mutual recursion -/

/-- Fewer steps. -/
theorem fspecAt_mono {n m a : Nat} {S : FSpec H} (hmn : m ≤ n) (h : FSpecAt P fx n a S) :
    FSpecAt P fx m a S := fun s K args hpre f vs₀ c hc =>
  safe_mono hmn (h s K args hpre f vs₀ c hc)

/-- A total specification holds for every number of steps. -/
theorem fspecT_at {a : Nat} {S : FSpec H} (h : FSpecT P fx a S) (n : Nat) : FSpecAt P fx n a S :=
  fun s K args hpre f vs₀ c hc => tsafe_hwp (h s K args hpre f vs₀ c hc) n

/-- **Mutual recursion** (Löb induction on the step index). -/
theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.valid_of_step {Γ : Ctx H}
    (h : ∀ n, Ctx.ValidAt P fx n Γ → Ctx.ValidAt P fx (n + 1) Γ) : Ctx.Valid P fx Γ := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ _ _ _ _ => trivial
  | succ n ih => exact h n ih

theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.ValidAt.of_le {n : Nat} {Γ Γ' : Ctx H}
    (hle : Ctx.Le Γ Γ')
    (h : Ctx.ValidAt P fx n Γ') : Ctx.ValidAt P fx n Γ :=
  fun a S hS => h a S (hle a S hS)

theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.union_some {Γ Γ' : Ctx H} {a : Nat} {S : FSpec H}
    (h : Ctx.union Γ Γ' a = some S) :
    Γ a = some S ∨ Γ' a = some S := by
  unfold Ctx.union at h
  cases hg : Γ a with
  | none => rw [hg] at h; exact .inr h
  | some S' => rw [hg] at h; exact .inl h

theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.ValidAt.union {n : Nat} {Γ Γ' : Ctx H}
    (h : Ctx.ValidAt P fx n Γ)
    (h' : Ctx.ValidAt P fx n Γ') : Ctx.ValidAt P fx n (Ctx.union Γ Γ') := fun a S hS =>
  (Ctx.union_some hS).elim (h a S) (h' a S)

theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.ValidAt.union_left {n : Nat} {Γ Γ' : Ctx H}
    (h : Ctx.ValidAt P fx n (Ctx.union Γ Γ')) : Ctx.ValidAt P fx n Γ := fun a S hS =>
  h a S (by simp [Ctx.union, hS])

theorem _root_.Silmaril.Wasm.FX.Logic.Module.Ctx.ValidAt.union_right {n : Nat} {Γ Γ' : Ctx H}
    (hd : ∀ a, Γ a = none ∨ Γ' a = none)
    (h : Ctx.ValidAt P fx n (Ctx.union Γ Γ')) : Ctx.ValidAt P fx n Γ' := fun a S hS => by
  rcases hd a with hn | hn
  · exact h a S (by simp [Ctx.union, hn, hS])
  · rw [hn] at hS; cases hS

/-- Valid imports give valid exports. -/
theorem _root_.Silmaril.Wasm.FX.Logic.Module.CtxSat.valid {Γi Γe : Ctx H} (hm : CtxSat P fx Γi Γe)
    (hi : Ctx.Valid P fx Γi) :
    Ctx.Valid P fx Γe :=
  Ctx.valid_of_step fun n h => hm n (hi n) h

/-- Weaker exports and stronger imports. -/
theorem _root_.Silmaril.Wasm.FX.Logic.Module.CtxSat.weaken {Γi Γi' Γe Γe' : Ctx H}
    (hm : CtxSat P fx Γi Γe) (hi : Ctx.Le Γi Γi')
    (he : Ctx.Le Γe' Γe)
    (hall : ∀ n, Ctx.ValidAt P fx n Γe' → Ctx.ValidAt P fx n Γe) : CtxSat P fx Γi' Γe' :=
  fun n hvi hve => (hm n (hvi.of_le hi) (hall n hve)).of_le he

/-- **Joining contexts** whose imports are provided by common imports or by each other's
exports (mutual recursion across groups). -/
theorem _root_.Silmaril.Wasm.FX.Logic.Module.CtxSat.link {Γi Γi₁ Γi₂ Γe₁ Γe₂ : Ctx H}
    (h₁ : CtxSat P fx Γi₁ Γe₁)
    (h₂ : CtxSat P fx Γi₂ Γe₂) (hd : ∀ a, Γe₁ a = none ∨ Γe₂ a = none)
    (hi₁ : ∀ n, Ctx.ValidAt P fx n Γi → Ctx.ValidAt P fx n Γe₂ → Ctx.ValidAt P fx n Γi₁)
    (hi₂ : ∀ n, Ctx.ValidAt P fx n Γi → Ctx.ValidAt P fx n Γe₁ → Ctx.ValidAt P fx n Γi₂) :
    CtxSat P fx Γi (Ctx.union Γe₁ Γe₂) := by
  intro n hi he
  have he₁ : Ctx.ValidAt P fx n Γe₁ := he.union_left
  have he₂ : Ctx.ValidAt P fx n Γe₂ := he.union_right hd
  exact (h₁ n (hi₁ n hi he₂) he₁).union (h₂ n (hi₂ n hi he₁) he₂)

/-- A context of specifications each proved from its body for `n + 1` steps, assuming the
contexts for `n` steps. -/
theorem _root_.Silmaril.Wasm.FX.Logic.Module.CtxSat.of_bodies {Γi Γe : Ctx H}
    (h : ∀ n, Ctx.ValidAt P fx n Γi → Ctx.ValidAt P fx n Γe → ∀ a S, Γe a = some S →
      FSpecAt P fx (n + 1) a S) : CtxSat P fx Γi Γe :=
  fun n hi he a S hS => h n hi he a S hS

end Silmaril.Proofs.Wasm.FX.Logic.Module
