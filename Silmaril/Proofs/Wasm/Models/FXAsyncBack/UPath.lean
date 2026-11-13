module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UExit

/-!
# Paths of unique steps, and isolated stack contexts

* `UPath`: a run each of whose steps is the only step of a non-result configuration;
  `inevP_of_upath`: such a run to `G` makes `G` inevitable;
* `IsoP`, `Wr`: contexts whose holes are isolated once filled with a label, frame or handler;
  **`iso_outer`**: the context of a well-formed stack around its top frame is isolated;
* `quiet_not_term`: quiet code under an isolated context is not a Core result.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (outer comp_hole plug_comp)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append_cons_inj fnvF fnvF_cvals)
open Silmaril.Wasm.Numerics (GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-! ## Paths of unique steps -/

/-- A unique step from a configuration that is not a Core result. -/
def UStepT (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX)
    (a b : ConfigFX H) : Prop :=
  UStep (SD o fx) a b ∧ ¬ TermFX a

/-- A run of unique steps. -/
inductive UPath (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  | one {a b : ConfigFX H} (h : UStepT o fx a b) : UPath o fx a b
  | cons {a b c : ConfigFX H} (h : UStepT o fx a b) (h' : UPath o fx b c) : UPath o fx a c

theorem UPath.trans {a b c : ConfigFX H} (h : UPath o fx a b) (h' : UPath o fx b c) :
    UPath o fx a c := by
  induction h with
  | one h => exact .cons h h'
  | cons h _ ih => exact .cons h (ih h')

theorem inev_of_upath {G : ConfigFX H → Prop} {a b : ConfigFX H} (h : UPath o fx a b)
    (hG : G b) : Inev (SD o fx) TermFX G a := by
  induction h with
  | one h =>
    refine .step h.2 (fun b' hb' => ?_)
    rw [h.1.2 b' hb']
    exact .base hG
  | cons h _ ih =>
    refine .step h.2 (fun b' hb' => ?_)
    rw [h.1.2 b' hb']
    exact ih hG

/-- **A path of unique steps to `G` makes `G` inevitable.** -/
theorem inevP_of_upath {G : ConfigFX H → Prop} {a b : ConfigFX H} (h : UPath o fx a b)
    (hG : G b) : InevP (SD o fx) TermFX G a := by
  cases h with
  | one h =>
    refine ⟨h.2, fun b' hb' => ?_⟩
    rw [h.1.2 b' hb']
    exact .base hG
  | cons h h' =>
    refine ⟨h.2, fun b' hb' => ?_⟩
    rw [h.1.2 b' hb']
    exact inev_of_upath h' hG

/-! ## Quiet code is not a result -/

theorem scalm_not_result {V : List FVal} {a : AdminFX} {T : List AdminFX} (ha : fval? a = none)
    (hc : SCalm a) (r : Result) : fvals V ++ a :: T ≠ r.toAdmin.map .core := by
  intro hr
  cases r with
  | values vs =>
    have h1 : fvals V ++ a :: T = fvals (liftV vs) := by rw [hr, liftV_fvals]; rfl
    exact fvals_ne_cons ha h1.symm
  | trap =>
    have h1 := (fvals_append_cons_inj
      (hr.trans (show [AdminFX.core .trap] = fvals [] ++ .core .trap :: [] from rfl)) ha rfl).2.1
    rw [h1] at hc
    exact hc
  | throw b =>
    have h1 := (fvals_append_cons_inj (hr.trans (throw_code b)) ha rfl).2.1
    rw [h1] at hc
    exact hc

theorem quiet_not_term {X : List AdminFX} (hq : Quiet X) {s : Store H}
    {K : List (Option ContFX)} {f : Frame} : ¬ TermFX (⟨s, K, f, X⟩ : ConfigFX H) := by
  rintro ⟨r, hr⟩
  obtain ⟨⟨V, a, T, hX, ha, hc⟩, -⟩ := hq
  exact scalm_not_result ha hc r (hX ▸ hr)

/-- A unique step of quiet code at the hole of an isolated context, as `UStepT`. -/
theorem ustepT_plug {E : CtxV} (hE : Iso E) {s s' : Store H} {K K' : List (Option ContFX)}
    {f : Frame} {X X' : List AdminFX} (hq : Quiet X)
    (hs : SD o fx ⟨s, K, E.frameAt f, X⟩ ⟨s', K', E.frameAt f, X'⟩)
    (hu : ∀ d, SD o fx ⟨s, K, E.frameAt f, X⟩ d → d = ⟨s', K', E.frameAt f, X'⟩) :
    UStepT o fx ⟨s, K, f, E.plug X⟩ ⟨s', K', f, E.plug X'⟩ :=
  ⟨ustep_plug hE hq hs hu, quiet_not_term (quiet_plug hq E hE)⟩

/-! ## Isolated stack contexts -/

/-- Isolated once the hole is filled with a label, frame or handler. -/
def IsoP : CtxV → Prop
  | .hole => True
  | .seq _ .hole _ => True
  | .seq _ (.label _ _ E) _ => IsoP E
  | .seq _ (.frame _ _ E) _ => IsoP E
  | .seq _ (.handler _ E) _ => IsoP E
  | .seq _ (.seq ..) _ => False
  | .label _ _ E => IsoP E
  | .frame _ _ E => IsoP E
  | .handler _ E => IsoP E

/-- A label, frame or handler at the top. -/
def Wr : CtxV → Prop
  | .label .. | .frame .. | .handler .. => True
  | _ => False

theorem iso_wr {E : CtxV} (hE : Iso E) (hw : Wr E) : ∀ vs rest, Iso (.seq vs E rest) := by
  intro vs rest
  match E, hw with
  | .label _ _ E', _ => exact hE
  | .frame _ _ E', _ => exact hE
  | .handler _ E', _ => exact hE

theorem isoP_wr {E : CtxV} (hE : IsoP E) (hw : Wr E) : ∀ vs rest, IsoP (.seq vs E rest) := by
  intro vs rest
  match E, hw with
  | .label _ _ E', _ => exact hE
  | .frame _ _ E', _ => exact hE
  | .handler _ E', _ => exact hE

theorem iso_comp {E' : CtxV} (hE' : Iso E') (hw : Wr E') :
    ∀ E : CtxV, IsoP E → Iso (comp E E')
  | .hole, _ => hE'
  | .seq vs .hole rest, _ => iso_wr hE' hw vs rest
  | .seq _ (.label _ _ E) _, h => iso_comp hE' hw E h
  | .seq _ (.frame _ _ E) _, h => iso_comp hE' hw E h
  | .seq _ (.handler _ E) _, h => iso_comp hE' hw E h
  | .label _ _ E, h => iso_comp hE' hw E h
  | .frame _ _ E, h => iso_comp hE' hw E h
  | .handler _ E, h => iso_comp hE' hw E h

theorem isoP_comp {E' : CtxV} (hE' : IsoP E') (hw : Wr E') :
    ∀ E : CtxV, IsoP E → IsoP (comp E E')
  | .hole, _ => hE'
  | .seq vs .hole rest, _ => isoP_wr hE' hw vs rest
  | .seq _ (.label _ _ E) _, h => isoP_comp hE' hw E h
  | .seq _ (.frame _ _ E) _, h => isoP_comp hE' hw E h
  | .seq _ (.handler _ E) _, h => isoP_comp hE' hw E h
  | .label _ _ E, h => isoP_comp hE' hw E h
  | .frame _ _ E, h => isoP_comp hE' hw E h
  | .handler _ E, h => isoP_comp hE' hw E h

variable (S : Setup H)

theorem isoP_kind (k : Kind) {E : CtxV} (hE : IsoP E) : IsoP (kindCtx k E) := by
  cases k <;> exact hE

theorem isoP_wait (vs : List FVal) (rest : List AdminFX) (w : Option (List Clause)) (wa : WA) :
    IsoP (.seq vs (waitCtx S w wa) rest) := by
  unfold waitCtx
  split <;> trivial

theorem isoP_low (p : SFrame Val × Ann) : IsoP (lowCtx S p) :=
  isoP_kind _ (isoP_wait S _ _ _ _)

theorem wr_low {p : SFrame Val × Ann} (hp : p.2.kind.isRoot = false) : Wr (lowCtx S p) := by
  unfold lowCtx
  match p.2.kind, hp with
  | .fn _, _ => trivial
  | .blk, _ => trivial

/-- Only the last frame of the stack is the root. -/
def RootLast : List (SFrame Val × Ann) → Prop
  | [] => True
  | p :: ps => (p.2.kind.isRoot = true → ps = []) ∧ RootLast ps

theorem isoP_lows : ∀ (rs : List (SFrame Val × Ann)), RootLast rs → IsoP (lowsCtx S rs)
  | [], _ => trivial
  | p :: ps, ⟨hp, hps⟩ => by
    show IsoP (Silmaril.Wasm.Models.FXAsyncFX.comp (lowsCtx S ps) (lowCtx S p))
    cases hk : p.2.kind.isRoot with
    | true =>
      obtain rfl := hp hk
      exact isoP_low S p
    | false => exact isoP_comp (isoP_low S p) (wr_low S hk) _ (isoP_lows ps hps)

theorem rootLast_of_shape {st : List (SFrame Val × Ann)}
    (h : Silmaril.Proofs.Wasm.Models.FXAsyncFX.RootShape st) : RootLast st := by
  obtain ⟨init, last, rfl, -, hinit⟩ := h
  induction init with
  | nil => exact ⟨fun _ => rfl, trivial⟩
  | cons q init ih =>
    refine ⟨fun hq => absurd hq (by simp [hinit q (List.mem_cons_self ..)]), ih ?_⟩
    exact fun p hp => hinit p (List.mem_cons_of_mem _ hp)

/-- **The context of a well-formed stack around its top frame is isolated.** -/
theorem iso_outer {W : Prog (Ins Val)} {p : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (hmain : MainOk S W (p :: rs)) : Iso (outer S rs p.2.kind) := by
  have hl : RootLast (p :: rs) := rootLast_of_shape hmain.2.2
  unfold outer
  cases hk : p.2.kind with
  | root =>
    obtain rfl := hl.1 (by simp [hk, Kind.isRoot])
    trivial
  | fn fi =>
    have h := iso_comp (E' := .frame 1 fi (.label 1 [] .hole)) trivial trivial _
      (isoP_lows S rs hl.2)
    exact h
  | blk =>
    have h := iso_comp (E' := .label 1 [] .hole) trivial trivial _ (isoP_lows S rs hl.2)
    exact h

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
