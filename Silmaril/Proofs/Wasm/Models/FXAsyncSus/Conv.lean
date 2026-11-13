module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Kernel

/-!
# The converse of `kernel_in_fx` with `suspend`: the tight fragment

`Silmaril.Wasm.Models.FXAsyncBack.beh_eq` covers the calm fragment (no `suspend` executed).
`StepFX'` is not deterministic at `suspend` (`suspend_nondet`), so it does not extend as it
stands. The right restatement keeps `suspend` and asks instead that **every executed `suspend`
finds exactly its payload on its frame** (`TightTop`, `TightSupported`): then each `StepFX'`
choice other than the intended one is a dead end (`inev_suspend`), and:

* `umatched_suspend`, `umatched_top_tight`, `umatched_rel_tight`: the backward obligation holds
  at every related configuration of the tight fragment;
* **`fx_in_kernel_tight`**, **`beh_eq_tight`**: the `StepFX'` behaviours of the encoding are
  exactly the images of the kernel's behaviours;
* `tight_of_calm`: the calm fragment is tight, so `beh_eq_tight` extends `beh_eq`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SV SFrame SCfg Ins Prog sstep sexec split lookup popN Res
  Outcome runN beh)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX Top cfgOf sstep_exec popN_eq fine_cons
  supported_next fine_of_supported runN_succ_next)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (SD TermFX InevP UMatched BackHyp CalmTop calmCfg
  CalmSupported umatched_top sx_eq fx_sub_kernel)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- A `suspend` on top finds exactly its payload on its frame. -/
def TightTop (fr : SFrame Val) : Bool :=
  match fr.code with
  | .suspend _ n :: _ => fr.ops.length == n
  | _ => true

/-- The top frame of a configuration is tight. -/
def tightCfg (x : SCfg Val) : Bool :=
  match x.stack with
  | fr :: _ => TightTop fr
  | [] => true

/-- **The tight fragment along a run**: `Supported`, and every executed `suspend` finds exactly
its payload on its frame. -/
def TightSupported (W : Prog (Ins Val)) (x : SCfg Val) : Prop :=
  Supported W x ∧ ∀ n y, runN (sstep W i32Test) n x = .next y → tightCfg y = true

theorem tightSupported_next {x x' : SCfg Val} (h : TightSupported W x)
    (hs : sstep W i32Test x = .next x') : TightSupported W x' :=
  ⟨supported_next h.1 hs, fun n y hy => h.2 (n + 1) y (by rw [runN_succ_next hs]; exact hy)⟩

theorem tightTop_of_calm {fr : SFrame Val} (h : CalmTop fr = true) : TightTop fr = true := by
  unfold CalmTop at h
  unfold TightTop
  split
  · next c n c' hc => simp [hc] at h
  · rfl

/-- **The calm fragment is tight.** -/
theorem tight_of_calm {x : SCfg Val} (h : CalmSupported W x) : TightSupported W x := by
  refine ⟨h.1, fun n y hy => ?_⟩
  have hc : calmCfg y = true := h.2 n y hy
  unfold calmCfg at hc
  unfold tightCfg
  split
  · next fr rest hst => simp only [hst] at hc; exact tightTop_of_calm hc
  · rfl

variable {KK : List (Option (List (SFrame Val)))} {K : List (Option ContFX)} {fr : SFrame Val}
  {a : Ann} {rs : List (SFrame Val × Ann)}

/-- **A tight `suspend` is matched backwards.** -/
theorem umatched_suspend (hS : SX S = SD o S.fx) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    {t : Nat} {c : List (Ins Val)} {Y : List InstrFX} (hc : fr.code = .suspend t (S.ar t) :: c)
    (hY : a.code = .fx (.suspend (S.xt t)) :: Y) (htag : TagOk S t) (henc : EncI S W c Y)
    (htight : fr.ops.length = S.ar t) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.suspend t (S.ar t)) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  obtain ⟨pl, o', hp⟩ : ∃ pl o', popN (S.ar t) fr.ops = some (pl, o') := by
    match hpp : popN (S.ar t) fr.ops with
    | some (pl, o') => exact ⟨pl, o', rfl⟩
    | none => exact absurd (by simp only [sexec, hpp]) hnt
  obtain ⟨m, h, r, rs', hsp⟩ : ∃ m h r rs', split t (rs.map Prod.fst) = some (m, h, r, rs') := by
    match hss : split t (rs.map Prod.fst) with
    | some (m, h, r, rs') => exact ⟨m, h, r, rs', rfl⟩
    | none => exact absurd (by simp only [sexec, hp, hss]) hnt
  obtain ⟨np, body, hW⟩ : ∃ np body, W h = some (np, body) := by
    match hww : W h with
    | some (np, body) => exact ⟨np, body, rfl⟩
    | none => exact absurd (by simp only [sexec, hp, hsp, hww]) hnt
  have hstep : sexec W i32Test KK fr (.suspend t (S.ar t)) c (rs.map Prod.fst) =
      .next ⟨KK ++ [some ({ fr with code := c, ops := o' } :: m)],
        ⟨body, .cont KK.length :: pl, none⟩ :: { r with wait := none } :: rs'⟩ := by
    simp only [sexec, hp, hsp, hW]
  have hpe : fr.ops = pl ++ o' ∧ pl.length = S.ar t := popN_eq hp
  have ho : o' = [] := by
    have hl : (pl ++ o').length = S.ar t := by rw [← hpe.1]; exact htight
    rw [List.length_append, hpe.2] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hops : fr.ops = pl := by rw [hpe.1, ho, List.append_nil]
  rw [hstep, ho]
  exact inev_suspend S hS hok hT.main hT.conts hops hpe.2 hY htag henc hsp hW

/-- **Every kernel step from a tight top frame in the fragment is matched backwards.** -/
theorem umatched_top_tight (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    (htight : TightTop fr = true) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  cases hcalm : CalmTop fr with
  | true => exact umatched_top S hS hP hH hok hT hcalm
  | false =>
    have henc : EncI S W fr.code a.code := (hT.main.1 _ (List.mem_cons_self ..)).1
    generalize hc : fr.code = code at henc
    generalize hY : a.code = Y at henc
    cases henc with
    | @suspend c Y' t htag h =>
      have hl : fr.ops.length = S.ar t := by simpa [TightTop, hc] using htight
      exact umatched_suspend S hS hok hT hc hY htag h hl
    | _ => simp [CalmTop, hc] at hcalm

/-- **The backward simulation step on the tight fragment.** -/
theorem umatched_rel_tight (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) : UMatched S W c (sstep W i32Test x) := by
  obtain ⟨hs, hf₀, hK, st, hstk, hmain, hcode⟩ := hR
  have hc : c = ⟨S.s, c.conts, S.f0, (stkCtx S st).plug []⟩ := by
    rw [← hs, ← hf₀, ← hcode]
  have hf : fine W x = true := fine_of_supported hsup.1
  have htight : tightCfg x = true := hsup.2 0 x rfl
  match st, hmain, hstk with
  | [], hm, _ =>
    obtain ⟨init, last, heq, -⟩ := hm.2.2
    exact absurd heq.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | (fr, a) :: rs, hm, hstk =>
    have hx : x = ⟨x.conts, fr :: rs.map Prod.fst⟩ := by
      rw [← List.map_cons (f := Prod.fst) (a := (fr, a)), ← hstk]
    have hf' : fine W ⟨x.conts, fr :: rs.map Prod.fst⟩ = true := hx ▸ hf
    have ht' : TightTop fr = true := by
      rw [hx] at htight
      simpa [tightCfg] using htight
    obtain ⟨hnt, htop⟩ := fine_cons hf'
    rw [hc, hx]
    exact umatched_top_tight S hS hP hH hok ⟨hm, hK, hnt, htop⟩ ht'

/-- The hypotheses of the backward argument, on the tight fragment. -/
theorem backHyp_tight (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) : BackHyp S W (TightSupported W) where
  next _ _ h hs := tightSupported_next h hs
  matched _ _ hR hsup := umatched_rel_tight S (sx_eq S hP hH) hP hH hok hR hsup
  stuck c d ws hc h := by
    rw [sx_eq S hP hH] at h
    exact Silmaril.Proofs.Wasm.Models.FXVRuns.no_step_fvals' h (liftV ws)
      (by rw [hc, Silmaril.Proofs.Wasm.Models.FXAsyncBack.liftV_fvals])

/-- **Every `StepFX'` behaviour is a kernel behaviour** (tight fragment, `suspend` included). -/
theorem fx_in_kernel_tight (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    ∀ b ∈ behavioursFX' S.P S.host S.fx c, ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = b :=
  fx_sub_kernel (backHyp_tight S hP hH hok) hR hsup

/-- **The `StepFX'` behaviours are exactly the images of the kernel's** (tight fragment). -/
theorem beh_eq_tight (hP : S.P = Profile.deterministic o) (hH : S.host = noHost)
    (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    behavioursFX' S.P S.host S.fx c = obsB '' beh (sstep W i32Test) x := by
  ext b
  constructor
  · intro hb
    obtain ⟨ob, hob, rfl⟩ := fx_in_kernel_tight S hP hH hok hR hsup b hb
    exact ⟨ob, hob, rfl⟩
  · rintro ⟨ob, hob, rfl⟩
    exact Silmaril.Proofs.Wasm.Models.FXAsyncFX.beh_in_fx S hok hR hsup.1 ob hob

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
