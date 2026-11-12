module

public import Silmaril.Proofs.Machine.OfLambdaSSA.Root

/-!
# Both root shapes, both directions
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-- Forwards, for the blocks of a `cfg` evaluated on their own. -/
theorem follow_forward (hsigs : CallOracle.MatchesSigs oracle sigs) {fn : SSA.Func ℕ}
    {env : Semantics.Env Word} {k : ℕ} {blocks : Fin k → Region (Opcode sigs)} {first ℓ : ℕ}
    {initial v : Value Word} {m m' : Memory}
    (h : Semantics.Region.Follow (Opcode.step oracle) env blocks first initial m ℓ v m') :
    FolFwd oracle fn env blocks first initial m ℓ v m' := by
  induction h using Semantics.Region.Follow.rec
      (motive_1 := fun env r m ℓ v m' _ => RegFwd oracle fn env r m ℓ v m') with
  | br harg => exact regFwd_br hsigs harg
  | let₁ ha _ ih => exact regFwd_let₁ hsigs ha ih
  | let₂ ha _ ih => exact regFwd_let₂ hsigs ha ih
  | case_inl ha _ ih => exact regFwd_case_inl hsigs ha ih
  | case_inr ha _ ih => exact regFwd_case_inr hsigs ha ih
  | cfg _ _ ihE ihF => exact regFwd_cfg ihE ihF
  | exit outside => exact fwdF_exit outside
  | step inside _ _ ihH ihT => exact fwdF_step inside ihH ihT

/-- The context of the root: the function's argument, in its parameter registers. -/
theorem root_context {params : ℕ} {fr : Frame ℕ} {args : List Word} {env : Semantics.Env Word}
    (hfr : fr.readAll (freshRegs 0 params) = some args) (henv : env 0 = packValues args) :
    Agrees [.tuple params] [freshRegs 0 params] env fr ∧
      Below [.tuple params] [freshRegs 0 params] params ∧ EnvFits [.tuple params] env ∧
      args.length = params := by
  have hlen : args.length = params := by simpa using (readAll_length hfr).symm
  have hold : (Shape.tuple params).Holds (env 0) args := ⟨henv, hlen⟩
  refine ⟨fun i s hi => ?_, fun i s g hi hg x hx => ?_, fun i s hi => ?_, hlen⟩
  · match i, hi with
    | 0, hi =>
      obtain rfl : Shape.tuple params = s := by simpa using hi
      exact ⟨_, args, rfl, hfr, hold⟩
  · match i, hg with
    | 0, hg =>
      obtain rfl : freshRegs 0 params = g := by simpa using hg
      simpa using (mem_freshRegs.mp hx).2
  · match i, hi with
    | 0, hi =>
      obtain rfl : Shape.tuple params = s := by simpa using hi
      exact ⟨args, hold⟩

/-! ## A root compiled as block `0` -/

theorem plain_forward (hsigs : CallOracle.MatchesSigs oracle sigs) {r : Region (Opcode sigs)}
    {a : Ann} {params results : ℕ} (hfits : RegionFits sigs [.tuple params] r a [results, 0])
    {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hc : regionOps r a [freshRegs 0 params] (rootLabels results) (start params) = some (ops, t, e))
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} {ℓ : ℕ}
    {v : Value Word} (hev : Semantics.Region.Eval (Opcode.step oracle) env r m ℓ v m') :
    RootOutcome oracle (rootFn params results ops t e) fr m ℓ v m' := by
  obtain ⟨hag, hb, henvf, -⟩ := root_context hfr henv
  have hinst := inst_root (results := results) hc
  obtain ⟨w, vs, hw, rfl, hlen⟩ := region_sound hsigs hev hfits henvf
  have run := region_forward (fn := rootFn params results ops t e) (out := rootExit ℓ vs m') hsigs
    hev hfits rfl hc (hinst.sub (List.subset_cons_self _ _)) hag hb
    fun frX ws _ hv _ hlt => cont_root hv hlt
  exact outcome_of_exit ⟨w, vs, hw, rfl, hlen⟩ ((exec_iff_run (hinst _ List.mem_cons_self)).2 run)

theorem plain_backward {r : Region (Opcode sigs)} {a : Ann} {params results : ℕ}
    (hfits : RegionFits sigs [.tuple params] r a [results, 0]) {ops : List (Op ℕ)} {t : Term ℕ}
    {e : Emit}
    (hc : regionOps r a [freshRegs 0 params] (rootLabels results) (start params) = some (ops, t, e))
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m : Memory} {out : Exit}
    (hex : Func.Exec oracle (rootFn params results ops t e) 0 fr m out) :
    ∃ ℓ vs m', Semantics.Region.Eval (Opcode.step oracle) env r m ℓ (packValues vs) m' ∧
      ExitOk [results, 0] ℓ (packValues vs) ∧ out = rootExit ℓ vs m' := by
  obtain ⟨hag, hb, -, -⟩ := root_context hfr henv
  have hinst := inst_root (results := results) hc
  obtain ⟨N, hN⟩ := hex.toExecIn
  obtain ⟨N', -, run⟩ := run_of_budget (n := N + 1) (hinst _ List.mem_cons_self) hN
  obtain ⟨ℓ, v, m', frX, ws, hev, rfl, -, hl, hcont⟩ :=
    region_backward hfits N' rfl hc (hinst.sub (List.subset_cons_self _ _)) hag hb run
  refine ⟨ℓ, ws, m', hev, ?_, ?_⟩ <;> unfold Cont at hcont
  · match ℓ, hcont, hl with
    | 0, _, hl => exact ⟨results, ws, rfl, rfl, hl _ rfl⟩
    | 1, _, hl => exact ⟨0, ws, rfl, rfl, hl _ rfl⟩
  · match ℓ, hcont with
    | 0, hcont => exact hcont
    | 1, hcont => exact hcont

end Silmaril.Proofs.Machine.OfLambdaSSA

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-! ## The root wrapper, whose block is block `0` -/

theorem inner_one (w : ℕ) : inner 0 [w] 1 = [(.block 0, w)] := by
  simp [inner]

/-- The wrapper's one block is block `0`, compiled from the initial state. -/
theorem wrap_cfgInst {blocks : Fin 1 → Region (Opcode sigs)} {ab : Ann} {params results : ℕ}
    {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hc : regionOps (blocks 0) ab [freshRegs 0 params]
      (inner 0 [params] 1 ++ rootLabels results) (start params) = some (ops, t, e)) :
    CfgInst (rootFn params results ops t e) blocks [ab] [params] []
      (inner 0 [params] 1 ++ rootLabels results) 0 0 := by
  have hinst := inst_root (results := results) hc
  intro i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  refine ⟨⟨0, 1, []⟩, ops, t, e, le_rfl, ?_, hinst.sub (List.subset_cons_self _ _),
    hinst _ List.mem_cons_self⟩
  simpa [start] using hc

/-- The wrapper's block, checked as the block of a one-block `cfg`. -/
theorem wrap_fits {blocks : Fin 1 → Region (Opcode sigs)} {ab : Ann} {params results : ℕ}
    (hfits : RegionFits sigs [.tuple params] (blocks 0) ab [params, results, 0]) :
    ∀ i : Fin 1, RegionFits sigs (.tuple ([params].getD i 0) :: []) (blocks i) ([ab].getD i .br)
      ([params] ++ [results, 0]) := by
  intro i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact hfits

/-- Entering block `0` with the function's argument, from the function's own frame. -/
theorem wrap_entry {fn : SSA.Func ℕ} {E : Label → Frame ℕ → Memory → Exit → Prop} {params results : ℕ}
    {ops : List (Op ℕ)} {t : Term ℕ} (hbt : fn.block? 0 = some ⟨freshRegs 0 params, ops, t⟩)
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {m : Memory} {out : Exit} :
    Cont fn E (inner 0 [params] 1 ++ rootLabels results) 0 args fr m out ↔ E 0 fr m out := by
  unfold Cont
  rw [inner_one]
  constructor
  · rintro ⟨bt, fr', hbt', hw, hex⟩
    obtain rfl := Option.some.inj (hbt'.symm.trans hbt)
    obtain rfl := Option.some.inj (hw.symm.trans (writeAll_self hfr))
    exact hex
  · intro hex
    exact ⟨_, fr, hbt, writeAll_self hfr, hex⟩

theorem wrap_forward (hsigs : CallOracle.MatchesSigs oracle sigs)
    {blocks : Fin 1 → Region (Opcode sigs)} {ab : Ann} {params results : ℕ}
    (hfits : RegionFits sigs [.tuple params] (blocks 0) ab [params, results, 0])
    {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hc : regionOps (blocks 0) ab [freshRegs 0 params]
      (inner 0 [params] 1 ++ rootLabels results) (start params) = some (ops, t, e))
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} {ℓ : ℕ}
    {v : Value Word}
    (hev : Semantics.Region.Eval (Opcode.step oracle) env (.cfg (.br 0 (.var 0)) 1 blocks) m ℓ v m') :
    RootOutcome oracle (rootFn params results ops t e) fr m ℓ v m' := by
  obtain ⟨-, -, -, hlen⟩ := root_context hfr henv
  obtain ⟨first, initial, m₁, hentry, hfol⟩ := region_eval_cfg_inv hev
  obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
  obtain ⟨rfl, rfl⟩ := eval_var_inv harg
  have hinst := inst_root (results := results) hc
  have hok₀ : ExitOk ([params] ++ [results, 0]) 0 (env 0) := ⟨params, args, rfl, henv, hlen⟩
  obtain ⟨w, vs, hw, rfl, hlen'⟩ :=
    follow_sound hsigs hfol (wrap_fits hfits) rfl (fun _ _ h => by simp at h) hok₀
  have run := follow_forward (fn := rootFn params results ops t e) (out := rootExit ℓ vs m') hsigs
    hfol (wrap_fits hfits) rfl rfl (wrap_cfgInst hc) (fun _ _ h => by simp at h)
    (fun _ _ _ h => by simp at h) (fun frX ws _ hv _ hlt => cont_root hv hlt) fr args
    (Same.refl _ _) henv (by rw [inner_one]; intro p hp; simp at hp; rw [← hp]; exact hlen)
    (by simp)
  exact outcome_of_exit ⟨w, vs, hw, rfl, hlen'⟩
    ((wrap_entry (hinst _ List.mem_cons_self) hfr).1 run)

/-- A root exit, read off a continuation through the root labels. -/
theorem exit_of_cont {E : Label → Frame ℕ → Memory → Exit → Prop} {fn : SSA.Func ℕ} {results ℓ : ℕ}
    {ws : List Word} {frX : Frame ℕ} {m' : Memory} {out : Exit}
    (hl : ∀ p, (rootLabels results)[ℓ]? = some p → ws.length = p.2)
    (hcont : Cont fn E (rootLabels results) ℓ ws frX m' out) :
    ExitOk [results, 0] ℓ (packValues ws) ∧ out = rootExit ℓ ws m' := by
  unfold Cont at hcont
  match ℓ, hcont, hl with
  | 0, hcont, hl => exact ⟨⟨results, ws, rfl, rfl, hl _ rfl⟩, hcont⟩
  | 1, hcont, hl => exact ⟨⟨0, ws, rfl, rfl, hl _ rfl⟩, hcont⟩

theorem wrap_backward {blocks : Fin 1 → Region (Opcode sigs)} {ab : Ann} {params results : ℕ}
    (hfits : RegionFits sigs [.tuple params] (blocks 0) ab [params, results, 0])
    {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hc : regionOps (blocks 0) ab [freshRegs 0 params]
      (inner 0 [params] 1 ++ rootLabels results) (start params) = some (ops, t, e))
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m : Memory} {out : Exit}
    (hex : Func.Exec oracle (rootFn params results ops t e) 0 fr m out) :
    ∃ ℓ vs m', Semantics.Region.Eval (Opcode.step oracle) env (.cfg (.br 0 (.var 0)) 1 blocks) m ℓ
        (packValues vs) m' ∧ ExitOk [results, 0] ℓ (packValues vs) ∧ out = rootExit ℓ vs m' := by
  obtain ⟨-, -, -, hlen⟩ := root_context hfr henv
  have hinst := inst_root (results := results) hc
  obtain ⟨N, hN⟩ := hex.toExecIn
  have hcont := (wrap_entry (E := budget oracle _ (N + 1)) (results := results)
    (hinst _ List.mem_cons_self) hfr).2 hN
  obtain ⟨ℓ, v, m', frZ, ws, hfol, rfl, -, hl, hcontZ⟩ :=
    fol_backward (k := 1) (blocks := blocks) (Γ := []) rfl rfl (wrap_cfgInst hc) (fun _ _ h => by simp at h)
      (fun _ _ _ h => by simp at h)
      (fun i => region_backward (wrap_fits hfits i)) (N + 1) 0 args fr m out (Same.refl _ _)
      (by rw [inner_one]; intro p hp; simp at hp; rw [← hp]; exact hlen) hcont
  obtain ⟨hok, rfl⟩ := exit_of_cont hl hcontZ
  exact ⟨ℓ, ws, m', .cfg (.br (.var_of_eq henv)) hfol, hok, rfl⟩

end Silmaril.Proofs.Machine.OfLambdaSSA
