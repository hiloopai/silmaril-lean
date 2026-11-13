module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Sim
public import Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Obs
public import Silmaril.Wasm.FX.Asyncify.Tool.Thms

/-!
# The tool in the kernel: the simulation assembled, and the behaviours

* `bridge_sim`: `BR` is a stuttering simulation (by the shape of the tool's top frame);
* `init_run`: two kernel steps from `sInit` (the call, `enterOp`) reach a configuration
  related to the tool's initial one;
* `src_beh_kernel`: **the tool's source behaviours are the translated kernel's**, host states
  observed, read back by `obsOut`;
* `straight_of_wf`: well-formed (statement-form) programs have no `return` and no `if`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm
open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Wasm.FX.Asyncify.Bridge

variable {σ : Type} (E : Tool.Env) (H : Tool.Host σ)

/-- The instructions the translation simulates: straight-line ones and calls. -/
theorem ctl_cases {i : Instr} (h : ctlNC i = true) : Tool.ctlOf i = none ∨ ∃ f, i = .call f := by
  unfold Tool.ctlOf
  split
  · exact .inr ⟨_, rfl⟩
  · simp only [ctlNC, Bool.false_eq_true] at h
  · simp only [ctlNC, Bool.false_eq_true] at h
  · exact .inl rfl

/-- The one-step obligation at a call. -/
theorem ok_call (hE : Straight E) (K : List (Option (List (SFrame KV)))) (s : σ) (fid : Nat)
    (ls ops : List Tool.W) (f : FuncIdx) (code : List Instr) (nres : Nat) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (g : List Tool.W) (m : Nat → Tool.W)
    (hw : List.Forall₂ (WaitF E) rest bs) (hc : NoCtl (.call f :: code))
    (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, .call f :: code, nres⟩ :: rest, g, m⟩
        ⟨fid, ls, ops, .call f :: code, nres⟩ :: (bs ++ [root])⟩, s) := by
  by_cases hf : f.value.val < E.imps.length
  · by_cases hn : (E.imps[f.value.val]'hf).1 ≤ ops.length
    · exact sim_imp E H K s fid ls ops nres g m f code rest bs hf hn hw hc hr
    · exact sim_imp_trap E H K s fid ls ops nres g m f code rest bs hf hn
  · cases hfn : E.fns[f.value.val - E.imps.length]? with
    | none => exact sim_fn_none E H K s fid ls ops nres g m f code rest bs hf hfn
    | some fn =>
      by_cases hn : fn.nparams ≤ ops.length
      · exact sim_fn E H K s fid ls ops nres g m hE f code rest bs hf hfn hn hw hc hr
      · exact sim_fn_trap E H K s fid ls ops nres g m f code rest bs hf hfn hn

/-- The one-step obligation, by the shape of the top frame. -/
theorem ok_of_shape (hE : Straight E) (K : List (Option (List (SFrame KV)))) (s : σ) (fid : Nat)
    (ls ops : List Tool.W) (code : List Instr) (nres : Nat) (rest : List Tool.Frame)
    (bs : List (SFrame KV)) (g : List Tool.W) (m : Nat → Tool.W)
    (hw : List.Forall₂ (WaitF E) rest bs) (hc : NoCtl code) (hr : ∀ fr ∈ rest, NoCtl fr.code) :
    Ok E H (⟨⟨fid, ls, ops, code, nres⟩ :: rest, g, m⟩, s)
      (⟨K, topF E ⟨⟨fid, ls, ops, code, nres⟩ :: rest, g, m⟩ ⟨fid, ls, ops, code, nres⟩ ::
        (bs ++ [root])⟩, s) := by
  cases code with
  | nil =>
    cases hw with
    | nil => exact sim_done E H K s fid ls ops nres g m
    | cons hb hw' =>
      exact sim_ret E H K s fid ls ops nres g m _ _ _ _ hb hw' (hr _ (List.mem_cons_self ..))
        (fun fr h => hr fr (List.mem_cons_of_mem _ h))
  | cons i code =>
    rcases ctl_cases (hc i (List.mem_cons_self ..)) with hctl | ⟨f, hf⟩
    · cases hseg : Tool.segCore i ⟨ls, ops, g, m⟩ with
      | some v' => exact sim_seg E H K s fid ls ops nres g m i code rest bs hctl v' hseg hw hc hr
      | none => exact sim_seg_trap E H K s fid ls ops nres g m i code rest bs hctl hseg
    · exact hf ▸ ok_call E H hE K s fid ls ops f code nres rest bs g m hw (hf ▸ hc) hr

/-- **The tool's source system is simulated by the translated kernel**, host states observed. -/
theorem bridge_sim (hE : Straight E) : SimRel (src E H) (tgt E H) (BR E) := by
  rintro ⟨⟨frames, g, m⟩, s⟩ ⟨⟨K, stk⟩, s'⟩ ⟨hs, ⟨fid, ls, ops, code, nres⟩, rest, bs, hfr, hstk, hw,
    hc, hr⟩
  simp only at hs hfr hstk
  subst hs hfr hstk
  exact ok_of_shape E H hE K s fid ls ops code nres rest bs g m hw hc hr

theorem tgt_call1 {g : Nat} {body : List (Ins KV)} (h : trP E g = some (1, body))
    (K : List (Option (List (SFrame KV)))) (s : σ) (c : List (Ins KV)) (a : KV)
    (L : List (SFrame KV)) :
    tgt E H (⟨K, ⟨.call g :: c, [.val a], none⟩ :: L⟩, s) =
      .next (⟨K, ⟨body, [.val a], none⟩ :: ⟨c, [], none⟩ :: L⟩, s) := by
  simp [tgt, mapObs, kSrc, observe, hsstep, blockedOn, sstep, sexec, scall, popN, h, Res.map]

/-- The tool's initial configuration of a call of defined function `e`. -/
def cfg0 (e : Nat) (fn : Tool.FnDef) (args : List Tool.W) : Tool.Cfg :=
  ⟨[Tool.entry e fn args], [], fun _ => 0⟩

/-- The kernel configuration two steps after `sInit`. -/
def kcfg1 (e : Nat) (fn : Tool.FnDef) (args : List Tool.W) : SCfg KV :=
  ⟨[], topF E (cfg0 e fn args) (Tool.entry e fn args) :: ([] ++ [root])⟩

theorem init_run {e : Nat} {fn : Tool.FnDef} (he : E.imps.length ≤ e)
    (hfn : E.fns[e - E.imps.length]? = some fn) (args : List Tool.W) (s : σ) :
    runN (tgt E H) 2 (sInit e (kArgs args), s) = .next (kcfg1 E e fn args, s) :=
  runN_two (tgt_call1 E H (trP_some E (Nat.not_lt_of_le he) hfn) [] s [] _ [])
    (tgt_prim1 E H [] s _ _ _ _)

theorem init_rel {e : Nat} {fn : Tool.FnDef} (hE : Straight E) (hmem : fn ∈ E.fns)
    (args : List Tool.W) (s : σ) : BR E (cfg0 e fn args, s) (kcfg1 E e fn args, s) :=
  ⟨rfl, Tool.entry e fn args, [], [], rfl, rfl, .nil, hE fn hmem, fun _ h => by cases h⟩

/-- Two continuing steps do not change the behaviours. -/
theorem beh_runN_two {C V : Type} {step : C → Res C V} {c c' : C} (h : runN step 2 c = .next c') :
    beh step c = beh step c' := by
  cases h1 : step c with
  | stop o => simp only [runN, h1] at h; cases h
  | next c₁ =>
    have h2 : step c₁ = .next c' := by
      have h' : runN step 1 c₁ = .next c' := by simpa only [runN, h1] using h
      cases h3 : step c₁ with
      | next c₂ => simp only [runN, h3] at h'; rw [h']
      | stop o => simp only [runN, h3] at h'; cases h'
    rw [beh_next_eq h1, beh_next_eq h2]

/-- **The tool's source behaviours are the translated kernel's**, host states observed. -/
theorem src_beh_kernel (hE : Straight E) {e : Nat} {fn : Tool.FnDef} (he : E.imps.length ≤ e)
    (hfn : E.fns[e - E.imps.length]? = some fn) (args : List Tool.W) (s : σ) :
    Tool.beh (Tool.srcStep E H) (cfg0 e fn args, s) =
      obsOut '' hSrcObs (trP E) kTest (kHost E H) s e (kArgs args) := by
  have h1 : Tool.beh (Tool.srcStep E H) (cfg0 e fn args, s) =
      backObs '' beh (src E H) (cfg0 e fn args, s) := tool_beh_asRes _ _
  have h2 : beh (src E H) (cfg0 e fn args, s) = beh (tgt E H) (kcfg1 E e fn args, s) :=
    beh_eq_of_simRel (bridge_sim E H hE) (init_rel E hE (List.mem_of_getElem? hfn) args s)
  have h3 : beh (tgt E H) (sInit e (kArgs args), s) = beh (tgt E H) (kcfg1 E e fn args, s) :=
    beh_runN_two (init_run E H he hfn args s)
  have h4 : beh (tgt E H) (sInit e (kArgs args), s) =
      Obs.mapV toolOut '' hSrcObs (trP E) kTest (kHost E H) s e (kArgs args) :=
    beh_mapObs _ _ _
  have h5 : obsOut = fun b : Obs (HOut KV σ) => backObs (Obs.mapV toolOut b) :=
    funext obsOut_eq
  rw [h1, h2, ← h3, h4, Set.image_image, h5]

/-! ## Statement-form programs are straight -/

theorem ctlNC_of_pure {S : Nat} {i : Instr} (h : Tool.pureIns S i = true) : ctlNC i = true := by
  cases Tool.pureShape h <;> rfl

theorem noCtl_append {a b : List Instr} (ha : NoCtl a) (hb : NoCtl b) : NoCtl (a ++ b) :=
  fun i hi => (List.mem_append.mp hi).elim (ha i) (hb i)

theorem noCtl_stmt {P : Tool.Prog} {S : Nat} {st : Tool.Stmt} (h : st.wf P S = true) :
    NoCtl st.code := by
  cases st with
  | pure is => exact fun i hi => ctlNC_of_pure ((Tool.Stmt.wf_pure h).2.1 i hi)
  | call f as rs =>
    intro i hi
    have hi' : i ∈ as.map Instr.localGet ∨ i = .call f ∨ i ∈ rs.reverse.map Instr.localSet := by
      simpa only [Tool.Stmt.code, Tool.getsCode, Tool.setsCode, List.mem_append,
        List.mem_singleton, or_assoc] using hi
    rcases hi' with hi' | rfl | hi'
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hi'
      rfl
    · rfl
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hi'
      rfl

theorem noCtl_flatS {P : Tool.Prog} {S : Nat} :
    ∀ {ss : List Tool.Stmt}, (∀ st ∈ ss, st.wf P S = true) → NoCtl (Tool.flatS ss)
  | [], _ => fun _ h => by cases h
  | st :: ss, h =>
    noCtl_append (noCtl_stmt (h st (List.mem_cons_self ..)))
      (noCtl_flatS fun st' h' => h st' (List.mem_cons_of_mem _ h'))

/-- **Well-formed programs are straight.** -/
theorem straight_of_wf {P : Tool.Prog} (hP : P.WF) : Straight P.env := by
  intro fd hfd
  obtain ⟨fn, hmem, rfl⟩ := List.mem_map.mp hfd
  have hwf : fn.wf P = true := Tool.Prog.wf_fns hP hmem
  have hparts : (∀ st ∈ fn.stmts, st.wf P fn.nloc = true) ∧ ∀ i ∈ fn.tail, Tool.pureIns fn.nloc i = true := by
    simp only [Tool.FnSrc.wf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hwf
    exact ⟨hwf.1.1.1, hwf.1.1.2⟩
  exact noCtl_append (noCtl_flatS hparts.1) fun i hi => ctlNC_of_pure (hparts.2 i hi)

end Silmaril.Proofs.Wasm.FX.Asyncify.Bridge
