module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Seg

/-!
# The top frame of `CRel`, and the control steps

`Top` exposes the top frame of `CRel`. Empty innermost arms are closed in Core without a machine
step (`normalize`). Then each kind of machine step is matched (`CMatch`): leaving a frame
(`ret_case`, used by `end_case` and `return_case`), `if` (`if_case`), calls (`call_case`) and
straight-line instructions (`seg_next`, `seg_trapped`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {mi : ModuleInst}

local notation "Steps" => Execution.Core.Steps Pf host

/-- `CRel` with the top frame exposed. -/
def Top (cap : Nat) (E : Env) (mi : ModuleInst) (c : Cfg) (s : Store H) (fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame)
    (frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame) (fs : CFr) (rest : List CFr) : Prop :=
  c.frames = fr :: frs ∧ FrRel fr fs ∧ List.Forall₂ FrRel frs rest ∧ fs.Ok E [] ∧
    Waits E fs.nres rest ∧ SInv cap E mi s c.globals c.mem ∧ EnvOk E

theorem crel_top {c : Cfg} {s : Store H} {Z : List Admin} (h : CRel cap E mi c s Z) :
    ∃ fr frs fs rest, Top cap E mi c s fr frs fs rest ∧ Z = stackC mi (fs :: rest) [] := by
  obtain ⟨fss, hF, hS, hZ, hH, hG, hM, hGI, hE⟩ := h
  match fss, hF, hS with
  | fs :: rest, hF, ⟨hok, hw⟩ =>
    obtain ⟨fr, frs, hfr, hfrs, hc⟩ := List.forall₂_cons_right_iff.1 hF
    exact ⟨fr, frs, fs, rest, ⟨hc, hfr, hfrs, hok, hw, ⟨hH, hG, hM, hGI⟩, hE⟩, hZ⟩

theorem top_crel {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr}
    {rest : List CFr} (h : Top cap E mi c s fr frs fs rest) :
    CRel cap E mi c s (stackC mi (fs :: rest) []) :=
  ⟨fs :: rest, by rw [h.1]; exact .cons h.2.1 h.2.2.1, ⟨h.2.2.2.1, h.2.2.2.2.1⟩, rfl,
    h.2.2.2.2.2.1.1, h.2.2.2.2.2.1.2.1, h.2.2.2.2.2.1.2.2.1, h.2.2.2.2.2.1.2.2.2, h.2.2.2.2.2.2⟩

theorem cmatch_pre {s : Store H} {Z Z₁ : List Admin} {r : Res}
    (h : Steps ⟨s, ⟨[], mi⟩, Z⟩ ⟨s, ⟨[], mi⟩, Z₁⟩) (hm : CMatch Pf host cap E mi s Z₁ r) :
    CMatch Pf host cap E mi s Z r := by
  cases r with
  | next c' => obtain ⟨s', Z', h', hR⟩ := hm; exact ⟨s', Z', h.trans h', hR⟩
  | done vs c' => obtain ⟨s', h', hrest⟩ := hm; exact ⟨s', h.trans h', hrest⟩
  | trap => obtain ⟨C', h', hc⟩ := hm; exact ⟨C', h.trans h', hc⟩
  | ask => exact hm.elim

theorem admin_nil (fs : CFr) :
    fs.admin mi [] =
      frameA mi fs.nres fs.locals (wrapL (stackA fs.l0.ops ++ expression fs.l0.code) fs.ls) := by
  simp only [CFr.admin, List.append_nil]

theorem stackC_cons (fs : CFr) (rest : List CFr) :
    stackC mi (fs :: rest) [] = stackC mi rest [fs.admin mi []] := rfl

theorem stackA_append (vs ops : List W) : stackA (vs ++ ops) = stackA ops ++ stackA vs := by
  simp only [stackA, List.reverse_append, List.map_append, vals_append]

/-! ## Closing empty arms -/

theorem ck_nil_inv {X : CkCtx} {Q : List Bool → Prop} {a : List Bool} (h : Ck X Q [] a) : Q a := by
  cases h with
  | nil hq => exact hq

theorem norm_once {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr}
    {rest : List CFr} {l : Lvl} {ls : List Lvl} (hT : Top cap E mi c s fr frs fs rest)
    (h0 : fs.l0.code = []) (hls : fs.ls = l :: ls) :
    Top cap E mi c s fr frs ⟨fs.locals, fs.nres, l, ls⟩ rest ∧
      Steps ⟨s, ⟨[], mi⟩, stackC mi (fs :: rest) []⟩
        ⟨s, ⟨[], mi⟩, stackC mi (⟨fs.locals, fs.nres, l, ls⟩ :: rest) []⟩ := by
  obtain ⟨hc, ⟨hl, hn, hops, hcode⟩, hfrs, ⟨hab, hck, hlv⟩, hw, hI, hE⟩ := hT
  have ha : fs.l0.abs = [] := by
    have hq := ck_nil_inv (h0 ▸ hck)
    rw [hls] at hq
    exact hq
  have hop : fs.l0.ops = [] :=
    List.eq_nil_of_length_eq_zero ((absOk_length hab).symm.trans (by rw [ha]; rfl))
  rw [hls] at hlv
  refine ⟨⟨hc, ⟨hl, hn, ?_, ?_⟩, hfrs, ⟨hlv.1, hlv.2.1, hlv.2.2⟩, hw, hI, hE⟩, ?_⟩
  · rw [hops]; simp only [CFr.ops, hop, hls, List.nil_append, List.flatMap_cons]
  · rw [hcode]; simp only [CFr.code, h0, hls, List.nil_append, List.flatMap_cons]
  · rw [stackC_cons, stackC_cons, admin_nil, admin_nil, hop, h0, hls]
    exact steps_stackC rest (steps_frameA (pop_level l ls)) _

theorem normalize_aux {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {rest : List CFr} :
    ∀ (ls : List Lvl) (fs : CFr), fs.ls = ls → Top cap E mi c s fr frs fs rest →
      ∃ fs', Top cap E mi c s fr frs fs' rest ∧ (fs'.l0.code = [] → fs'.ls = []) ∧
        Steps ⟨s, ⟨[], mi⟩, stackC mi (fs :: rest) []⟩ ⟨s, ⟨[], mi⟩, stackC mi (fs' :: rest) []⟩
  | [], fs, hls, hT => ⟨fs, hT, fun _ => hls, .refl⟩
  | l :: ls, fs, hls, hT => by
    by_cases h0 : fs.l0.code = []
    · obtain ⟨hT', h1⟩ := norm_once hT h0 hls
      obtain ⟨fs', hT'', hn, h2⟩ := normalize_aux ls _ rfl hT'
      exact ⟨fs', hT'', hn, h1.trans h2⟩
    · exact ⟨fs, hT, fun h => absurd h h0, .refl⟩

/-! ## Leaving a frame -/

theorem steps_admin {s s' : Store H} (fs : CFr) {X X' : List Admin}
    (h : ∀ f, Steps ⟨s, f, X⟩ ⟨s', f, X'⟩) (f : Silmaril.Wasm.Execution.Core.Frame) :
    Steps ⟨s, f, [fs.admin mi X]⟩ ⟨s', f, [fs.admin mi X']⟩ :=
  steps_stackC [fs] h f

/-- The frame below after the callee returned `vs`. -/
def pushFr (fs : CFr) (vs : List W) (k : Nat) : CFr :=
  { fs with l0 := ⟨vs ++ fs.l0.ops, List.replicate k false ++ fs.l0.abs, fs.l0.code⟩ }

theorem admin_push (fs : CFr) (vs : List W) (k : Nat) :
    (pushFr fs vs k).admin mi [] = fs.admin mi (stackA vs) := by
  simp only [pushFr, CFr.admin, List.append_nil, stackA_append]

theorem push_ok {fs : CFr} {vs : List W} {k : Nat} (hk : vs.length = k)
    (h : fs.Ok E (List.replicate k false)) : (pushFr fs vs k).Ok E [] :=
  ⟨by rw [← hk]; exact absOk_replicate h.1, h.2.1, h.2.2⟩

theorem push_rel {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} (vs : List W) (k : Nat) (h : FrRel fr fs) :
    FrRel { fr with ops := vs ++ fr.ops } (pushFr fs vs k) :=
  ⟨h.1, h.2.1, by rw [h.2.2.1]; simp only [CFr.ops, pushFr, List.append_assoc], h.2.2.2⟩

/-- The top frame returns `vs`. -/
theorem ret_case {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr}
    {rest : List CFr} (hT : Top cap E mi c s fr frs fs rest) (vs : List W)
    (hvs : vs.length = fs.nres) (hcore : ∀ f, Steps ⟨s, f, [fs.admin mi []]⟩ ⟨s, f, stackA vs⟩) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (ret c vs frs) := by
  obtain ⟨hc, -, hfrs, -, hw, hI, hE⟩ := hT
  match frs, rest, hfrs, hw with
  | [], [], _, _ => exact ⟨s, hcore _, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2⟩
  | fr₁ :: frs', fs₁ :: rest', .cons hr₁ hrs, ⟨hok₁, hw'⟩ =>
    refine ⟨s, stackC mi (pushFr fs₁ vs fs.nres :: rest') [], ?_, ?_⟩
    · rw [stackC_cons, stackC_cons, admin_push]
      exact steps_stackC rest' (steps_admin fs₁ hcore) _
    · exact top_crel ⟨rfl, push_rel vs fs.nres hr₁, hrs, push_ok hvs hok₁, hw', hI, hE⟩

/-! ## Machine steps of the top frame -/

theorem step_top {c : Cfg} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {i : Instr} {code : List Instr}
    (E : Env) (hc : c.frames = fr :: frs) (hcode : fr.code = i :: code) :
    step E c = exec E c fr i code frs := by
  simp only [step, hc, hcode]

theorem access_top {c : Cfg} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {i : Instr} {code : List Instr}
    (hc : c.frames = fr :: frs) (hcode : fr.code = i :: code) : access c = accessAt i fr.ops := by
  simp only [access, hc, hcode]

theorem stepB_top {c : Cfg} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {i : Instr} {code : List Instr}
    (hc : c.frames = fr :: frs) (hcode : fr.code = i :: code) (hoob : ¬ OOB cap c) :
    stepB cap E c = exec E c fr i code frs := by
  rw [stepB, ite_eq_right_iff.2 (fun h => absurd h hoob), step_top E hc hcode]

theorem not_oob {c : Cfg} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {i : Instr} {code : List Instr}
    (hc : c.frames = fr :: frs) (hcode : fr.code = i :: code) (hacc : accessAt i fr.ops = none) :
    ¬ OOB cap c := fun ⟨_, h, _⟩ => by rw [access_top hc hcode, hacc] at h; cases h

theorem fr_code {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} {i : Instr} {code : List Instr} (h : FrRel fr fs)
    (h0 : fs.l0.code = i :: code) : fr.code = i :: (code ++ fs.ls.flatMap Lvl.code) := by
  rw [h.2.2.2, CFr.code, h0, List.cons_append]

theorem fr_ops {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} (h : FrRel fr fs) :
    fr.ops = fs.l0.ops ++ fs.ls.flatMap Lvl.ops := h.2.2.1

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
