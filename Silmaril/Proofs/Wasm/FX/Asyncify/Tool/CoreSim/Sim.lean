module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Call

/-!
# Every step of the bounded machine in `CRel` is matched by Core 3.0

`crel_step`: from `CRel`, the result of `stepB` is matched (`CMatch`): a next configuration by
Core steps back into `CRel`, a return of the bottom frame by Core steps to the same values, a
trap by Core steps to a trap; an import call does not happen. By instruction: the checker's
`InsOk` constructors (`ins_case`), `return`, `if`, and the end of the body.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {mi : ModuleInst} {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame}
  {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} {rest : List CFr}
  {i : Instr} {code : List Instr} {a a' : List Bool}

/-- The cases of the checker on a non-empty code. -/
theorem ck_cons_inv {X : CkCtx} {Q : List Bool → Prop} (h : Ck X Q (i :: code) a) :
    (i = .return_ ∧ X.nres ≤ a.length) ∨ (∃ a', InsOk X i a a' ∧ Ck X Q code a') ∨
      (∃ t e b a₀, i = .if_ .empty t e ∧ a = b :: a₀ ∧ Ck X (· = []) t [] ∧
        Ck X (· = []) e [] ∧ Ck X Q code a₀) := by
  cases h with
  | ret hn => exact .inl ⟨rfl, hn⟩
  | ins hi hc => exact .inr (.inl ⟨_, hi, hc⟩)
  | ifE ht he hc => exact .inr (.inr ⟨_, _, _, _, rfl, rfl, ht, he, hc⟩)

theorem top_absOk (hT : Top cap E mi c s fr frs fs rest) : AbsOk fs.l0.abs fs.l0.ops :=
  hT.2.2.2.1.1

/-- A straight-line instruction that is not a memory access. -/
theorem seg_go (hT : Top cap E mi c s fr frs fs rest) (h0 : fs.l0.code = i :: code)
    (hctl : ctlOf i = none) (hacc : ∀ o, accessAt i o = none)
    (hS : SegStep Pf host cap E mi s fs.locals fs.l0.ops c.globals c.mem i a' (expression code))
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code a') :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) :=
  seg_next hT h0 hctl (not_oob hT.1 (fr_code hT.2.1 h0) (hacc _)) hS hck

/-- One operand on level 0. -/
theorem ops1 (hT : Top cap E mi c s fr frs fs rest) {b : Bool} (habs : fs.l0.abs = b :: a) :
    ∃ w ops', fs.l0.ops = w :: ops' ∧ (b = true → w.toNat % 4 = 0) ∧ AbsOk a ops' :=
  absOk_cons_inv (habs ▸ top_absOk hT)

/-- Two operands on level 0. -/
theorem ops2 (hT : Top cap E mi c s fr frs fs rest) {b₁ b₂ : Bool}
    (habs : fs.l0.abs = b₁ :: b₂ :: a) :
    ∃ w₁ w₂ ops', fs.l0.ops = w₁ :: w₂ :: ops' ∧ (b₁ = true → w₁.toNat % 4 = 0) ∧
      (b₂ = true → w₂.toNat % 4 = 0) ∧ AbsOk a ops' := by
  obtain ⟨w₁, o₁, h₁, hw₁, ha₁⟩ := ops1 hT habs
  obtain ⟨w₂, o₂, h₂, hw₂, ha₂⟩ := absOk_cons_inv ha₁
  exact ⟨w₁, w₂, o₂, by rw [h₁, h₂], hw₁, hw₂, ha₂⟩

theorem bin_case (hT : Top cap E mi c s fr frs fs rest) {op : IntBinOp} {fy fx : Bool}
    (h0 : fs.l0.code = .intBinOp .i32 op :: code) (habs : fs.l0.abs = fy :: fx :: a)
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code (binAl op fx fy :: a)) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  obtain ⟨y, x, ops', hops, hy, hx, ha⟩ := ops2 hT habs
  have hoob := not_oob (cap := cap) hT.1 (fr_code hT.2.1 h0) (by simp [accessAt])
  cases hr : Numerics.intBinOp .i32 op x y with
  | ok r =>
    exact seg_next hT h0 rfl hoob
      (by rw [hops]; exact seg_bin _ op y x hr hy hx (top_sinv hT) ha) hck
  | error e =>
    obtain ⟨hn, hc⟩ := bin_trap (Pf := Pf) (host := host) (s := s) (mi := mi)
      (ls := fs.locals) (ops := ops') (gs := c.globals) (mem := c.mem) (expression code) op y x hr
      (fs.ls.flatMap Lvl.ops)
    exact seg_trapped hT h0 rfl hoob (by rw [hops]; exact hn) (by rw [hops]; exact hc)

theorem load_case (hT : Top cap E mi c s fr frs fs rest) {arg : MemArg}
    (h0 : fs.l0.code = .intLoad .i32 none ⟨0⟩ arg :: code) (habs : fs.l0.abs = true :: a)
    (hoff : arg.offset.val % 4 = 0) (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code (false :: a)) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  obtain ⟨x, ops', hops, hx, ha⟩ := ops1 hT habs
  have hacc : access c = some (x.toNat + arg.offset.val) := by
    rw [access_l0 hT h0, hops]; rfl
  by_cases hoob : OOB cap c
  · have hcap : cap < x.toNat + arg.offset.val + 4 := by
      obtain ⟨a₁, h₁, h₂⟩ := hoob
      rw [hacc] at h₁; cases h₁; exact h₂
    exact oob_trapped h0 hoob (by rw [hops]; exact load_oob _ x hcap (top_sinv hT))
  · have hcap : x.toNat + arg.offset.val + 4 ≤ cap :=
      Nat.le_of_not_lt fun h => hoob ⟨_, hacc, h⟩
    exact seg_next hT h0 rfl hoob
      (by rw [hops]; exact seg_load _ x (hx rfl) hoff hcap (top_sinv hT) ha) hck

theorem store_case (hT : Top cap E mi c s fr frs fs rest) {arg : MemArg} {b : Bool}
    (h0 : fs.l0.code = .intStore .i32 none ⟨0⟩ arg :: code) (habs : fs.l0.abs = b :: true :: a)
    (hoff : arg.offset.val % 4 = 0) (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code a) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  obtain ⟨v, x, ops', hops, -, hx, ha⟩ := ops2 hT habs
  have hacc : access c = some (x.toNat + arg.offset.val) := by
    rw [access_l0 hT h0, hops]; rfl
  by_cases hoob : OOB cap c
  · have hcap : cap < x.toNat + arg.offset.val + 4 := by
      obtain ⟨a₁, h₁, h₂⟩ := hoob
      rw [hacc] at h₁; cases h₁; exact h₂
    exact oob_trapped h0 hoob (by rw [hops]; exact store_oob _ v x hcap (top_sinv hT))
  · have hcap : x.toNat + arg.offset.val + 4 ≤ cap :=
      Nat.le_of_not_lt fun h => hoob ⟨_, hacc, h⟩
    exact seg_next hT h0 rfl hoob
      (by rw [hops]; exact seg_store _ v x (hx rfl) hoff hcap (top_sinv hT) ha) hck

/-- **A non-branching instruction accepted by the checker.** -/
theorem ins_case (hT : Top cap E mi c s fr frs fs rest) (h0 : fs.l0.code = i :: code)
    (habs : fs.l0.abs = a) (hI : InsOk (fs.ctx E) i a a')
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code a') :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hS : SInv cap E mi s c.globals c.mem := top_sinv hT
  cases hI with
  | nop => exact seg_go hT h0 rfl (fun _ => rfl) (seg_nop _ hS (habs ▸ top_absOk hT)) hck
  | drop =>
    obtain ⟨w, o, hops, -, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_drop _ w hS ha) hck
  | get hi => exact seg_go hT h0 rfl (fun _ => rfl) (seg_get _ hi hS (habs ▸ top_absOk hT)) hck
  | set hi =>
    obtain ⟨w, o, hops, -, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_set _ hi w hS ha) hck
  | tee hi =>
    obtain ⟨w, o, hops, -, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_tee _ hi w hS ha) hck
  | const => exact seg_go hT h0 rfl (fun _ => rfl) (seg_const _ _ hS (habs ▸ top_absOk hT)) hck
  | un =>
    obtain ⟨w, o, hops, -, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_un _ _ w hS ha) hck
  | bin => exact bin_case hT h0 habs hck
  | test =>
    obtain ⟨w, o, hops, -, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_test _ _ w hS ha) hck
  | rel =>
    obtain ⟨y, x, o, hops, -, -, ha⟩ := ops2 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_rel _ _ y x hS ha) hck
  | gget hg => exact seg_go hT h0 rfl (fun _ => rfl) (seg_gget _ hg hS (habs ▸ top_absOk hT)) hck
  | gset hg hb =>
    obtain ⟨w, o, hops, hw, ha⟩ := ops1 hT habs
    exact seg_go hT h0 rfl (fun _ => rfl) (by rw [hops]; exact seg_gset _ hg hb w hw hS ha) hck
  | load hoff => exact load_case hT h0 habs hoff hck
  | store hoff => exact store_case hT h0 habs hoff hck
  | call hf hfn hn => exact call_case hT h0 hf hfn (habs ▸ hn) (habs ▸ hck)

/-- **The top frame, normalized, against Core.** -/
theorem top_match (hT : Top cap E mi c s fr frs fs rest) (hn : fs.l0.code = [] → fs.ls = []) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  match h0 : fs.l0.code with
  | [] => exact end_case hT h0 (hn h0)
  | i :: code =>
    have hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) (i :: code) fs.l0.abs := h0 ▸ hT.2.2.2.1.2.1
    rcases ck_cons_inv hck with ⟨hi, hr⟩ | ⟨a', hI, hc⟩ | ⟨t, e, b, a₀, hi, ha, ht, he, hc⟩
    · exact return_case hT (hi ▸ h0) hr
    · exact ins_case hT h0 rfl hI hc
    · exact if_case hT (hi ▸ h0) ha ht he hc

/-- **Every step of the bounded machine in `CRel` is matched by Core 3.0.** -/
theorem crel_step {Z : List Admin} (h : CRel cap E mi c s Z) :
    CMatch Pf host cap E mi s Z (stepB cap E c) := by
  obtain ⟨fr, frs, fs, rest, hT, rfl⟩ := crel_top h
  obtain ⟨fs', hT', hn, hsteps⟩ := normalize_aux fs.ls fs rfl hT
  exact cmatch_pre hsteps (top_match hT' hn)

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
