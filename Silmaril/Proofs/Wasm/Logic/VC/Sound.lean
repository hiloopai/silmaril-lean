module

public import Silmaril.Proofs.Wasm.Logic.VC.Rules
public import Silmaril.Wasm.Examples.Common.Thms

/-!
# Soundness of the verification-condition generator

`wpc_sound_ctx`: with a spec context `Γ` valid at `P` and `host`, `wpc inv k is Q s f vs`
implies `HWP P host s f (vals vs ++ expression is) Q`, for **every** family of loop invariants.
By well-founded recursion on the instruction list, one case per case of `wpc`, using the rules
of `Silmaril.Proofs.Wasm.Logic.VC.Rules` (`hwp_block`, `hwp_loop`, `wp_brTable`, `wp_cvt`,
`hwp_call`), `HWP.if_`, `HWP.brIf`, `Wp.br`, `Wp.selectTrue`/`False`, `Wp.of_exits` (for
`return`) and the symbolic-execution step `Common.Wp.exec1`. `wpc_sound`: the empty context,
at every profile and for every host relation.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp)

variable {H : Type} {P : Profile} {host : HostSemantics H}

section Cases

variable [Γ : VCSpecs H] {inv : Invs H} {k : Nat} {i : Instr} {r : List Instr} {Q : Post H} {s : Store H}
  {f : Frame} {vs : List Val}

/-! ### Unfolding `wpc` at each kind of instruction -/

theorem wpc_block {bt : BlockType} {b : List Instr} (hc : ctl i = .block bt b)
    (h : wpc inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args _ n₂ =>
      wpc inv k b (labelQ n₂ us (fun s f vs => wpc inv (k + loops b) r Q s f vs) Q) s f args := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_loop {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (h : wpc inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args n₁ _ => inv k s f args ∧
      ∀ s' f' a', inv k s' f' a' → f'.module = f.module → a'.length = n₁ →
        wpc inv (k + 1) b
          (loopQ n₁ us (fun s'' f'' a'' => inv k s'' f'' a'' ∧ f''.module = f.module)
            (fun s f vs => wpc inv (k + 1 + loops b) r Q s f vs) Q) s' f' a' := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_if {bt : BlockType} {b₁ b₂ : List Instr} (hc : ctl i = .if_ bt b₁ b₂)
    (h : wpc inv k (i :: r) Q s f vs) : ∃ us c, popI32 vs = some (us, c) ∧
      (c ≠ 0 → enterVC f bt us fun us' args _ n₂ => wpc inv k b₁
        (labelQ n₂ us' (fun s f vs => wpc inv (k + loops b₁ + loops b₂) r Q s f vs) Q) s f args) ∧
      (c = 0 → enterVC f bt us fun us' args _ n₂ => wpc inv (k + loops b₁) b₂
        (labelQ n₂ us' (fun s f vs => wpc inv (k + loops b₁ + loops b₂) r Q s f vs) Q) s f args) := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpc_br {l : LabelIdx} (hc : ctl i = .br l) (h : wpc inv k (i :: r) Q s f vs) :
    Q s f (.br l.toNat vs) := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_brIf {l : LabelIdx} (hc : ctl i = .brIf l) (h : wpc inv k (i :: r) Q s f vs) :
    ∃ us c, popI32 vs = some (us, c) ∧ (c ≠ 0 → Q s f (.br l.toNat us)) ∧
      (c = 0 → wpc inv k r Q s f us) := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpc_select (hc : ctl i = .select) (h : wpc inv k (i :: r) Q s f vs) :
    ∃ us v₁ v₂ c, popSelect vs = some (us, v₁, v₂, c) ∧
      (c ≠ 0 → wpc inv k r Q s f (us ++ [v₁])) ∧ (c = 0 → wpc inv k r Q s f (us ++ [v₂])) := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpc_ret (hc : ctl i = .ret) (h : wpc inv k (i :: r) Q s f vs) : Q s f (.ret vs) := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_trap (hc : ctl i = .trap) (h : wpc inv k (i :: r) Q s f vs) : Q s f .trap := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_brTable {ls : List LabelIdx} {d : LabelIdx} (hc : ctl i = .brTable ls d)
    (h : wpc inv k (i :: r) Q s f vs) :
    ∃ us c, popI32 vs = some (us, c) ∧ tableVC (fun l => Q s f (.br l.toNat us)) c.toNat 0 ls d := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpc_call {x : FuncIdx} (hc : ctl i = .call x) (h : wpc inv k (i :: r) Q s f vs) :
    callVC s f vs x (fun s' vs' => wpc inv k r Q s' f vs') Q := by
  rw [wpc] at h
  split at h <;> simp_all

theorem wpc_cvt {op : ConvertOp} (hc : ctl i = .cvt op) (h : wpc inv k (i :: r) Q s f vs) :
    ∃ vs', cvt1 op vs = some vs' ∧ wpc inv k r Q s f vs' := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpc_plain (hc : ctl i = .plain) (h : wpc inv k (i :: r) Q s f vs) :
    ∃ s' f' rs', Silmaril.Wasm.Logic.Core.exec1 s f vs.reverse i = some (s', f', rs') ∧
      wpc inv k r Q s' f' rs'.reverse := by
  rw [wpc] at h
  split at h <;> simp_all
  split at h <;> simp_all

/-! ### Each case, given soundness for the parts -/

theorem sound_block {bt : BlockType} {b : List Instr} (hc : ctl i = .block bt b)
    (ihb : ∀ Q s f vs, wpc inv k b Q s f vs → HWP P host s f (vals vs ++ expression b) Q)
    (ihr : ∀ s f vs, wpc inv (k + loops b) r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  rw [ctl_block hc]
  exact hwp_block ihr ((wpc_block hc h).mono fun _ args _ _ hb => ihb _ s f args hb)

theorem sound_loop {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (ihb : ∀ Q s f vs, wpc inv (k + 1) b Q s f vs → HWP P host s f (vals vs ++ expression b) Q)
    (ihr : ∀ s f vs, wpc inv (k + 1 + loops b) r Q s f vs →
      HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  rw [ctl_loop hc]
  exact hwp_loop (I := inv k) ihr ((wpc_loop hc h).mono fun _ _ _ _ hb =>
    ⟨hb.1, fun s' f' a' hi hm hl => ihb _ s' f' a' (hb.2 s' f' a' hi hm hl)⟩)

theorem sound_if {bt : BlockType} {b₁ b₂ : List Instr} (hc : ctl i = .if_ bt b₁ b₂)
    (ih₁ : ∀ Q s f vs, wpc inv k b₁ Q s f vs → HWP P host s f (vals vs ++ expression b₁) Q)
    (ih₂ : ∀ Q s f vs, wpc inv (k + loops b₁) b₂ Q s f vs →
      HWP P host s f (vals vs ++ expression b₂) Q)
    (ihr : ∀ s f vs, wpc inv (k + loops b₁ + loops b₂) r Q s f vs →
      HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨us, c, hp, h₁, h₂⟩ := wpc_if hc h
  rw [ctl_if hc, popI32_eq hp]
  exact HWP.if_ (fun hc₁ => hwp_block ihr ((h₁ hc₁).mono fun _ args _ _ hb => ih₁ _ s f args hb))
    (fun hc₂ => hwp_block ihr ((h₂ hc₂).mono fun _ args _ _ hb => ih₂ _ s f args hb))

theorem sound_brIf {l : LabelIdx} (hc : ctl i = .brIf l)
    (ihr : ∀ s f vs, wpc inv k r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨us, c, hp, h₁, h₂⟩ := wpc_brIf hc h
  rw [ctl_brIf hc, popI32_eq hp]
  exact HWP.brIf (fun hc₁ => Wp.br (m := .part) (h₁ hc₁)) (fun hc₂ => ihr s f us (h₂ hc₂))

theorem sound_select (hc : ctl i = .select)
    (ihr : ∀ s f vs, wpc inv k r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨ts, hi⟩ := ctl_select hc
  obtain ⟨us, v₁, v₂, c, hp, h₁, h₂⟩ := wpc_select hc h
  rw [hi, popSelect_eq hp]
  by_cases hc₀ : c = 0
  · rw [hc₀]
    exact Wp.selectFalse (m := .part) (ihr s f _ (h₂ hc₀))
  · exact Wp.selectTrue (m := .part) hc₀ (ihr s f _ (h₁ hc₀))

theorem sound_plain (hc : ctl i = .plain)
    (ihr : ∀ s f vs, wpc inv k r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨s', f', rs', he, hk⟩ := wpc_plain hc h
  have h₁ : Wp .part P host s f (vals vs.reverse.reverse ++ .plain i :: expression r) Q :=
    Silmaril.Wasm.Examples.Common.Wp.exec1 he (ihr s' f' rs'.reverse hk)
  simpa only [List.reverse_reverse, Silmaril.Wasm.Logic.Hoare.wp_part] using h₁

theorem sound_brTable {ls : List LabelIdx} {d : LabelIdx} (hc : ctl i = .brTable ls d)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨us, c, hp, ht⟩ := wpc_brTable hc h
  rw [ctl_brTable hc, popI32_eq hp]
  exact wp_brTable (m := .part) ht

theorem sound_cvt {op : ConvertOp} (hc : ctl i = .cvt op)
    (ihr : ∀ s f vs, wpc inv k r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  obtain ⟨vs', hv, hk⟩ := wpc_cvt hc h
  rw [ctl_cvt hc]
  exact wp_cvt (m := .part) hv (ihr s f vs' hk)

theorem sound_call (hΓ : Γ.Valid P host) {x : FuncIdx} (hc : ctl i = .call x)
    (ihr : ∀ s f vs, wpc inv k r Q s f vs → HWP P host s f (vals vs ++ expression r) Q)
    (h : wpc inv k (i :: r) Q s f vs) : HWP P host s f (vals vs ++ .plain i :: expression r) Q := by
  rw [ctl_call hc]
  exact hwp_call hΓ (fun s' vs' hk => ihr s' f vs' hk) (wpc_call hc h)

end Cases

/-- **Soundness of the generator** with a valid spec context. -/
theorem wpc_sound_ctx {Γ : VCSpecs H} (hΓ : Γ.Valid P host) (inv : Invs H) (k : Nat)
    (is : List Instr) (Q : Post H) (s : Store H) (f : Frame) (vs : List Val)
    (h : wpc inv k is Q s f vs) :
    HWP P host s f (vals vs ++ expression is) Q := by
  cases is with
  | nil => simpa [expression] using HWP.of_vals (P := P) (host := host) (by rw [wpc] at h; exact h)
  | cons i r =>
    show HWP P host s f (vals vs ++ .plain i :: expression r) Q
    cases hc : ctl i with
    | block bt b => exact sound_block hc (wpc_sound_ctx hΓ inv k b) (wpc_sound_ctx hΓ inv _ r Q) h
    | loop bt b => exact sound_loop hc (wpc_sound_ctx hΓ inv _ b) (wpc_sound_ctx hΓ inv _ r Q) h
    | if_ bt b₁ b₂ =>
      exact sound_if hc (wpc_sound_ctx hΓ inv k b₁) (wpc_sound_ctx hΓ inv _ b₂)
        (wpc_sound_ctx hΓ inv _ r Q) h
    | br l => exact (ctl_br hc) ▸ Wp.br (m := .part) (wpc_br hc h)
    | brIf l => exact sound_brIf hc (wpc_sound_ctx hΓ inv k r Q) h
    | brTable ls d => exact sound_brTable hc h
    | call x => exact sound_call hΓ hc (wpc_sound_ctx hΓ inv k r Q) h
    | cvt op => exact sound_cvt hc (wpc_sound_ctx hΓ inv k r Q) h
    | select => exact sound_select hc (wpc_sound_ctx hΓ inv k r Q) h
    | ret => exact (ctl_ret hc) ▸ Wp.of_exits (m := .part) (o := .ret vs) ⟨_, rfl⟩ (wpc_ret hc h)
    | trap => exact (ctl_trap hc) ▸ Wp.unreachable (m := .part) (wpc_trap hc h)
    | plain => exact sound_plain hc (wpc_sound_ctx hΓ inv k r Q) h
termination_by sizeOf is
decreasing_by
  all_goals
    subst_vars
    simp only [List.cons.sizeOf_spec]
    first
    | omega
    | (have := sizeOf_block hc; omega)
    | (have := sizeOf_loop hc; omega)
    | (have := (sizeOf_if hc).1; omega)
    | (have := (sizeOf_if hc).2; omega)

/-- The empty spec context is valid. -/
theorem VCSpecs.valid_empty : (VCSpecs.empty : VCSpecs H).Valid P host :=
  fun _ _ _ h => nomatch h

/-- **Soundness of the generator** (empty spec context). -/
theorem wpc_sound (inv : Invs H) (k : Nat) (is : List Instr) (Q : Post H) (s : Store H)
    (f : Frame) (vs : List Val) (h : wpc inv k is Q s f vs) :
    HWP P host s f (vals vs ++ expression is) Q :=
  wpc_sound_ctx VCSpecs.valid_empty inv k is Q s f vs h

/-- **A function specification from verification conditions**: if, for every call allowed by
the precondition, the generator's condition holds for the body in the callee's initial frame
(with the loop invariants `inv args s`, which may depend on the arguments and the initial
store), the specification is valid at every profile and for every host relation. -/
theorem FSpecValid.of_wpc {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {S : Silmaril.Wasm.Logic.Hoare.FSpec H}
    (inv : List Val → Store H → Invs H)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (inv args s) 0 code.body
      (Silmaril.Wasm.Examples.Common.bodyPost rs.length (S.post s args)) s
      (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S :=
  Silmaril.Wasm.Examples.Common.FSpecValid.of_body_hwp hfi hcode he hlen fun s args hp => by
    simpa [vals] using wpc_sound (P := P) (host := host) (inv args s) 0 _ _ _ _ [] (hvc s args hp)

/-- `FSpecValid.of_wpc` for a body with calls, specified by a spec context valid at `P` and
`host` (the callee specifications are used, not re-proved: **modular** verification). -/
theorem FSpecValid.of_wpc_ctx {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    {S : Silmaril.Wasm.Logic.Hoare.FSpec H} (inv : List Val → Store H → Invs H)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (inv args s) 0 code.body
      (Silmaril.Wasm.Examples.Common.bodyPost rs.length (S.post s args)) s
      (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S :=
  Silmaril.Wasm.Examples.Common.FSpecValid.of_body_hwp hfi hcode he hlen fun s args hp => by
    simpa [vals] using wpc_sound_ctx hΓ (inv args s) 0 _ _ _ _ [] (hvc s args hp)

end Silmaril.Wasm.Logic.VC
