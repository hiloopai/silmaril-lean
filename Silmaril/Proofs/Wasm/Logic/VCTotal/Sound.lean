module

public import Silmaril.Wasm.Logic.Exec.Thms
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Logic.VCTotal.Defs
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# Total correctness from the verification-condition generator, for loop-free code

`wpc_sound_total`: for an instruction list without loops (`loops is = 0`), the generator's
condition `wpc inv k is Q s f vs` implies the **total-correctness** weakest precondition
`TWP P host s f (vals vs ++ expression is) Q` (every run terminates, at an exit satisfying `Q`),
at every profile and for every host relation. The proof follows `Silmaril.Wasm.Logic.VC.wpc_sound`
case by case, with the total rules `TWP.block`, `TWP.if_`, `TWP.brIf` and the symbolic-execution
step `Common.Wp.exec1` at `Wp .total`; the `loop` case is excluded by `loops is = 0`.

`TFSpecAt.of_wpc`: a total function specification from the generator's condition for a
loop-free body. So `wat_vc` proves total correctness of loop-free functions unchanged.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (TWP TSafe Wp labelPostT seqPostT)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## `loops` at each kind of instruction -/

section Loops

variable {i : Instr} {r : List Instr}

theorem loops_block {bt : BlockType} {b : List Instr} (hc : ctl i = .block bt b) :
    loops (i :: r) = loops b + loops r := by
  rw [loops]
  split <;> simp_all

theorem loops_loop {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b) :
    loops (i :: r) = loops b + 1 + loops r := by
  rw [loops]
  split <;> simp_all

theorem loops_if {bt : BlockType} {b₁ b₂ : List Instr} (hc : ctl i = .if_ bt b₁ b₂) :
    loops (i :: r) = loops b₁ + loops b₂ + loops r := by
  rw [loops]
  split <;> simp_all

theorem loops_other (hb : ∀ bt b, ctl i ≠ .block bt b) (hl : ∀ bt b, ctl i ≠ .loop bt b)
    (hi : ∀ bt b₁ b₂, ctl i ≠ .if_ bt b₁ b₂) : loops (i :: r) = loops r := by
  rw [loops]
  split <;> simp_all

end Loops

/-! ## Blocks -/

/-- The outcome of a block body, from `labelQ` to `labelPostT`. -/
theorem labelQ_postT {n : Nat} {us : List Val} {K : Store H → Frame → List Val → Prop}
    {Q : Post H} {rest : List Admin}
    (hK : ∀ s f vs, K s f vs → TWP P host s f (vals vs ++ rest) Q) {s : Store H} {f : Frame}
    {o : Outcome} (h : labelQ n us K Q s f o) :
    labelPostT P host n [] us (seqPostT P host rest Q) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact hK s f _ h
  · obtain ⟨hn, hk⟩ := h
    refine ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; omega, ?_⟩
    refine TSafe.exit (.normal (us ++ vs.drop (vs.length - n))) ?_ ?_
    · show _ = _
      simp [expression, vals, List.map_drop]
    · exact hK s f _ hk
  all_goals exact h

/-- **The `block` case**, total correctness. -/
theorem twp_block {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {b : List Instr}
    {rest : List Admin} {Q : Post H} {K : Store H → Frame → List Val → Prop}
    (hK : ∀ s f vs, K s f vs → TWP P host s f (vals vs ++ rest) Q)
    (h : enterVC f bt vs fun us args _ n₂ =>
      TWP P host s f (vals args ++ expression b) (labelQ n₂ us K Q)) :
    TWP P host s f (vals vs ++ .plain (.block bt b) :: rest) Q := by
  unfold enterVC at h
  split at h
  next t₁ t₂ hbt =>
    obtain ⟨hle, hb⟩ := h
    have hvs : vs = vs.take (vs.length - t₁.length) ++ vs.drop (vs.length - t₁.length) :=
      (List.take_append_drop _ _).symm
    rw [hvs]
    exact Silmaril.Wasm.Logic.Hoare.TWP.block hbt (by simp only [List.length_drop]; omega)
      (TSafe.post_mono hb fun _ _ _ hq => labelQ_postT hK hq)
  next => exact h.elim

/-! ## Calls -/

/-- **The `call` case**, total correctness: the callee's specification is totally correct. -/
theorem twp_call {Γ : VCSpecs H} (hΓ : Γ.TValid P host) {s : Store H} {f : Frame}
    {vs : List Val} {x : FuncIdx} {rest : List Admin} {Q : Post H}
    {K : Store H → List Val → Prop}
    (hK : ∀ s' vs', K s' vs' → TWP P host s' f (vals vs' ++ rest) Q)
    (h : callVC s f vs x K Q) :
    TWP P host s f (vals vs ++ .plain (.call x) :: rest) Q := by
  unfold callVC at h
  split at h
  next a hx =>
    split at h
    next n S hS =>
      obtain ⟨hn, hpre, hpost⟩ := h
      obtain ⟨fi, hf⟩ := Option.isSome_iff_exists.mp ((hΓ a n S hS).2 _ _ hpre)
      have hvs : vs = vs.take (vs.length - n) ++ vs.drop (vs.length - n) :=
        (List.take_append_drop _ _).symm
      show TSafe P host Q _
      rw [hvs]
      refine Silmaril.Wasm.Logic.Hoare.TSafe.callIdx hx hf (hΓ a n S hS).1 hpre ?_
      rintro s' o ⟨-, ⟨res, rfl, hR⟩ | ⟨rfl, hR⟩ | ⟨b, rfl, hR⟩⟩
      · exact hK s' _ (hpost s' _ hR)
      · exact hpost s' _ hR
      · exact hpost s' _ hR
    next => exact h.elim
  next => exact h.elim

/-! ## Soundness -/

/-- **Total soundness of the generator for loop-free code**, with a totally correct spec
context. -/
theorem wpc_sound_total_ctx {Γ : VCSpecs H} (hΓ : Γ.TValid P host) (inv : Invs H) (k : Nat)
    (is : List Instr) (hl : loops is = 0)
    (Q : Post H) (s : Store H) (f : Frame) (vs : List Val) (h : wpc inv k is Q s f vs) :
    TWP P host s f (vals vs ++ expression is) Q := by
  cases is with
  | nil =>
    simpa [expression] using
      (Wp.of_vals (m := .total) (P := P) (host := host) (by rw [wpc] at h; exact h))
  | cons i r =>
    show TWP P host s f (vals vs ++ .plain i :: expression r) Q
    cases hc : ctl i with
    | block bt b =>
      have hl' : loops (i :: r) = loops b + loops r := loops_block hc
      rw [ctl_block hc]
      exact twp_block (fun s f vs => wpc_sound_total_ctx hΓ inv _ r (by omega) Q s f vs)
        ((wpc_block hc h).mono fun _ args _ _ hb =>
          wpc_sound_total_ctx hΓ inv k b (by omega) _ s f args hb)
    | loop bt b =>
      have hl' : loops (i :: r) = loops b + 1 + loops r := loops_loop hc
      omega
    | if_ bt b₁ b₂ =>
      show TWP P host s f (vals vs ++ .plain i :: expression r) Q
      have hl' : loops (i :: r) = loops b₁ + loops b₂ + loops r := loops_if hc
      obtain ⟨us, c, hp, h₁, h₂⟩ := wpc_if hc h
      rw [ctl_if hc, popI32_eq hp]
      refine Silmaril.Wasm.Logic.Hoare.TWP.if_ ?_
      by_cases hc₀ : c ≠ 0
      · simp only [hc₀, ↓reduceIte, ne_eq, not_false_eq_true]
        exact twp_block (fun s f vs => wpc_sound_total_ctx hΓ inv _ r (by omega) Q s f vs)
          ((h₁ hc₀).mono fun _ args _ _ hb => wpc_sound_total_ctx hΓ inv k b₁ (by omega) _ s f args hb)
      · simp only [hc₀, ↓reduceIte]
        exact twp_block (fun s f vs => wpc_sound_total_ctx hΓ inv _ r (by omega) Q s f vs)
          ((h₂ (by simpa using hc₀)).mono fun _ args _ _ hb =>
            wpc_sound_total_ctx hΓ inv _ b₂ (by omega) _ s f args hb)
    | br l =>
      exact (ctl_br hc) ▸ Wp.br (m := .total) (wpc_br hc h)
    | brIf l =>
      have hl' : loops (i :: r) = loops r :=
        loops_other (by simp [hc]) (by simp [hc]) (by simp [hc])
      obtain ⟨us, c, hp, h₁, h₂⟩ := wpc_brIf hc h
      rw [ctl_brIf hc, popI32_eq hp]
      exact Silmaril.Wasm.Logic.Hoare.TWP.brIf h₁
        (fun hc₂ => wpc_sound_total_ctx hΓ inv k r (by omega) Q s f us (h₂ hc₂))
    | brTable ls d =>
      obtain ⟨us, c, hp, ht⟩ := wpc_brTable hc h
      rw [ctl_brTable hc, popI32_eq hp]
      exact wp_brTable (m := .total) ht
    | call x =>
      have hl' : loops (i :: r) = loops r :=
        loops_other (by simp [hc]) (by simp [hc]) (by simp [hc])
      rw [ctl_call hc]
      exact twp_call hΓ (fun s' vs' hk => wpc_sound_total_ctx hΓ inv k r (by omega) Q s' f vs' hk)
        (wpc_call hc h)
    | cvt op =>
      have hl' : loops (i :: r) = loops r :=
        loops_other (by simp [hc]) (by simp [hc]) (by simp [hc])
      obtain ⟨vs', hv, hk⟩ := wpc_cvt hc h
      rw [ctl_cvt hc]
      exact wp_cvt (m := .total) hv (wpc_sound_total_ctx hΓ inv k r (by omega) Q s f vs' hk)
    | select =>
      show TWP P host s f (vals vs ++ .plain i :: expression r) Q
      have hl' : loops (i :: r) = loops r :=
        loops_other (by simp [hc]) (by simp [hc]) (by simp [hc])
      obtain ⟨ts, hi⟩ := ctl_select hc
      obtain ⟨us, v₁, v₂, c, hp, h₁, h₂⟩ := wpc_select hc h
      rw [hi, popSelect_eq hp]
      by_cases hc₀ : c = 0
      · rw [hc₀]
        exact Wp.selectFalse (m := .total)
          (wpc_sound_total_ctx hΓ inv k r (by omega) Q s f _ (h₂ hc₀))
      · exact Wp.selectTrue (m := .total) hc₀
          (wpc_sound_total_ctx hΓ inv k r (by omega) Q s f _ (h₁ hc₀))
    | trap => exact (ctl_trap hc) ▸ Wp.unreachable (m := .total) (wpc_trap hc h)
    | ret =>
      exact (ctl_ret hc) ▸ Wp.of_exits (m := .total) (o := .ret vs) ⟨_, rfl⟩ (wpc_ret hc h)
    | plain =>
      have hl' : loops (i :: r) = loops r :=
        loops_other (by simp [hc]) (by simp [hc]) (by simp [hc])
      obtain ⟨s', f', rs', he, hk⟩ := wpc_plain hc h
      have h₁ : Wp .total P host s f (vals vs.reverse.reverse ++ .plain i :: expression r) Q :=
        Silmaril.Wasm.Logic.Exec.Wp.exec1 he
          (wpc_sound_total_ctx hΓ inv k r (by omega) Q s' f' rs'.reverse hk)
      simpa only [List.reverse_reverse, Silmaril.Wasm.Logic.Hoare.wp_total] using h₁
termination_by sizeOf is
decreasing_by
  all_goals
    subst_vars
    simp only [List.cons.sizeOf_spec]
    first
    | omega
    | (have := sizeOf_block hc; omega)
    | (have := (sizeOf_if hc).1; omega)
    | (have := (sizeOf_if hc).2; omega)

/-- The empty spec context is totally correct. -/
theorem VCSpecs.tvalid_empty : (VCSpecs.empty : VCSpecs H).TValid P host :=
  fun _ _ _ h => nomatch h

/-- **Total soundness of the generator for loop-free code** (empty spec context). -/
theorem wpc_sound_total (inv : Invs H) (k : Nat) (is : List Instr) (hl : loops is = 0)
    (Q : Post H) (s : Store H) (f : Frame) (vs : List Val) (h : wpc inv k is Q s f vs) :
    TWP P host s f (vals vs ++ expression is) Q :=
  wpc_sound_total_ctx VCSpecs.tvalid_empty inv k is hl Q s f vs h

/-- `bodyPost` (returns or traps) seen as the total body postcondition of a call. -/
theorem bodyPost_bodyPostT {n : Nat} {R : Store H → Outcome → Prop} {f : Frame}
    {vs₀ : List Val} {s : Store H} {F : Frame} {o : Outcome}
    (h : Silmaril.Wasm.Logic.Exec.bodyPost n R s F o) :
    Silmaril.Wasm.Logic.Hoare.bodyPostT P host n f vs₀
      (Silmaril.Wasm.Logic.Hoare.callPost f vs₀ R) s F o := by
  rcases o with res | _ | _ | _ | _ | _
  · exact ⟨by simpa using h.1, rfl, .inl ⟨res, rfl, h.2⟩⟩
  all_goals first | exact h.elim | exact ⟨rfl, .inr (.inl ⟨rfl, h⟩)⟩

/-- **A total function specification from verification conditions** for a loop-free body. -/
theorem TFSpecAt.of_wpc {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {S : Silmaril.Wasm.Logic.Hoare.FSpec H}
    (inv : List Val → Store H → Invs H) (hl : loops code.body = 0)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (inv args s) 0 code.body
      (Silmaril.Wasm.Logic.Exec.bodyPost rs.length (S.post s args)) s
      (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S :=
  Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body hfi hcode he hlen fun s args hp f vs₀ => by
    have h := wpc_sound_total (P := P) (host := host) (inv args s) 0 _ hl _ _ _ [] (hvc s args hp)
    simp only [vals, List.map_nil, List.nil_append] at h
    exact TSafe.post_mono h fun _ _ _ hq => bodyPost_bodyPostT hq

end Silmaril.Wasm.Logic.VC

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (TWP TSafe Wp labelPostT seqPostT)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The cut rule**: a loop-free segment `is₁` verified by `wpc` up to the cut predicate `C`,
followed by code `rest` that is totally correct from every state satisfying `C`. -/
theorem twp_cut {inv : Invs H} {k : Nat} {is₁ : List Instr} {rest : List Admin}
    {C : Store H → Frame → List Val → Prop} {Q : Post H} {s : Store H} {f : Frame}
    {vs : List Val} (hl : loops is₁ = 0) (h : wpc inv k is₁ (cutQ C Q) s f vs)
    (hC : ∀ s f vs, C s f vs → TWP P host s f (vals vs ++ rest) Q) :
    TWP P host s f (vals vs ++ (expression is₁ ++ rest)) Q := by
  rw [← List.append_assoc]
  refine Silmaril.Wasm.Logic.Hoare.TWP.seq (TSafe.post_mono (wpc_sound_total inv k is₁ hl _ s f vs h)
    fun s f o hq => ?_)
  rcases o with vs' | _ | _ | _ | _ | _
  · exact hC s f vs' hq
  all_goals exact hq

/-- **`bodyPost` is the no-`return` case of `fnPost`**: every outcome `bodyPost` allows,
`fnPost` allows. -/
theorem fnPost_of_bodyPost {n : Nat} {R : Store H → Outcome → Prop} {s : Store H} {f : Frame}
    {o : Outcome} (h : Silmaril.Wasm.Logic.Exec.bodyPost n R s f o) : fnPost n R s f o := by
  rcases o with _ | _ | _ | _ | _ | _ <;> first | exact h | exact h.elim

set_option linter.unusedTactic false in
/-- `bodyPost` is exactly `fnPost` restricted to outcomes other than `return`. -/
theorem bodyPost_iff_fnPost {n : Nat} {R : Store H → Outcome → Prop} {s : Store H} {f : Frame}
    {o : Outcome} :
    Silmaril.Wasm.Logic.Exec.bodyPost n R s f o ↔ fnPost n R s f o ∧ ∀ vs, o ≠ .ret vs := by
  refine ⟨fun h => ⟨fnPost_of_bodyPost h, ?_⟩, fun ⟨h, hr⟩ => ?_⟩
  · rintro vs rfl
    exact h
  · rcases o with _ | _ | vs | _ | _ | _
    all_goals first | exact h | exact h.elim | exact absurd rfl (hr vs)

/-- `fnPost` seen as the total body postcondition of a call. -/
theorem fnPost_bodyPostT {n : Nat} {R : Store H → Outcome → Prop} {f : Frame}
    {vs₀ : List Val} {s : Store H} {F : Frame} {o : Outcome} (h : fnPost n R s F o) :
    Silmaril.Wasm.Logic.Hoare.bodyPostT P host n f vs₀
      (Silmaril.Wasm.Logic.Hoare.callPost f vs₀ R) s F o := by
  rcases o with res | _ | vs | _ | _ | _
  · exact ⟨by simpa using h.1, rfl, .inl ⟨res, rfl, h.2⟩⟩
  · exact h.elim
  · refine ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; have := h.1; omega, rfl, .inl ⟨_, rfl, h.2⟩⟩
  all_goals first | exact h.elim | exact ⟨rfl, .inr (.inl ⟨rfl, h⟩)⟩

/-- **A total function specification from a total proof of the body** that returns (falling
through or by `return`) or traps. -/
theorem TFSpecAt.of_fnPost {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {S : Silmaril.Wasm.Logic.Hoare.FSpec H}
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hbody : ∀ s args, S.pre s args → TWP P host s (Frame.forCall fi.module args code.locals)
      (expression code.body) (fnPost rs.length (S.post s args))) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S :=
  Silmaril.Wasm.Logic.Hoare.TFSpecAt.of_body hfi hcode he hlen fun s args hp _ _ =>
    TSafe.post_mono (hbody s args hp) fun _ _ _ hq => fnPost_bodyPostT hq

/-- `fnPost` (returns by falling through or by `return`, or traps) gives the step-indexed body
postcondition of a call, at every index. -/
theorem fnPost_bodyPostK {n k : Nat} {R : Store H → Outcome → Prop} {f : Frame}
    {vs₀ : List Val} {s : Store H} {F : Frame} {o : Outcome} (h : fnPost n R s F o) :
    Silmaril.Wasm.Logic.Hoare.bodyPostK P host n f vs₀
      (Silmaril.Wasm.Logic.Hoare.callPost f vs₀ R) k s F o := by
  rcases o with res | _ | vs | _ | _ | _
  · exact ⟨by simpa using h.1, rfl, .inl ⟨res, rfl, h.2⟩⟩
  · exact h.elim
  · refine ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; have := h.1; omega, rfl, .inl ⟨_, rfl, h.2⟩⟩
  all_goals first | exact h.elim | exact ⟨rfl, .inr (.inl ⟨rfl, h⟩)⟩

/-- **A function specification from verification conditions**, with a valid spec context for
the calls of the body and the body postcondition `fnPost` (which, unlike `bodyPost`, accepts
`return`). -/
theorem FSpecValid.of_wpc_fn {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    {S : Silmaril.Wasm.Logic.Hoare.FSpec H} (inv : List Val → Store H → Invs H)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (inv args s) 0 code.body (fnPost rs.length (S.post s args))
      s (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S := by
  intro n
  cases n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ n =>
    refine Silmaril.Wasm.Logic.Hoare.FSpecAt.of_body hfi hcode he hlen fun s args hpre f vs₀ => ?_
    have h := wpc_sound_ctx (P := P) (host := host) hΓ (inv args s) 0 _ _ _ _ [] (hvc s args hpre)
    simp only [vals, List.map_nil, List.nil_append] at h
    exact (h n).post_mono fun _ _ _ hq => fnPost_bodyPostK hq

/-- `TFSpecAt.of_wpc` with a totally correct spec context and `fnPost` (loop-free body). -/
theorem TFSpecAt.of_wpc_fn {Γ : VCSpecs H} (hΓ : Γ.TValid P host) {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    {S : Silmaril.Wasm.Logic.Hoare.FSpec H} (inv : List Val → Store H → Invs H)
    (hl : loops code.body = 0)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpc (inv args s) 0 code.body (fnPost rs.length (S.post s args))
      s (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S :=
  TFSpecAt.of_fnPost hfi hcode he hlen fun s args hp => by
    have h := wpc_sound_total_ctx (P := P) (host := host) hΓ (inv args s) 0 _ hl _ _ _ []
      (hvc s args hp)
    simpa only [vals, List.map_nil, List.nil_append] using h

end Silmaril.Wasm.Logic.VC

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post WP)
open Silmaril.Wasm.Logic.Hoare (TWP TSafe)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Total correctness gives a run** (`WP`, the existential weakest precondition), for
postconditions that exclude traps and escaping exceptions (on those outcomes the two notions
of final form differ). -/
theorem wp_of_twp {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (hQ : ∀ s f, ¬ Q s f .trap ∧ ∀ a, ¬ Q s f (.throw a)) (h : TWP P host s f code Q) :
    WP P host s f code Q := by
  have : ∀ c : Config H, TSafe P host Q c → ∃ s' f' c' o,
      Steps P host c ⟨s', f', c'⟩ ∧ o.Ends c' ∧ Q s' f' o := by
    intro c hc
    induction hc with
    | @exit c o he hq =>
      refine ⟨c.store, c.frame, c.code, o, .refl, ?_, hq⟩
      rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, cc⟩
      · exact he
      · exact he
      · exact he
      · exact ((hQ _ _).1 hq).elim
      · exact ((hQ _ _).2 a hq).elim
      · exact he
    | step hp _ ih =>
      obtain ⟨c₁, h₁⟩ := hp
      obtain ⟨s', f', c', o, hs, he, hq⟩ := ih c₁ h₁
      exact ⟨s', f', c', o, .head h₁ hs, he, hq⟩
  exact this _ h

end Silmaril.Wasm.Logic.VC

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **A (partial) function specification from an every-run proof of the body** that returns
(falling through or by `return`) or traps. -/
theorem FSpecValid.of_fnPost {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {S : Silmaril.Wasm.Logic.Hoare.FSpec H}
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hbody : ∀ s args, S.pre s args → Silmaril.Wasm.Logic.Hoare.HWP P host s
      (Frame.forCall fi.module args code.locals) (expression code.body)
      (fnPost rs.length (S.post s args))) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S := by
  intro n
  cases n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ n =>
    exact Silmaril.Wasm.Logic.Hoare.FSpecAt.of_body hfi hcode he hlen fun s args hpre f vs₀ =>
      (hbody s args hpre n).post_mono fun _ _ _ h => fnPost_bodyPostK h

end Silmaril.Wasm.Logic.VC
namespace Silmaril.Wasm.Logic.Hoare

/-- `Silmaril.Wasm.Logic.VC.TFSpecAt.of_wpc`, in the namespace of `TFSpecAt`. -/
alias TFSpecAt.of_wpc := Silmaril.Wasm.Logic.VC.TFSpecAt.of_wpc

/-- `Silmaril.Wasm.Logic.VC.TFSpecAt.of_wpc_fn`, in the namespace of `TFSpecAt`. -/
alias TFSpecAt.of_wpc_fn := Silmaril.Wasm.Logic.VC.TFSpecAt.of_wpc_fn

end Silmaril.Wasm.Logic.Hoare
