module

public import Silmaril.Wasm.Logic.Exec.Thms
public import Silmaril.Wasm.Logic.VCInline.Defs
public import Silmaril.Wasm.Logic.VCTotal.Thms

/-!
# Soundness of the generator with inlining

`wpi_sound`: with a valid code table (`C.Valid`) and a valid spec context (`Γ.Valid P host`),
`wpi C d inv k is Q s f vs` implies `HWP P host s f (vals vs ++ expression is) Q`, for every
inlining depth and every family of loop invariants. By well-founded recursion on the depth and
the instruction list: an inlined call is the call rule (`Safe.callIdx`) for the one-call
specification "this store and these arguments, the callee's exits satisfy the continuation",
valid by `FSpecAt.of_body` and the soundness of the callee's condition at depth `d - 1`; a loop
is `HWP.loop` with the invariant "the entry state, or `inv k` together with the inductiveness
condition `G`".
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Safe FSpec FSpecAt labelPost seqPost loopPost seqPostK callPost)

variable {H : Type} {P : Profile} {host : HostSemantics H}

section Cases

variable [Γ : VCSpecs H] {C : Codes H} {d : Nat} {inv : IInvs H} {k : Nat} {i : Instr}
  {r : List Instr} {Q : Post H} {s : Store H} {f : Frame} {vs : List Val}

theorem wpi_block {bt : BlockType} {b : List Instr} (hc : ctl i = .block bt b)
    (h : wpi C d inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args _ n₂ =>
      wpi C d inv k b (labelQ n₂ us (fun s f vs => wpi C d inv (k + loops b) r Q s f vs) Q) s f args := by
  rw [wpi] at h
  split at h <;> simp_all

theorem wpi_loop {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (h : wpi C d inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args n₁ _ =>
      match inv k with
      | none =>
        wpi C d inv (k + 1) b (loopQ n₁ us (fun _ _ _ => False)
          (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s f args
      | some I =>
        I s f args ∧
        ∀ s' f' a', I s' f' a' → f'.module = f.module → a'.length = n₁ →
          wpi C d inv (k + 1) b
            (loopQ n₁ us (fun s'' f'' a'' => I s'' f'' a'' ∧ f''.module = f.module)
              (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s' f' a' := by
  rw [wpi] at h
  split at h <;> (try (exfalso; simp_all; done))
  rename_i bt' b' hc'
  rw [hc] at hc'
  obtain ⟨rfl, rfl⟩ := Ctl.loop.inj hc'
  exact h

theorem wpi_if {bt : BlockType} {b₁ b₂ : List Instr} (hc : ctl i = .if_ bt b₁ b₂)
    (h : wpi C d inv k (i :: r) Q s f vs) : ∃ us c, popI32 vs = some (us, c) ∧
      (c ≠ 0 → enterVC f bt us fun us' args _ n₂ => wpi C d inv k b₁
        (labelQ n₂ us' (fun s f vs => wpi C d inv (k + loops b₁ + loops b₂) r Q s f vs) Q) s f args) ∧
      (c = 0 → enterVC f bt us fun us' args _ n₂ => wpi C d inv (k + loops b₁) b₂
        (labelQ n₂ us' (fun s f vs => wpi C d inv (k + loops b₁ + loops b₂) r Q s f vs) Q) s f args) := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all
  exact ⟨fun hc => by simpa [hc] using h, fun hc => by simpa [hc] using h⟩

theorem wpi_br {l : LabelIdx} (hc : ctl i = .br l) (h : wpi C d inv k (i :: r) Q s f vs) :
    Q s f (.br l.toNat vs) := by
  rw [wpi] at h
  split at h <;> simp_all

theorem wpi_brIf {l : LabelIdx} (hc : ctl i = .brIf l) (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ us c, popI32 vs = some (us, c) ∧ (c ≠ 0 → Q s f (.br l.toNat us)) ∧
      (c = 0 → wpi C d inv k r Q s f us) := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all
  exact ⟨fun hc => by simpa [hc] using h, fun hc => by simpa [hc] using h⟩

theorem wpi_brTable {ls : List LabelIdx} {dl : LabelIdx} (hc : ctl i = .brTable ls dl)
    (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ us c, popI32 vs = some (us, c) ∧ tableI (fun l => Q s f (.br l.toNat us)) c.toNat 0 ls dl := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpi_call {x : FuncIdx} (hc : ctl i = .call x) (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ a, f.module.funcs[x.toNat]? = some a ∧
      ((∃ c, C a = some c ∧ 0 < d ∧ c.np ≤ vs.length ∧ s.funcs[a]? = some c.fi ∧
          wpi C (d - 1) (fun _ => none) 0 c.code.body
            (fnPost c.nr fun s' o => callK f (vs.take (vs.length - c.np))
              (fun s' vs' => wpi C d inv k r Q s' f vs') Q s' o)
            s (Frame.forCall c.fi.module (vs.drop (vs.length - c.np)) c.code.locals) []) ∨
        callVC s f vs x (fun s' vs' => wpi C d inv k r Q s' f vs') Q) := by
  rw [wpi] at h
  split at h <;> (try (exfalso; simp_all; done))
  rename_i x' hx'
  obtain rfl : x' = x := by rw [hc] at hx'; exact (Ctl.call.inj hx').symm
  split at h
  next a ha =>
    refine ⟨a, ha, ?_⟩
    split at h
    next c hca =>
      split at h
      next hd => exact .inl ⟨c, hca, hd, h⟩
      next => exact .inr h
    next => exact .inr h
  next => exact h.elim

theorem wpi_cvt {op : ConvertOp} (hc : ctl i = .cvt op) (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ vs', cvt1 op vs = some vs' ∧ wpi C d inv k r Q s f vs' := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpi_select (hc : ctl i = .select) (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ us v₁ v₂ c, popSelect vs = some (us, v₁, v₂, c) ∧
      (c ≠ 0 → wpi C d inv k r Q s f (us ++ [v₁])) ∧ (c = 0 → wpi C d inv k r Q s f (us ++ [v₂])) := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all
  exact ⟨fun hc => by simpa [hc] using h, fun hc => by simpa [hc] using h⟩

theorem wpi_ret (hc : ctl i = .ret) (h : wpi C d inv k (i :: r) Q s f vs) : Q s f (.ret vs) := by
  rw [wpi] at h
  split at h <;> simp_all

theorem wpi_trap (hc : ctl i = .trap) (h : wpi C d inv k (i :: r) Q s f vs) : Q s f .trap := by
  rw [wpi] at h
  split at h <;> simp_all

theorem wpi_plain (hc : ctl i = .plain) (h : wpi C d inv k (i :: r) Q s f vs) :
    ∃ s' f' rs', Silmaril.Wasm.Logic.Core.exec1 s f vs.reverse i = some (s', f', rs') ∧
      wpi C d inv k r Q s' f' rs'.reverse := by
  rw [wpi] at h
  split at h <;> simp_all
  split at h <;> simp_all

theorem wpi_loop_none {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (hik : inv k = none) (h : wpi C d inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args n₁ _ =>
      wpi C d inv (k + 1) b (loopQ n₁ us (fun _ _ _ => False)
        (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s f args := by
  have h' := wpi_loop hc h
  rw [hik] at h'
  exact h'

theorem wpi_loop_some {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    {I : Store H → Frame → List Val → Prop} (hik : inv k = some I)
    (h : wpi C d inv k (i :: r) Q s f vs) :
    enterVC f bt vs fun us args n₁ _ =>
      I s f args ∧
      ∀ s' f' a', I s' f' a' → f'.module = f.module → a'.length = n₁ →
        wpi C d inv (k + 1) b
          (loopQ n₁ us (fun s'' f'' a'' => I s'' f'' a'' ∧ f''.module = f.module)
            (fun s f vs => wpi C d inv (k + 1 + loops b) r Q s f vs) Q) s' f' a' := by
  have h' := wpi_loop hc h
  rw [hik] at h'
  exact h'

end Cases

theorem tableVC_gt {K : LabelIdx → Prop} {c : Nat} :
    ∀ {j : Nat} {ls : List LabelIdx} {d : LabelIdx}, c < j → tableVC K c j ls d
  | j, [], d, hj => fun h => absurd h (by omega)
  | j, l :: ls, d, hj => ⟨fun h => absurd h (by omega), tableVC_gt (by omega)⟩

theorem tableI_vc {K : LabelIdx → Prop} {c : Nat} :
    ∀ {j : Nat} {ls : List LabelIdx} {d : LabelIdx}, j ≤ c → tableI K c j ls d → tableVC K c j ls d
  | j, [], d, _, h => fun _ => h
  | j, l :: ls, d, hj, h => by
    unfold tableI at h
    by_cases hcj : c = j
    · subst hcj
      simp only [↓reduceIte] at h
      exact ⟨fun _ => h, tableVC_gt (by omega)⟩
    · simp only [hcj, ↓reduceIte] at h
      exact ⟨fun h' => absurd h' hcj, tableI_vc (by omega) h⟩

/-! ## The inlined call and the loop -/

/-- **An inlined call**: the callee's body, run in its initial frame, exits as the caller's
continuation requires. -/
theorem hwp_inline {s : Store H} {f : Frame} {vs : List Val} {x : FuncIdx} {rest : List Admin}
    {Q : Post H} {K : Store H → List Val → Prop} {a : Nat} {c : ICode H}
    (hx : f.module.funcs[x.toNat]? = some a) (hcode : c.fi.code = .wasm c.code)
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (he : Silmaril.Wasm.Validation.Expand c.fi.type (.func ps rs)) (hps : ps.length = c.np)
    (hrs : rs.length = c.nr) (hnp : c.np ≤ vs.length) (hf : s.funcs[a]? = some c.fi)
    (hK : ∀ s' vs', K s' vs' → HWP P host s' f (vals vs' ++ rest) Q)
    (hb : HWP P host s (Frame.forCall c.fi.module (vs.drop (vs.length - c.np)) c.code.locals)
      (expression c.code.body)
      (fnPost c.nr fun s' o => callK f (vs.take (vs.length - c.np)) K Q s' o)) :
    HWP P host s f (vals vs ++ .plain (.call x) :: rest) Q := by
  let us := vs.take (vs.length - c.np)
  let args := vs.drop (vs.length - c.np)
  let S : FSpec H := ⟨fun s' args' => s' = s ∧ args' = args,
    fun _ _ s' o => callK f us K Q s' o⟩
  have hvs : vs = us ++ args := (List.take_append_drop _ _).symm
  have hS : ∀ N, FSpecAt P host N a S := by
    intro N
    cases N with
    | zero => intro _ _ _ _ _ _ _; trivial
    | succ m =>
      refine Silmaril.Wasm.Logic.Hoare.FSpecAt.of_body (fun s' args' h => h.1 ▸ hf) hcode he
        (fun s' args' h => by rw [h.2, hps]; simp only [args, List.length_drop]; omega)
        fun s' args' h f₀ vs₀ => ?_
      rw [h.1, h.2, hrs]
      exact (hb m).post_mono fun _ _ _ hq => fnPost_bodyPostK hq
  intro N
  cases N with
  | zero => trivial
  | succ N =>
    rw [hvs]
    refine Silmaril.Wasm.Logic.Hoare.Safe.callIdx hx hf (hS N) ⟨rfl, rfl⟩ fun s' o hp => ?_
    obtain ⟨-, hR⟩ := hp
    rcases hR with ⟨res, ho, hR⟩ | ⟨ho, hR⟩ | ⟨b, ho, hR⟩
    · rw [ho]; exact hK s' _ hR N
    · rw [ho]; exact hR
    · rw [ho]; exact hR

/-- The loop's body postcondition, from `loopQ` to `loopPost`, for any invariant `J` the back
edges establish. -/
theorem loopQ_post' {n : Nat} {us : List Val} {I J : Store H → Frame → List Val → Prop}
    {K : Store H → Frame → List Val → Prop} {Q : Post H} {rest : List Admin}
    (hIJ : ∀ s f a, I s f a → a.length = n → J s f a)
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q) {s : Store H} {f : Frame}
    {o : Outcome} (h : loopQ n us I K Q s f o) : loopPost n us J (seqPost P host rest Q) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact hK s f _ h
  · obtain ⟨hn, hi⟩ := h
    exact ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; omega, hIJ _ _ _ hi (by simp only [List.length_drop]; omega)⟩
  all_goals exact h

/-- A `block` or `loop` entered: the block type resolves and the stack has its parameters. -/
theorem enterVC_some {f : Frame} {bt : BlockType} {vs : List Val}
    {B : List Val → List Val → Nat → Nat → Prop} (h : enterVC f bt vs B) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ t₁.length ≤ vs.length ∧
      B (vs.take (vs.length - t₁.length)) (vs.drop (vs.length - t₁.length)) t₁.length t₂.length := by
  unfold enterVC at h
  split at h
  next t₁ t₂ hbt => exact ⟨t₁, t₂, hbt, h⟩
  next => exact h.elim

/-- **The inlined `loop` case**, for a body condition `W` sound for every postcondition: the
invariant is "the entry state, or `J` together with the inductiveness condition". -/
theorem hwp_loop_inline {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {b : List Instr} {rest : List Admin} {Q : Post H} {K J : Store H → Frame → List Val → Prop}
    {W : Post H → Store H → Frame → List Val → Prop}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q)
    (hW : ∀ Q' s f a, W Q' s f a → HWP P host s f (vals a ++ expression b) Q')
    (h : enterVC f bt vs fun us args n₁ _ =>
      W (loopQ n₁ us (fun s'' f'' a'' => J s'' f'' a'' ∧ f''.module = f.module ∧
          ∀ s' f' a', J s' f' a' → f'.module = f.module → a'.length = n₁ →
            W (loopQ n₁ us (fun s'' f'' a'' => J s'' f'' a'' ∧ f''.module = f.module) K Q) s' f' a')
        K Q) s f args) :
    HWP P host s f (vals vs ++ .plain (.loop bt b) :: rest) Q := by
  obtain ⟨t₁, t₂, hbt, hle, hb⟩ := enterVC_some h
  let us := vs.take (vs.length - t₁.length)
  let args := vs.drop (vs.length - t₁.length)
  let I₂ := fun (s'' : Store H) (f'' : Frame) a'' => J s'' f'' a'' ∧ f''.module = f.module
  let G : Prop := ∀ s' f' a', J s' f' a' → f'.module = f.module → a'.length = t₁.length →
    W (loopQ t₁.length us I₂ K Q) s' f' a'
  let Inv := fun s' f' a' => (s' = s ∧ f' = f ∧ a' = args) ∨
    (J s' f' a' ∧ f'.module = f.module ∧ a'.length = t₁.length ∧ G)
  have hvs : vs = us ++ args := (List.take_append_drop _ _).symm
  have hcode : vals vs ++ Admin.plain (.loop bt b) :: rest =
      (vals (us ++ args) ++ [Admin.plain (.loop bt b)]) ++ rest := by
    rw [← hvs, List.append_assoc, List.singleton_append]
  have hbt' : ∀ s' f' a', Inv s' f' a' → f'.module.blockType? bt = some (t₁, t₂) :=
    fun _ _ _ hi => hi.elim (fun he => he.2.1 ▸ hbt) (fun hj => hj.2.1 ▸ hbt)
  have hn : ∀ s' f' a', Inv s' f' a' → a'.length = t₁.length := by
    rintro _ _ _ (⟨-, -, ha⟩ | ⟨-, -, hl, -⟩)
    · rw [ha, List.length_drop]; omega
    · exact hl
  have hbody : ∀ s' f' a', Inv s' f' a' → HWP P host s' f' (vals a' ++ expression b)
      (loopPost t₁.length us Inv (seqPost P host rest Q)) := by
    rintro s' f' a' (⟨hs, hf, ha⟩ | ⟨hi, hm, hl, hG⟩)
    · rw [hs, hf, ha]
      exact (hW _ _ _ _ hb).mono fun _ _ _ hq =>
        loopQ_post' (fun _ _ _ hI hl => .inr ⟨hI.1, hI.2.1, hl, hI.2.2⟩) hK hq
    · exact (hW _ _ _ _ (hG s' f' a' hi hm hl)).mono
        fun _ _ _ hq => loopQ_post' (fun _ _ _ hI hl => .inr ⟨hI.1, hI.2, hl, hG⟩) hK hq
  rw [hcode]
  exact Silmaril.Wasm.Logic.Hoare.HWP.seq
    (Silmaril.Wasm.Logic.Hoare.HWP.loop hbt' hn hbody (.inl ⟨rfl, rfl, rfl⟩))

/-- **The `loop` case without an invariant**: the body runs once from the entry state; a
branch back to the loop is impossible. -/
theorem hwp_loop_plain {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {b : List Instr} {rest : List Admin} {Q : Post H} {K : Store H → Frame → List Val → Prop}
    {W : Post H → Store H → Frame → List Val → Prop}
    (hK : ∀ s f vs, K s f vs → HWP P host s f (vals vs ++ rest) Q)
    (hW : ∀ Q' s f a, W Q' s f a → HWP P host s f (vals a ++ expression b) Q')
    (h : enterVC f bt vs fun us args n₁ _ => W (loopQ n₁ us (fun _ _ _ => False) K Q) s f args) :
    HWP P host s f (vals vs ++ .plain (.loop bt b) :: rest) Q := by
  obtain ⟨t₁, t₂, hbt, hle, hb⟩ := enterVC_some h
  let us : List Val := vs.take (vs.length - t₁.length)
  let args : List Val := vs.drop (vs.length - t₁.length)
  have hvs : vs = us ++ args := (List.take_append_drop _ _).symm
  have hcode : vals vs ++ Admin.plain (.loop bt b) :: rest =
      (vals (us ++ args) ++ [Admin.plain (.loop bt b)]) ++ rest := by
    rw [← hvs, List.append_assoc, List.singleton_append]
  rw [hcode]
  refine Silmaril.Wasm.Logic.Hoare.HWP.seq (Silmaril.Wasm.Logic.Hoare.HWP.loop
    (Inv := fun s' f' a' => s' = s ∧ f' = f ∧ a' = args)
    (t₁ := t₁) (t₂ := t₂) (fun _ _ _ hi => hi.2.1 ▸ hbt) ?_ ?_ ⟨rfl, rfl, rfl⟩)
  · rintro _ _ _ ⟨-, -, ha⟩
    rw [ha, List.length_drop]; omega
  · rintro s' f' a' ⟨hs, hf, ha⟩
    rw [hs, hf, ha]
    exact (hW _ _ _ _ hb).mono fun _ _ _ hq => loopQ_post' (fun _ _ _ hI _ => hI.elim) hK hq

/-! ## Soundness -/

/-- **Soundness of the generator with inlining.** -/
theorem wpi_sound {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {C : Codes H} (hC : C.Valid)
    (d : Nat) (inv : IInvs H) (k : Nat) (is : List Instr) (Q : Post H) (s : Store H) (f : Frame)
    (vs : List Val) (h : wpi C d inv k is Q s f vs) :
    HWP P host s f (vals vs ++ expression is) Q := by
  cases is with
  | nil => simpa [expression] using HWP.of_vals (P := P) (host := host) (by simpa only [wpi] using h)
  | cons i r =>
    show HWP P host s f (vals vs ++ .plain i :: expression r) Q
    cases hc : ctl i with
    | block bt b =>
      rw [ctl_block hc]
      exact hwp_block (fun s f vs hk => wpi_sound hΓ hC d inv _ r Q s f vs hk)
        ((wpi_block hc h).mono fun _ args _ _ hb => wpi_sound hΓ hC d inv k b _ s f args hb)
    | loop bt b =>
      show HWP P host s f (vals vs ++ .plain i :: expression r) Q
      rw [ctl_loop hc]
      cases hik : inv k with
      | some I =>
        exact hwp_loop (I := I) (fun s f vs hk => wpi_sound hΓ hC d inv _ r Q s f vs hk)
          ((wpi_loop_some hc hik h).mono fun _ _ _ _ hb => ⟨hb.1, fun s' f' a' hi hm hl =>
            wpi_sound hΓ hC d inv (k + 1) b _ s' f' a' (hb.2 s' f' a' hi hm hl)⟩)
      | none =>
        exact hwp_loop_plain (W := fun Q' s f a => wpi C d inv (k + 1) b Q' s f a)
          (fun s f vs hk => wpi_sound hΓ hC d inv _ r Q s f vs hk)
          (fun Q' s f a hb => wpi_sound hΓ hC d inv (k + 1) b Q' s f a hb) (wpi_loop_none hc hik h)
    | if_ bt b₁ b₂ =>
      obtain ⟨us, c, hp, h₁, h₂⟩ := wpi_if hc h
      rw [ctl_if hc, popI32_eq hp]
      exact HWP.if_
        (fun hc₁ => hwp_block (fun s f vs hk => wpi_sound hΓ hC d inv _ r Q s f vs hk)
          ((h₁ hc₁).mono fun _ args _ _ hb => wpi_sound hΓ hC d inv k b₁ _ s f args hb))
        (fun hc₂ => hwp_block (fun s f vs hk => wpi_sound hΓ hC d inv _ r Q s f vs hk)
          ((h₂ hc₂).mono fun _ args _ _ hb => wpi_sound hΓ hC d inv _ b₂ _ s f args hb))
    | br l => exact (ctl_br hc) ▸ Wp.br (m := .part) (wpi_br hc h)
    | brIf l =>
      obtain ⟨us, c, hp, h₁, h₂⟩ := wpi_brIf hc h
      rw [ctl_brIf hc, popI32_eq hp]
      exact HWP.brIf (fun hc₁ => Wp.br (m := .part) (h₁ hc₁))
        (fun hc₂ => wpi_sound hΓ hC d inv k r Q s f us (h₂ hc₂))
    | brTable ls dl =>
      obtain ⟨us, c, hp, ht⟩ := wpi_brTable hc h
      rw [ctl_brTable hc, popI32_eq hp]
      exact wp_brTable (m := .part) (tableI_vc (Nat.zero_le _) ht)
    | call x =>
      rw [ctl_call hc]
      obtain ⟨a, hx, ⟨c, hca, hd, hnp, hf, hb⟩ | hv⟩ := wpi_call hc h
      · obtain ⟨hcode, ps, rs, he, hps, hrs⟩ := hC a c hca
        exact hwp_inline hx hcode he hps hrs hnp hf
          (fun s' vs' hk => wpi_sound hΓ hC d inv k r Q s' f vs' hk)
          (by simpa [vals] using wpi_sound hΓ hC (d - 1) _ 0 _ _ _ _ [] hb)
      · exact hwp_call hΓ (fun s' vs' hk => wpi_sound hΓ hC d inv k r Q s' f vs' hk) hv
    | cvt op =>
      obtain ⟨vs', hv, hk⟩ := wpi_cvt hc h
      rw [ctl_cvt hc]
      exact wp_cvt (m := .part) hv (wpi_sound hΓ hC d inv k r Q s f vs' hk)
    | select =>
      obtain ⟨ts, hi⟩ := ctl_select hc
      obtain ⟨us, v₁, v₂, c, hp, h₁, h₂⟩ := wpi_select hc h
      rw [hi, popSelect_eq hp]
      by_cases hc₀ : c = 0
      · rw [hc₀]
        exact Wp.selectFalse (m := .part) (wpi_sound hΓ hC d inv k r Q s f _ (h₂ hc₀))
      · exact Wp.selectTrue (m := .part) hc₀ (wpi_sound hΓ hC d inv k r Q s f _ (h₁ hc₀))
    | ret => exact (ctl_ret hc) ▸ Wp.of_exits (m := .part) (o := .ret vs) ⟨_, rfl⟩ (wpi_ret hc h)
    | trap => exact (ctl_trap hc) ▸ Wp.unreachable (m := .part) (wpi_trap hc h)
    | plain =>
      obtain ⟨s', f', rs', he, hk⟩ := wpi_plain hc h
      have h₁ : Wp .part P host s f (vals vs.reverse.reverse ++ .plain i :: expression r) Q :=
        Silmaril.Wasm.Logic.Exec.Wp.exec1 he (wpi_sound hΓ hC d inv k r Q s' f' rs'.reverse hk)
      simpa only [List.reverse_reverse, Silmaril.Wasm.Logic.Hoare.wp_part] using h₁
termination_by (d, sizeOf is)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       subst_vars
       simp only [List.cons.sizeOf_spec]
       first
       | omega
       | (have := sizeOf_block hc; omega)
       | (have := sizeOf_loop hc; omega)
       | (have := (sizeOf_if hc).1; omega)
       | (have := (sizeOf_if hc).2; omega))

/-- **A function specification** from the generator with inlining (body postcondition
`fnPost`, accepting `return`). -/
theorem FSpecValid.of_wpi {Γ : VCSpecs H} (hΓ : Γ.Valid P host) {C : Codes H} (hC : C.Valid)
    (d : Nat) {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    {S : FSpec H} (inv : List Val → Store H → IInvs H)
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hvc : ∀ s args, S.pre s args → wpi C d (inv args s) 0 code.body (fnPost rs.length (S.post s args))
      s (Frame.forCall fi.module args code.locals) []) :
    Silmaril.Wasm.Logic.Hoare.FSpecValid P host a S := by
  intro n
  cases n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ n =>
    refine Silmaril.Wasm.Logic.Hoare.FSpecAt.of_body hfi hcode he hlen fun s args hpre f vs₀ => ?_
    have h := wpi_sound (P := P) (host := host) hΓ hC d (inv args s) 0 _ _ _ _ [] (hvc s args hpre)
    simp only [vals, List.map_nil, List.nil_append] at h
    exact (h n).post_mono fun _ _ _ hq => fnPost_bodyPostK hq

end Silmaril.Wasm.Logic.VC
