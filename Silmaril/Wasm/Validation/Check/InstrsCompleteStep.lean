module

public import Silmaril.Wasm.Validation.Check.Instrs

@[expose] public section

/-! # Principal completeness of `directStep`

If `i : t₁ →_xs t₂` (a non-structured instruction) and the top of the stack `S`
matches `t₁`, then `directStep` accepts: a normal step consumes `t₁.length`
operands, initialises `xs` and produces some `out <: t₂`; a polymorphic step
consumes at most `t₁.length` operands.

The two oracles are assumed complete (`TyOkComplete`, `AtomComplete`).
-/

namespace Silmaril.Wasm.Validation.StepComplete

open Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs

/-- Completeness of the type-validity oracle (in closed, well-formed contexts). -/
def TyOkComplete (tyOk : TyOkOracle) : Prop :=
  ∀ (Δ : TypeCtx) (k : TKind) (t : Ty k), Δ.Ok → Δ.recs = [] → TyOk Δ t → tyOk Δ t = true

/-- The instructions handled by `directStep` itself (or by the structured cases of
`checkInstr`). -/
def isCtl : Instr → Bool
  | .unreachable | .br _ | .brIf _ | .brTable _ _ | .brOnNull _ | .brOnNonNull _
  | .brOnCast _ _ _ | .brOnCastFail _ _ _ | .call _ | .callRef _ | .callIndirect _ _
  | .return_ | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ | .throw _
  | .throwRef | .block _ _ | .loop _ _ | .if_ _ _ _ | .tryTable _ _ _ => true
  | _ => false

/-- Completeness of the fallthrough oracle (shape of `atomicA?_complete`), for the
instructions not handled by `directStep` and not an implicit `select` on two `BOT`s. -/
def AtomComplete (atom? : AtomOracle) : Prop :=
  ∀ (C : Context) (S : List CValType) (i : Instr) (t₁ t₂ : List CValType) (xs : List Nat),
    C.Wf → C.recs = [] → isCtl i = false →
    ¬ (i = .select none ∧ ∃ S₀ c, S = S₀ ++ [.botv, .botv, c]) →
    InstrOk C i ⟨t₁, xs, t₂⟩ → ResultOk C.toTypeCtx S → t₁.length ≤ S.length →
    ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁ →
    ∃ out, atom? C S i = some (t₁.length, xs, out) ∧ ResultOk C.toTypeCtx out ∧
      ResultSub C.toTypeCtx out t₂

/-! ## Small completeness lemmas -/

theorem resSub_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {a b : List CValType}
    (ha : ResultOk Δ a) (hb : ResultOk Δ b) (h : ResultSub Δ a b) : resSub Δ a b = true :=
  Sub.check_complete hΔ hr ((ResultSub.iff_sub Δ a b).1 h) (TyOk.ofList _ ha) (TyOk.ofList _ hb)

theorem topSub_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {S t : List CValType}
    (hS : ResultOk Δ S) (ht : ResultOk Δ t) (hlen : t.length ≤ S.length)
    (hsub : ResultSub Δ (S.drop (S.length - t.length)) t) : topSub Δ S t = true := by
  simp only [topSub, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlen, resSub_complete hΔ hr (ResultOk.drop' hS _) ht hsub⟩

theorem stepA_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {S t : List CValType}
    {xs : List Nat} {out : List CValType}
    (hS : ResultOk Δ S) (ht : ResultOk Δ t) (hlen : t.length ≤ S.length)
    (hsub : ResultSub Δ (S.drop (S.length - t.length)) t) :
    stepA Δ S t xs out = some (.normal t.length xs out) := by
  unfold stepA; rw [ite_eq_left (topSub_complete hΔ hr hS ht hlen hsub)]

theorem stepB_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {S t : List CValType}
    (hS : ResultOk Δ S) (ht : ResultOk Δ t) (hlen : t.length ≤ S.length)
    (hsub : ResultSub Δ (S.drop (S.length - t.length)) t) :
    stepB Δ S t = some (.poly t) := by
  unfold stepB; rw [ite_eq_left (topSub_complete hΔ hr hS ht hlen hsub)]

theorem splitLast_append {α : Type} (l : List α) (a : α) : splitLast (l ++ [a]) = some (l, a) := by
  simp [splitLast]

theorem funcOfDef?_complete {d : DefType} {ps rs : Ty (.list .val)} (h : Expand d (.func ps rs)) :
    funcOfDef? d = some (ps, rs) := by
  unfold funcOfDef?; rw [Expand.iff.1 h]

theorem tagParams?_complete {C : Context} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)}
    (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil)) :
    tagParams? C x = some ts.toList := by
  unfold tagParams?; rw [hx]; simp only; rw [Expand.iff.1 he]; rfl

/-- Splitting a result subtyping at an append on the right. -/
theorem sub_split {Δ : TypeCtx} {D A B : List CValType} (h : ResultSub Δ D (A ++ B)) :
    ResultSub Δ (D.take A.length) A ∧ ResultSub Δ (D.drop A.length) B := by
  constructor
  · have := List.forall₂_take A.length h
    simpa [ResultSub] using this
  · have := List.forall₂_drop A.length h
    simpa [ResultSub] using this

theorem ResultSub.length_eq' {Δ : TypeCtx} {a b : List CValType} (h : ResultSub Δ a b) :
    a.length = b.length := List.Forall₂.length_eq h

theorem drop_drop_top (S : List CValType) (a b : Nat) (h : a + b ≤ S.length) :
    (S.drop (S.length - (a + b))).drop a = S.drop (S.length - b) := by
  rw [List.drop_drop]; congr 1; omega

/-- The top `B` part of a top-of-stack match on `A ++ B`. -/
theorem top_suffix {Δ : TypeCtx} {S A B : List CValType} (hlen : (A ++ B).length ≤ S.length)
    (hsub : ResultSub Δ (S.drop (S.length - (A ++ B).length)) (A ++ B)) :
    B.length ≤ S.length ∧ ResultSub Δ (S.drop (S.length - B.length)) B := by
  have h2 := (sub_split hsub).2
  rw [List.length_append] at hlen h2
  rw [drop_drop_top S _ _ hlen] at h2
  exact ⟨by omega, h2⟩

theorem mem_of_top {S : List CValType} {n : Nat} {t : CValType}
    (h : t ∈ S.drop n) : t ∈ S := List.mem_of_mem_drop h

end Silmaril.Wasm.Validation.StepComplete

namespace Silmaril.Wasm.Validation

open StepComplete CheckInstrs

variable {atom? : AtomOracle} {tyOk : TyOkOracle}

theorem directStep_complete (hatom : AtomComplete atom?) (htyOk : TyOkComplete tyOk) :
    ∀ (C : Context) (S : List CValType) (i : Instr) (t₁ t₂ : List CValType) (xs : List Nat),
      C.Wf → C.recs = [] → (∀ bt b, i ≠ .block bt b) → (∀ bt b, i ≠ .loop bt b) →
      (∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) → (∀ bt cs b, i ≠ .tryTable bt cs b) →
      ¬ (i = .select none ∧ ∃ S₀ c, S = S₀ ++ [.botv, .botv, c]) →
      InstrOk C i ⟨t₁, xs, t₂⟩ → ResultOk C.toTypeCtx S → t₁.length ≤ S.length →
      ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁ →
      ∃ r, directStep atom? tyOk C S i = some r ∧
        (match r with
          | .normal n xs' out => n = t₁.length ∧ xs' = xs ∧ ResultOk C.toTypeCtx out ∧
              ResultSub C.toTypeCtx out t₂
          | .poly t' => t'.length ≤ t₁.length) := by
  intro C S i t₁ t₂ xs hC hr hnb hnl hni hnt hsel hi hS hlen hsub
  have hΔ : C.toTypeCtx.Ok := hC.types
  have hr' : C.toTypeCtx.recs = [] := hr
  have hreg := InstrOk.regular hC hi
  unfold directStep
  split
  · -- unreachable
    cases hi with
    | parametric h => ?_
    | _ => (rename_i h; cases h)
    cases h
    refine ⟨_, stepB_complete hΔ hr' hS (by simp [ResultOk]) (by simp) (by simp [ResultSub]), ?_⟩
    simp
  · -- br
    cases hi with
    | br hl _ => ?_
    | _ => (rename_i h; cases h)
    rw [hl]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (hC.label hl) hl2 hs2, by simp⟩
  · -- br_if
    cases hi with
    | brIf hl => ?_
    | _ => (rename_i h; cases h)
    rw [hl]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- br_table
    rename_i ls l'
    cases hi with
    | @brTable _ _ _ ts t₁' _ hls hl' _ => ?_
    | _ => (rename_i h; cases h)
    obtain ⟨lt, hlt, hslt⟩ := hl'
    have hm : lt.length = ts.length := (ResultSub.length_eq' hslt).symm
    rw [List.append_assoc] at hlen hsub hreg
    have htsok : ResultOk C.toTypeCtx ts := (ResultOk.right hreg.1).left
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    simp only [List.length_append, List.length_singleton] at hl2 hs2
    obtain ⟨hA, hB⟩ := sub_split hs2
    have hXok : ResultOk C.toTypeCtx
        ((S.drop (S.length - (ts.length + 1))).take ts.length) :=
      ResultOk.take' (ResultOk.drop' hS _) _
    have hres : resOk tyOk C.toTypeCtx
        ((S.drop (S.length - (ts.length + 1))).take ts.length) = true :=
      List.all_eq_true.2 (fun t ht => htyOk _ _ _ hΔ hr' (hXok t ht))
    have hall : (l' :: ls).all (fun l => match C.labels[l.toNat]? with
        | some lt => resSub C.toTypeCtx ((S.drop (S.length - (ts.length + 1))).take ts.length) lt
        | none => false) = true := by
      rw [List.all_eq_true]
      intro l hl
      have : ∃ lt, C.labels[l.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt := by
        rcases List.mem_cons.1 hl with rfl | hl
        · exact ⟨lt, hlt, hslt⟩
        · exact hls l hl
      obtain ⟨lt2, h2, hs2'⟩ := this
      simp only [h2]
      exact resSub_complete hΔ hr' hXok (hC.label h2) (ResultSub.trans hΔ htsok hA hs2')
    rw [hlt]
    dsimp only
    rw [hm, ite_eq_left hl2]
    try dsimp only
    rw [hres, ite_eq_left (by rw [Bool.true_and]; exact hall)]
    have hXl : ((S.drop (S.length - (ts.length + 1))).take ts.length).length = ts.length := by
      simp; omega
    have hsubX : ResultSub C.toTypeCtx
        (S.drop (S.length - ((S.drop (S.length - (ts.length + 1))).take ts.length ++ [Ty.i32]).length))
        ((S.drop (S.length - (ts.length + 1))).take ts.length ++ [Ty.i32]) := by
      rw [List.length_append, hXl, List.length_singleton]
      conv => lhs; rw [← List.take_append_drop ts.length (S.drop (S.length - (ts.length + 1)))]
      exact ResultSub.append (ResultSub.refl _ _) hB
    refine ⟨_, stepB_complete hΔ hr' hS (ResultOk.append hXok (resultOk_i32 _))
      (by simp [hXl]; omega) hsubX, ?_⟩
    simp [hXl]
  · -- br_on_null
    cases hi with
    | @brOnNull _ _ ts ht hl hh => ?_
    | _ => (rename_i h; cases h)
    obtain ⟨hA, hB⟩ := sub_split hsub
    generalize hDd : (List.drop (S.length - (ts ++ [Ty.refT true ht]).length) S).drop ts.length
      = Y at hB
    rcases hB with _ | ⟨hb, hnil⟩
    cases hnil
    rename_i b
    have hbmem : b ∈ S :=
      List.mem_of_mem_drop (List.mem_of_mem_drop (hDd ▸ List.mem_singleton_self b))
    have hlast : S.getLast? = some b := by
      have hDd2 := hDd
      rw [List.drop_drop] at hDd2
      rw [← List.take_append_drop _ S, hDd2]; simp
    have hbok := hS b hbmem
    obtain ⟨h₁, htop, hh₁, hb₁, h₁s⟩ : ∃ h₁, topHeap S = some h₁ ∧ TyOk C.toTypeCtx h₁ ∧
        Sub C.toTypeCtx b (Ty.refT true h₁) ∧ Sub C.toTypeCtx h₁ ht := by
      simp only [Ty.refT] at hb
      cases hb with
      | refv hr0 =>
        cases hr0 with
        | refNull hh' =>
          rename_i n h₁
          refine ⟨h₁, by simp [topHeap, hlast], ?_, .refv (.refNull .heapRefl), hh'⟩
          cases hbok with | refv h => cases h with | ref h => exact h
      | botv => exact ⟨.bot, by simp [topHeap, hlast], .bot, .botv, .bot⟩
    rw [hl, htop]
    dsimp only
    rw [ite_eq_left (htyOk _ _ _ hΔ hr' hh₁)]
    have hlenEq : (ts ++ [Ty.refT true h₁]).length = (ts ++ [Ty.refT true ht]).length := by simp
    have htsok : ResultOk C.toTypeCtx ts := hC.label hl
    have hsub' : ResultSub C.toTypeCtx (S.drop (S.length - (ts ++ [Ty.refT true h₁]).length))
        (ts ++ [Ty.refT true h₁]) := by
      rw [hlenEq, ← List.take_append_drop ts.length
        (List.drop (S.length - (ts ++ [Ty.refT true ht]).length) S), hDd]
      exact ResultSub.append hA (.cons hb₁ .nil)
    refine ⟨_, stepA_complete hΔ hr' hS (ResultOk.append htsok (by simpa [ResultOk] using hh₁))
      (hlenEq ▸ hlen) hsub', by simp, rfl, ResultOk.append htsok (by simpa [ResultOk] using hh₁),
      ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNonNull h₁s)) .nil)⟩
  · -- br_on_non_null
    cases hi with
    | brOnNonNull hl => ?_
    | _ => (rename_i h; cases h)
    simp only [hl, splitLast_append, Ty.refT]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- br_on_cast
    cases hi with
    | @brOnCast _ _ _ _ _ rt hl h₁ h₂ h₂₁ h₂l => ?_
    | _ => (rename_i h; cases h)
    have hrt : TyOk C.toTypeCtx rt := by
      have := (hC.label hl) (.refv rt) (by simp)
      simpa using this
    simp only [hl, splitLast_append]
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨htyOk _ _ _ hΔ hr' h₁, htyOk _ _ _ hΔ hr' h₂⟩,
        Sub.check_complete hΔ hr' h₂₁ h₂ h₁⟩, Sub.check_complete hΔ hr' h₂l h₂ hrt⟩)]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- br_on_cast_fail
    cases hi with
    | @brOnCastFail _ _ _ _ _ rt hl h₁ h₂ h₂₁ hdl => ?_
    | _ => (rename_i h; cases h)
    have hrt : TyOk C.toTypeCtx rt := by
      have := (hC.label hl) (.refv rt) (by simp)
      simpa using this
    simp only [hl, splitLast_append]
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨htyOk _ _ _ hΔ hr' h₁, htyOk _ _ _ hΔ hr' h₂⟩,
        Sub.check_complete hΔ hr' h₂₁ h₂ h₁⟩,
        Sub.check_complete hΔ hr' hdl (TyOk.diffrt h₁) hrt⟩)]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- call
    cases hi with
    | call hf he => ?_
    | _ => (rename_i h; cases h)
    rw [hf]
    dsimp only
    rw [funcOfDef?_complete he]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- call_ref
    cases hi with
    | callRef hd he => ?_
    | _ => (rename_i h; cases h)
    rw [hd]
    dsimp only
    rw [funcOfDef?_complete he]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- call_indirect
    cases hi with
    | @callIndirect _ _ _ _ _ rt _ _ _ htt hs hd he => ?_
    | _ => (rename_i h; cases h)
    have hrt : TyOk C.toTypeCtx rt := hC.tables _ (List.mem_of_getElem? htt)
    rw [htt, hd]
    dsimp only
    rw [ite_eq_left (Sub.check_complete hΔ hr' hs hrt (.ref (.abs _))), funcOfDef?_complete he]
    exact ⟨_, stepA_complete hΔ hr' hS hreg.1 hlen hsub, rfl, rfl, hreg.2.1, ResultSub.refl _ _⟩
  · -- return
    cases hi with
    | return_ hrt _ => ?_
    | _ => (rename_i h; cases h)
    rw [hrt]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (hC.return_ _ hrt) hl2 hs2, by simp⟩
  · -- return_call
    cases hi with
    | returnCall hf he hrt hs _ => ?_
    | _ => (rename_i h; cases h)
    have hrs := (Expand.func_ok (hC.funcs _ (List.mem_of_getElem? hf)) he).2
    rw [hf, hrt]
    dsimp only
    rw [funcOfDef?_complete he]
    dsimp only
    rw [ite_eq_left (resSub_complete hΔ hr' hrs (hC.return_ _ hrt) hs)]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (ResultOk.right hreg.1) hl2 hs2, by simp⟩
  · -- return_call_ref
    cases hi with
    | returnCallRef hd he hrt hs _ => ?_
    | _ => (rename_i h; cases h)
    have hrs := (Expand.func_ok (hC.type hd) he).2
    rw [List.append_assoc] at hlen hsub hreg
    rw [hd, hrt]
    dsimp only
    rw [funcOfDef?_complete he]
    dsimp only
    rw [ite_eq_left (resSub_complete hΔ hr' hrs (hC.return_ _ hrt) hs)]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (ResultOk.right hreg.1) hl2 hs2, by simp⟩
  · -- return_call_indirect
    cases hi with
    | @returnCallIndirect _ _ _ _ _ rt _ _ _ _ _ _ htt hs hd he hrt hrs' _ => ?_
    | _ => (rename_i h; cases h)
    have hrtok : TyOk C.toTypeCtx rt := hC.tables _ (List.mem_of_getElem? htt)
    have hrs := (Expand.func_ok (hC.type hd) he).2
    rw [List.append_assoc] at hlen hsub hreg
    rw [htt, hd, hrt]
    dsimp only
    rw [ite_eq_left (Sub.check_complete hΔ hr' hs hrtok (.ref (.abs _))), funcOfDef?_complete he]
    dsimp only
    rw [ite_eq_left (resSub_complete hΔ hr' hrs (hC.return_ _ hrt) hrs')]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (ResultOk.right hreg.1) hl2 hs2, by simp⟩
  · -- throw
    cases hi with
    | throw hx he _ => ?_
    | _ => (rename_i h; cases h)
    rw [tagParams?_complete hx he]
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (ResultOk.right hreg.1) hl2 hs2, by simp⟩
  · -- throw_ref
    cases hi with
    | throwRef _ => ?_
    | _ => (rename_i h; cases h)
    obtain ⟨hl2, hs2⟩ := top_suffix hlen hsub
    exact ⟨_, stepB_complete hΔ hr' hS (ResultOk.right hreg.1) hl2 hs2, by simp⟩
  · -- atoms
    rename_i _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    have hctl : isCtl i = false := by
      unfold isCtl
      split <;> first | rfl | (exfalso; simp_all)
    obtain ⟨out, ha, ho, hs⟩ := hatom C S i t₁ t₂ xs hC hr hctl hsel hi hS hlen hsub
    rw [ha]
    exact ⟨_, rfl, rfl, rfl, ho, hs⟩

end Silmaril.Wasm.Validation
