module

public import Silmaril.Wasm.Auto.EquivUnroll.Defs
public import Silmaril.Wasm.Auto.EquivFn.Thms

/-!
# Loop unrolling by symbolic execution: soundness (unrefined)

* `wp_loop_iff`: a loop without parameters steps only to its label;
* `wp_brIf_iff`: `br_if` on a known condition;
* `wp_loop_xstep`: one iteration of a `do … while` loop entered with an empty stack is the body's
  symbolic run, then a trap at its first failing guard, the exit (condition `0`) or the next
  iteration (any other condition);
* **`wp_xsexecU`**: the unrolling executor gives the weakest precondition of the code as `XOut`
  of its final state, like `wp_xsexec`, for values below that do not end in a function reference;
* **`segEquivXN_of_checkXU`**: the equivalence check with unrolling is sound.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivUnroll

open Silmaril.Wasm.Auto.EquivUnroll
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (NoFuncTop wp_seq_iff wp_label_iff seqPostM_normal seqPostM_ne_normal
  labelPostM loop_step wp_step_inv wp_exit_post)
open Silmaril.Wasm.Auto.EquivFn (wp_iff_of_det)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem whileBody?_eq {b body : List Instr} (h : whileBody? b = some body) :
    ∃ l : LabelIdx, l.toNat = 0 ∧ b = body ++ [.brIf l] := by
  unfold whileBody? at h
  split at h
  · rename_i l hl
    split at h
    · rename_i h0
      cases h
      exact ⟨l, h0, (List.dropLast_append_getLast? (a := Instr.brIf l) (by simp [hl])).symm⟩
    · cases h
  · cases h

/-! ## Control steps -/

theorem wp_loop_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {b : List Instr}
    {rest : List Admin} {Q : Post H} :
    Wp m P host s f (vals us ++ .plain (.loop .empty b) :: rest) Q ↔
      Wp m P host s f (vals us ++ [.label 0 [.loop .empty b] (expression b)] ++ rest) Q := by
  obtain ⟨t₂, ht⟩ := Silmaril.Wasm.Auto.Equiv.noParams_empty f.module
  have hst : Step P host ⟨s, f, vals us ++ .plain (.loop .empty b) :: rest⟩
      ⟨s, f, vals us ++ [.label 0 [.loop .empty b] (expression b)] ++ rest⟩ := by
    have h₁ := Sim.Step.append_right (loop_step (P := P) (host := host) (s := s) (us := us) (a := b) ht) rest
    simpa using h₁
  refine wp_iff_of_det (c := ⟨s, f, _⟩) hst fun d hd => ?_
  obtain ⟨vs', args, c₀, hW, hh, rfl⟩ := SingleThreaded.inert_head_inv rfl (by simp) rfl hd
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
  obtain ⟨rfl, rfl⟩ : t₁' = [] ∧ t₂' = t₂ := by simpa [ht] using hbt'.symm
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hn'
  subst hargs
  have hus' : vs' = us := by simpa using hW.symm
  subst hus'
  simp

theorem wp_brIf_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔
      (if c = 0 then Q s f (.normal us) else Q s f (.br l.toNat us)) := by
  have e₂ : ∀ x : Admin, vals (us ++ [.i32 c]) ++ [x] = vals us ++ [constI32 c, x] := fun x => by
    simp only [vals, List.map_append, List.map_cons, List.map_nil, constI32, List.append_assoc,
      List.cons_append, List.nil_append]
  by_cases hc0 : c = 0
  · show Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔
        (if c = 0 then Q s f (.normal us) else Q s f (.br l.toNat us))
    subst hc0
    rw [ite_eq_left rfl]
    have hst : Step P host ⟨s, f, vals (us ++ [.i32 0]) ++ [.plain (.brIf l)]⟩ ⟨s, f, vals us⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfFalse (P := P) (host := host) (s := s) (f := f) (l := l)) us
    constructor
    · intro hw
      exact wp_exit_post (wp_step_inv hw hst) (o := .normal us) rfl
    · intro hq
      cases m
      · exact HWP.brIf (rest := []) (fun h => (h rfl).elim) (fun _ => by simpa using HWP.of_vals hq)
      · exact TWP.brIf (rest := []) (fun h => (h rfl).elim) (fun _ => by
          have := TSafe.exit (P := P) (host := host) (Q := Q) (c := ⟨s, f, vals us⟩) (.normal _) rfl hq
          simpa [TWP] using this)
  · show Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔
        (if c = 0 then Q s f (.normal us) else Q s f (.br l.toNat us))
    rw [ite_eq_right hc0]
    have hst : Step P host ⟨s, f, vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]⟩
        ⟨s, f, vals us ++ [.plain (.br l)]⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfTrue (P := P) (host := host) (s := s) (f := f) (l := l) hc0) us
    have hex : Exits (.br l.toNat us) (vals us ++ [.plain (.br l)]) := ⟨l, [], rfl, rfl⟩
    constructor
    · intro hw
      exact wp_exit_post (wp_step_inv hw hst) hex
    · intro hq
      cases m
      · exact HWP.brIf (rest := []) (fun _ => HWP.of_exits hex hq) (fun h => (hc0 h).elim)
      · exact TWP.brIf (rest := []) (fun _ => hq) (fun h => (hc0 h).elim)

theorem labelPostM_trap {m : Corr} {k : Nat} {cont : List Instr} {us : List Val} {Q : Post H}
    {s : Store H} {f : Frame} : labelPostM m P host k cont us Q s f .trap ↔ Q s f .trap := by
  cases m <;> exact Iff.rfl

theorem labelPostM_normal {m : Corr} {k : Nat} {cont : List Instr} {us vs : List Val} {Q : Post H}
    {s : Store H} {f : Frame} :
    labelPostM m P host k cont us Q s f (.normal vs) ↔ Q s f (.normal (us ++ vs)) := by
  cases m <;> exact Iff.rfl

theorem labelPostM_br0 {m : Corr} {cont : List Instr} {us V : List Val} {Q : Post H}
    {s : Store H} {f : Frame} :
    labelPostM m P host 0 cont us Q s f (.br 0 V) ↔ Wp m P host s f (vals us ++ expression cont) Q := by
  cases m
  · constructor
    · rintro ⟨vs₁, vs₂, -, hn, hw⟩
      have hv : vs₂ = [] := List.eq_nil_of_length_eq_zero hn
      subst hv
      simpa using hw
    · intro hw
      exact ⟨V, [], by simp, rfl, by simpa using hw⟩
  · constructor
    · rintro ⟨vs₁, vs₂, -, hn, hw⟩
      have hv : vs₂ = [] := List.eq_nil_of_length_eq_zero hn
      subst hv
      show TSafe P host Q ⟨s, f, vals us ++ expression cont⟩
      simpa using hw
    · intro hw
      have hw' : TSafe P host Q ⟨s, f, vals us ++ expression cont⟩ := hw
      exact ⟨V, [], by simp, rfl, by simpa using hw'⟩

theorem wp_brIf_zero {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} (hc : c = 0) :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔ Q s f (.normal us) := by
  rw [wp_brIf_iff, ite_eq_left hc]

theorem wp_brIf_ne {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} (hc : c ≠ 0) :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q ↔ Q s f (.br l.toNat us) := by
  rw [wp_brIf_iff, ite_eq_right hc]

/-! ## One iteration -/

theorem condConst_spec {ρ : Silmaril.Wasm.Auto.Equiv.Env} {B0 : ByteArray} {e : XT} {k : Nat}
    (hk : condConst? e = some k) : (evX ρ B0 .i32 e = 0 ↔ k = 0) := by
  unfold condConst? at hk
  split at hk
  · rename_i k₀ hc
    cases hk
    have hv : evX ρ B0 .i32 e = BitVec.ofNat 32 k₀ := by
      rw [← evX_canon .i32 e, hc]
      rfl
    rw [hv]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa [IntType.width] using this
    · intro h
      apply BitVec.eq_of_toNat_eq
      simpa [IntType.width] using h
  · cases hk

/-- **One iteration of a `do … while` loop.** -/
theorem wp_loop_xstep {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) {us : List Val}
    (hus : NoFuncTop us) {rest : List Admin} {Q : Post H} {S S₁ : XState} {b body : List Instr}
    {e : XT} {st' : List (IntType × XT)} {k : Nat}
    (hS : S.stack = []) (hl : S.globs.length = c.ga.length)
    (hf : firstFail c.ρ c.mi.bytes S.guards = none)
    (hb : whileBody? b = some body) (hr : xsexec mem S body = some S₁)
    (h₁ : S₁.stack = (.i32, e) :: st') (hk : condConst? e = some k) :
    Wp m P host (c.storeOf mem S) (c.frameOf S)
        (vals (us ++ (c.stackOf S).reverse) ++ .plain (.loop .empty b) :: rest) Q ↔
      match firstFail c.ρ c.mi.bytes S₁.guards with
      | some T => Q (c.storeOf mem T) (c.frameOf T) .trap
      | none =>
        if k = 0 then
          Wp m P host (c.storeOf mem S₁) (c.frameOf S₁)
            (vals (us ++ (c.stackOf { S₁ with stack := st' }).reverse) ++ rest) Q
        else
          Wp m P host (c.storeOf mem S₁) (c.frameOf S₁)
            (vals (us ++ (c.stackOf { S₁ with stack := [] }).reverse) ++ .plain (.loop .empty b) :: rest) Q := by
  have hsS : c.stackOf S = [] := by simp [XCtx.stackOf, hS]
  obtain ⟨l, hl0, rfl⟩ := whileBody?_eq hb
  rw [hsS, List.reverse_nil, List.append_nil, wp_loop_iff, wp_seq_iff, wp_label_iff hus]
  have hex : expression (body ++ [.brIf l]) =
      vals ([] ++ (c.stackOf S).reverse) ++ expression body ++ [.plain (.brIf l)] := by
    simp [hsS, expression]
  rw [hex, wp_xsexec hc [] [.plain (.brIf l)] _ body hl hf hr]
  unfold XOut
  cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
  | some T =>
    simp only
    rw [labelPostM_trap, seqPostM_ne_normal (fun vs h => Outcome.noConfusion h)]
  | none =>
    simp only
    have hstack : vals ([] ++ (c.stackOf S₁).reverse) ++ [Admin.plain (.brIf l)] =
        vals ((c.stackOf { S₁ with stack := st' }).reverse ++ [.i32 (evX c.ρ c.mi.bytes .i32 e)]) ++
          [.plain (.brIf l)] := by
      simp [XCtx.stackOf, h₁, denX, Val.i32]
    rw [hstack]
    have hv : ((evX c.ρ c.mi.bytes .i32 e : BitVec 32) = 0) ↔ k = 0 :=
      condConst_spec (ρ := c.ρ) (B0 := c.mi.bytes) hk
    by_cases hk0 : k = 0
    · rw [wp_brIf_zero (hv.mpr hk0), ite_eq_left hk0,
        labelPostM_normal, seqPostM_normal]
    · rw [wp_brIf_ne (mt hv.mp hk0), ite_eq_right hk0, hl0,
        labelPostM_br0, ← wp_seq_iff]
      have e₂ : vals us ++ expression [Instr.loop .empty (body ++ [.brIf l])] ++ rest =
          vals (us ++ (c.stackOf { S₁ with stack := [] }).reverse) ++
            .plain (.loop .empty (body ++ [.brIf l])) :: rest := by
        simp [XCtx.stackOf, expression]
      rw [e₂]

/-! ## Runs -/

theorem xsexecU_guards {mem : Bool} : ∀ (fuel : Nat) {S S' : XState} {a : List Instr},
    xsexecU mem fuel S a = some S' → ∃ G, S'.guards = S.guards ++ G
  | _, S, S', [], h => by
    unfold xsexecU at h
    cases h
    exact ⟨[], by simp⟩
  | 0, _, _, _ :: _, h => by unfold xsexecU at h; cases h
  | f + 1, S, S', i :: is, h => by
    unfold xsexecU at h
    split at h
    · split at h
      · split at h
        · rename_i S₁ hr
          split at h
          · obtain ⟨G₁, hG₁⟩ := xsexec_guards hr
            split at h
            · obtain ⟨G, hG⟩ := xsexecU_guards f h
              exact ⟨G₁ ++ G, by rw [hG]; simp [hG₁]⟩
            · obtain ⟨G, hG⟩ := xsexecU_guards f h
              exact ⟨G₁ ++ G, by rw [hG]; simp [hG₁]⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i S₁ hs
        obtain ⟨G, hG⟩ := xsexecU_guards f h
        obtain ⟨G₁, hG₁⟩ := xsexec_guards (mem := mem) (S := S) (S' := S₁) (a := [i]) (by simp [xsexec, hs])
        exact ⟨G₁ ++ G, by rw [hG, hG₁]; simp⟩
      · cases h

/-- A trap before the end of a run is the run's trap. -/
theorem xout_of_fail {m : Corr} {mem : Bool} {c : XCtx H} {us : List Val} {rest : List Admin}
    {Q : Post H} {S₁ S' : XState} {T : XState} (hT : firstFail c.ρ c.mi.bytes S₁.guards = some T)
    (hG : ∃ G, S'.guards = S₁.guards ++ G) :
    XOut m P host c mem S' us rest Q ↔ Q (c.storeOf mem T) (c.frameOf T) .trap := by
  obtain ⟨G, hG⟩ := hG
  have hf : firstFail c.ρ c.mi.bytes S'.guards = some T := by
    rw [hG]
    exact firstFail_append_some G hT
  simp only [XOut, hf]

/-- **The unrolling executor is sound.** -/
theorem wp_xsexecU {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) (us : List Val)
    (hus : NoFuncTop us) (rest : List Admin) (Q : Post H) :
    ∀ (fuel : Nat) (a : List Instr) {S S' : XState}, S.globs.length = c.ga.length →
      firstFail c.ρ c.mi.bytes S.guards = none → xsexecU mem fuel S a = some S' →
      (Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ expression a ++ rest) Q ↔
        XOut m P host c mem S' us rest Q)
  | _, [], S, S', _, hf, h => by
    unfold xsexecU at h
    cases h
    simp [XOut, hf, expression]
  | 0, _ :: _, _, _, _, _, h => by unfold xsexecU at h; cases h
  | f + 1, i :: is, S, S', hl, hf, h => by
    have e : vals (us ++ (c.stackOf S).reverse) ++ expression (i :: is) ++ rest =
        vals (us ++ (c.stackOf S).reverse) ++ .plain i :: (expression is ++ rest) := by
      simp [expression]
    rw [e]
    unfold xsexecU at h
    split at h
    · rename_i b
      split at h
      · rename_i body hS hb
        split at h
        · rename_i S₁ hr
          split at h
          · rename_i e₀ st' h₁
            have hl₁ : S₁.globs.length = c.ga.length := by rw [xsexec_globs hr, hl]
            split at h
            · rename_i hk
              rw [wp_loop_xstep hc hus hS hl hf hb hr h₁ hk]
              cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
              | some T =>
                simp only
                exact (xout_of_fail hT (by
                  obtain ⟨G, hG⟩ := xsexecU_guards f h
                  exact ⟨G, hG⟩)).symm
              | none =>
                simp only [↓reduceIte]
                have := wp_xsexecU (m := m) hc us hus rest Q f is (S := { S₁ with stack := st' }) hl₁ hT h
                rw [← this]
                simp [expression]
                rfl
            · rename_i n hk
              rw [wp_loop_xstep hc hus hS hl hf hb hr h₁ hk]
              cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
              | some T =>
                simp only
                exact (xout_of_fail hT (by
                  obtain ⟨G, hG⟩ := xsexecU_guards f h
                  exact ⟨G, hG⟩)).symm
              | none =>
                simp only [Nat.add_one_ne_zero, ↓reduceIte]
                have := wp_xsexecU (m := m) hc us hus rest Q f (.loop .empty b :: is)
                  (S := { S₁ with stack := [] }) hl₁ hT h
                rw [← this]
                simp [expression]
                rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · split at h
      · rename_i S₁ hs
        have hx : xsexec mem S [i] = some S₁ := by simp [xsexec, hs]
        have h₀ := wp_xsexec (m := m) (P := P) (host := host) hc us (expression is ++ rest) Q [i] hl hf hx
        have e' : vals (us ++ (c.stackOf S).reverse) ++ expression [i] ++ (expression is ++ rest) =
            vals (us ++ (c.stackOf S).reverse) ++ .plain i :: (expression is ++ rest) := by
          simp [expression]
        rw [e'] at h₀
        rw [h₀]
        have hl₁ : S₁.globs.length = c.ga.length := by rw [xsexec_globs hx, hl]
        unfold XOut
        cases hT : firstFail c.ρ c.mi.bytes S₁.guards with
        | some T =>
          simp only
          obtain ⟨G, hG⟩ := xsexecU_guards f h
          have hf' : firstFail c.ρ c.mi.bytes S'.guards = some T := by
            rw [hG]
            exact firstFail_append_some G hT
          simp only [hf']
        | none =>
          simp only
          have := wp_xsexecU (m := m) hc us hus rest Q f is hl₁ hT h
          rw [← List.append_assoc]
          exact this
      · cases h

/-- A symbolic run with unrolling from the initial state of a typed context: the weakest
precondition of the segment is that of the run's outcome. -/
theorem wp_init_iffU {m : Corr} {c : XCtx H} {lt st gt : List IntType} {mem : Bool} {fuel : Nat}
    (hc : c.Ok lt st gt mem) {us : List Val} (hus : NoFuncTop us) (rest : List Admin) (Q : Post H)
    {x : List Instr} {X : XState} (hx : xsexecU mem fuel (initX lt st gt) x = some X) :
    Wp m P host c.s c.f (c.code lt st gt us x rest) Q ↔ XOut m P host c mem X us rest Q := by
  have h₀ := wp_xsexecU (m := m) (P := P) (host := host) hc.good us hus rest Q fuel x
    (S := initX lt st gt) (by simp [initX, hc.2.2.1]) rfl hx
  rw [hc.1, hc.2.1] at h₀
  exact h₀

/-- Two runs with the same guard keys, keys and canonical stacks have the same outcomes. -/
theorem xout_iff_of_keys {m : Corr} {c : XCtx H} {mem : Bool} {A B : XState} {us : List Val}
    {rest : List Admin} {Q : Post H} (hgk : guardKeys A = guardKeys B) (hk : A.key = B.key)
    (hs : canonSlots A.stack = canonSlots B.stack) :
    XOut m P host c mem A us rest Q ↔ XOut m P host c mem B us rest Q := by
  obtain ⟨hl, hgl, hm⟩ := key_eq_parts hk
  unfold XOut
  rcases firstFail_of_keys (ρ := c.ρ) (B0 := c.mi.bytes) hgk with ⟨hA, hB⟩ | ⟨T, T', hA, hB, hT⟩
  · simp only [hA, hB]
    rw [frameOf_eq_of_key c hl, storeOf_eq_of_key c mem hgl hm, stackOf_eq c hs]
  · simp only [hA, hB]
    obtain ⟨hl', hgl', hm'⟩ := key_eq_parts hT
    rw [frameOf_eq_of_key c hl', storeOf_eq_of_key c mem hgl' hm']

/-- **The equivalence check with unrolling is sound.** -/
theorem segEquivXN_of_checkXU {fuel : Nat} {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkXU fuel lt st gt mem a b = true) : SegEquivXN lt st gt mem a b := by
  intro m P H host c us rest Q hc hus
  cases ha : xsexecU mem fuel (initX lt st gt) a with
  | none => simp [checkXU, ha] at h
  | some A =>
    cases hb : xsexecU mem fuel (initX lt st gt) b with
    | none => simp [checkXU, ha, hb] at h
    | some B =>
      have h' : (guardKeys A = guardKeys B ∧ A.key = B.key) ∧
          canonSlots A.stack = canonSlots B.stack := by
        simpa only [checkXU, ha, hb, Bool.and_eq_true, decide_eq_true_eq] using h
      obtain ⟨⟨hgk, hk⟩, hs⟩ := h'
      rw [wp_init_iffU hc hus rest Q ha, wp_init_iffU hc hus rest Q hb]
      exact xout_iff_of_keys hgk hk hs

end Silmaril.Proofs.Wasm.Auto.EquivUnroll
