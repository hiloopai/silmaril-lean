module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Ctl.Congr

/-!
# Equivalence in context: loops and typing facts

* **`CEquiv.loop`**: two loops (no parameters) whose bodies are equivalent in typed contexts
  have the same partial-correctness weakest precondition (`PEquiv`). The proof is Löb
  induction on the step index of `HWP`: one unfolding of the right loop is its label around
  the right body; the right body is equivalent to the left one for the label's postcondition,
  whose back edge is the left loop, which is safe for fewer steps by the induction hypothesis.
  The back edges must leave the locals typed (`KeepsBr0`), so that the body equivalence applies
  at the next iteration;
* `KeepsBr0.of_cequiv`: the typing fact transfers along `CEquiv`;
* `Keeps.of_sexec`: symbolically executed straight-line code keeps typed states;
  `Keeps.append`: typing facts compose.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem typedVals_nil : TypedVals [] [] := ⟨rfl, fun _ hi => absurd hi (by simp)⟩

theorem TypedVals.cons {t : IntType} {ts : List IntType} {v : Val} {vs : List Val}
    (x : BitVec t.width) (hv : v = .num ⟨.int t, x⟩) (h : TypedVals ts vs) :
    TypedVals (t :: ts) (v :: vs) :=
  ⟨by simp [h.1], fun i hi => match i with
    | 0 => ⟨x, hv⟩
    | i + 1 => h.2 i (by simpa using hi)⟩

theorem noFuncTop_nil : NoFuncTop [] := fun _ h => by simp at h

/-- Equivalent bodies on an empty stack, for any postcondition. -/
theorem CEquiv.body_iff {lt : List IntType} {a b : List Instr} (h : CEquiv lt [] a b)
    {m : Corr} {s : Store H} {f : Frame} {Q : Post H} (hf : TypedFrame lt f) :
    Wp m P host s f (expression a) Q ↔ Wp m P host s f (expression b) Q := by
  have := h m P host s f [] [] [] Q hf typedVals_nil noFuncTop_nil
  simpa [cfgCode] using this

/-- The typing fact at back edges transfers along `CEquiv`. -/
theorem KeepsBr0.of_cequiv {lt : List IntType} {a b : List Instr} (hk : KeepsBr0 lt a)
    (h : CEquiv lt [] a b) : KeepsBr0 lt b := by
  intro P H host s f Q hf hb
  have ha : HWP P host s f (expression a) Q := (CEquiv.body_iff h (m := .part) hf).mpr hb
  exact (CEquiv.body_iff h (m := .part) hf).mp (hk P host s f Q hf ha)

theorem loop_step {s : Store H} {f : Frame} {us : List Val} {bt : BlockType} {a : List Instr}
    {t₂ : List Validation.CValType} (ht : f.module.blockType? bt = some ([], t₂)) :
    Step P host ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩
      ⟨s, f, vals us ++ [.label 0 [.loop bt a] (expression a)]⟩ := by
  simpa using Sim.Step.vals_left (Step.loop (P := P) (host := host) (s := s) (f := f) (body := a)
    (vs := []) ht rfl) us

/-- **Löb induction for the loop congruence.** -/
theorem safe_loop_congr {lt : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) (n : Nat) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      TypedFrame lt f → NoFuncTop us → HWP P host s f (vals us ++ [.plain (.loop bt a)]) Q →
      Safe P host Q n ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f us Q hf hus hw
  rcases n with _ | n
  · trivial
  obtain ⟨t₂, ht⟩ := hbt f.module
  have hbA : HWP P host s f (expression a) (labelPost P host 0 [.loop bt a] us Q) :=
    hwp_label_inv hus (hw.step_inv (loop_step ht))
  have hbB : HWP P host s f (expression b) (TypedBr0 lt (labelPost P host 0 [.loop bt a] us Q)) :=
    (CEquiv.body_iff h (m := .part) hf).mp (hk P host s f _ hf hbA)
  refine Safe.head ⟨rfl, by simp, rfl⟩ ⟨us, [], _, by simp, .loop ht rfl⟩ ?_
  intro us' args c₀ hW hh
  obtain ⟨t₁', t₂', hbt', hn', rfl⟩ := head_loop hh
  obtain ⟨rfl, rfl⟩ : t₁' = [] ∧ t₂' = t₂ := by simpa [ht] using hbt'.symm
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hn'
  subst hargs
  have hus' : us' = us := by simpa using hW.symm
  subst hus'
  rcases n with _ | k
  · trivial
  have hb : Safe P host (labelPostK P host 0 [.loop bt b] us' Q k) (k + 1)
      ⟨s, f, vals [] ++ expression b⟩ := by
    refine ((hbB (k + 1)).post_mono fun s' F o ho => ?_)
    rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | x | ⟨vs, x, c⟩
    · exact ho.1
    · obtain ⟨vs₁, vs₂, he, hn, hw'⟩ := ho.1
      have hv : vs₂ = [] := List.eq_nil_of_length_eq_zero hn
      subst hv
      refine ⟨vs₁, [], he, rfl, ?_⟩
      have := ih k (by omega) (ho.2 _ rfl) hus (by simpa [expression] using hw')
      simpa [expression] using this
    all_goals exact ho.1
  simpa using Safe.label (us := us') (k := k) le_rfl hb

/-- **Loops** (no parameters): equivalent bodies, typed at their back edges, give loops with
the same partial-correctness weakest precondition. -/
theorem CEquiv.loop {lt st : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) :
    PEquiv lt st [.loop bt a] [.loop bt b] := by
  intro P H host s f rs us rest Q hf hrs hus
  have hU := noFuncTop_append hus hrs
  have e : ∀ x : List Instr, cfgCode us rs [.loop bt x] rest =
      (vals (us ++ rs.reverse) ++ [.plain (.loop bt x)]) ++ rest := fun x => by
    simp [cfgCode, expression]
  rw [e, e]
  constructor
  · intro hw
    exact HWP.seq fun n => safe_loop_congr hbt h hk n hf hU (hwp_seq_inv hw)
  · intro hw
    exact HWP.seq fun n => safe_loop_congr hbt (CEquiv.symm h) (KeepsBr0.of_cequiv hk h) n hf hU (hwp_seq_inv hw)

/-! ## Typing facts -/

/-- Typing facts compose. -/
theorem Keeps.append {lt st lt' st' lt'' st'' : List IntType} {c d : List Instr}
    (hc : Keeps lt st c lt' st') (hd : Keeps lt' st' d lt'' st'') : Keeps lt st (c ++ d) lt'' st'' := by
  intro m P H host s f rs us Q hf hrs hw
  have e : cfgCode us rs (c ++ d) [] = cfgCode us rs c [] ++ expression d := by
    simp [cfgCode, expression]
  rw [e, wp_seq_iff] at hw ⊢
  refine wp_mono (fun s F o ho => ?_) (hc m P host s f rs us _ hf hrs hw)
  obtain ⟨hq, ht⟩ := ho
  rcases o with vs | _ | _ | _ | _ | _
  · obtain ⟨hF, rs', hrs', rfl⟩ := ht vs rfl
    have hq' : Wp m P host s F (cfgCode us rs' d []) Q := by
      simpa [cfgCode] using (seqPostM_normal (P := P) (host := host)).mp hq
    have := hd m P host s F rs' us Q hF hrs' hq'
    exact (seqPostM_normal (P := P) (host := host)).mpr (by simpa [cfgCode] using this)
  all_goals
    refine (seqPostM_ne_normal ?_).mpr ⟨(seqPostM_ne_normal ?_).mp hq, fun _ h => by cases h⟩ <;>
      intro vs h <;> cases h

theorem typedVals_map_den (ρ : Silmaril.Wasm.Auto.Equiv.Env) :
    ∀ l : List (IntType × Term), TypedVals (l.map Prod.fst) (l.map (den ρ))
  | [] => typedVals_nil
  | p :: l => TypedVals.cons (Silmaril.Wasm.Auto.Equiv.ev ρ p.1 p.2) rfl (typedVals_map_den ρ l)

/-- **Symbolically executed straight-line code keeps typed states.** -/
theorem Keeps.of_sexec {lt st : List IntType} {c : List Instr} {S : SState}
    (h : sexec (initState lt st) c = some S) :
    Keeps lt st c (S.locals.map Prod.fst) (S.stack.map Prod.fst) := by
  intro m P H host s f rs us Q hf hrs hw
  obtain ⟨ls, hls, hlt⟩ := hf
  have hF : frameAt f (envOfVals (ls ++ rs)) (initState lt st) = f := frameAt_envOfVals hls hlt
  have hS : stackAt (envOfVals (ls ++ rs)) (initState lt st) = rs := stackAt_envOfVals hlt hrs
  have hc : cfgCode us rs c [] = codeAt (envOfVals (ls ++ rs)) (initState lt st) us c [] := by
    simp [cfgCode, codeAt, hS]
  rw [hc, ← hF] at hw ⊢
  rw [wp_sexec_iff h, List.append_nil, wp_vals_iff] at hw ⊢
  refine ⟨hw, fun vs hvs => ?_⟩
  cases hvs
  refine ⟨⟨S.locals.map (den (envOfVals (ls ++ rs))), by simp [frameAt, List.map_map],
    typedVals_map_den _ _⟩, _, ?_, rfl⟩
  simpa [stackAt] using typedVals_map_den (envOfVals (ls ++ rs)) S.stack

/-- `br_if` keeps the frame. -/
theorem wp_brIf_frame {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} (hw : Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q) :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) (fun s' F o => Q s' F o ∧ F = f) := by
  have e₂ : ∀ x : Admin, vals (us ++ [.i32 c]) ++ [x] = vals us ++ [constI32 c, x] := fun x => by
    simp only [vals, List.map_append, List.map_cons, List.map_nil, constI32, List.append_assoc,
      List.cons_append, List.nil_append]
  by_cases hc0 : c = 0
  · show Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)])
      (fun s' F o => Q s' F o ∧ F = f)
    subst hc0
    have hst : Step P host ⟨s, f, vals (us ++ [.i32 0]) ++ [.plain (.brIf l)]⟩ ⟨s, f, vals us⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfFalse (P := P) (host := host) (s := s) (f := f) (l := l)) us
    have hq := wp_exit_post (wp_step_inv hw hst) (o := .normal us) rfl
    cases m
    · exact HWP.brIf (fun h => (h rfl).elim) (fun _ => by simpa using HWP.of_vals (Q := fun s' F o => Q s' F o ∧ F = f) ⟨hq, rfl⟩)
    · exact TWP.brIf (fun h => (h rfl).elim) (fun _ => by
        have := TSafe.exit (P := P) (host := host) (Q := fun s' F o => Q s' F o ∧ F = f)
          (c := ⟨s, f, vals us⟩) (.normal _) rfl ⟨hq, rfl⟩
        simpa [TWP] using this)
  · show Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)])
      (fun s' F o => Q s' F o ∧ F = f)
    have hst : Step P host ⟨s, f, vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]⟩
        ⟨s, f, vals us ++ [.plain (.br l)]⟩ := by
      rw [e₂]
      simpa using Sim.Step.vals_left (Step.brIfTrue (P := P) (host := host) (s := s) (f := f) (l := l) hc0) us
    have hex : Exits (.br l.toNat us) (vals us ++ [.plain (.br l)]) := ⟨l, [], rfl, rfl⟩
    have hq := wp_exit_post (wp_step_inv hw hst) hex
    cases m
    · exact HWP.brIf (fun _ => HWP.of_exits hex ⟨hq, rfl⟩) (fun h => (hc0 h).elim)
    · exact TWP.brIf (fun _ => ⟨hq, rfl⟩) (fun h => (hc0 h).elim)

/-- **Back edges of a `do … while` body**: straight-line code that keeps the local types and
leaves an `i32` on top, followed by `br_if`. -/
theorem KeepsBr0.of_sexec_brIf {lt : List IntType} {c : List Instr} {S : SState} {st' : List IntType}
    (l : LabelIdx) (h : sexec (initState lt []) c = some S) (hl : S.locals.map Prod.fst = lt)
    (hs : S.stack.map Prod.fst = .i32 :: st') : KeepsBr0 lt (c ++ [.brIf l]) := by
  intro P H host s f Q hf hw
  obtain ⟨ls, hls, hlt⟩ := hf
  have hF : frameAt f (envOfVals ls) (initState lt []) = f := by
    simpa using frameAt_envOfVals (st := []) (rs := []) hls hlt
  have hS : stackAt (envOfVals ls) (initState lt []) = [] := by
    simpa using stackAt_envOfVals (rs := []) hlt typedVals_nil
  have hc : expression (c ++ [.brIf l]) =
      codeAt (envOfVals ls) (initState lt []) [] c [.plain (.brIf l)] := by
    simp only [codeAt, hS, expression, List.map_append, List.map_cons, List.map_nil,
      List.reverse_nil, List.append_nil]
    rfl
  rw [hc, ← hF] at hw ⊢
  have hw' := (wp_sexec_iff (m := .part) h s f [] [.plain (.brIf l)]).mp hw
  refine (wp_sexec_iff (m := .part) h s f [] [.plain (.brIf l)]).mpr ?_
  have hty0 : TypedVals (.i32 :: st') (stackAt (envOfVals ls) S) := by
    have := typedVals_map_den (envOfVals ls) S.stack
    rw [hs] at this
    exact this
  obtain ⟨r, rs', hrs⟩ := TypedVals.cons_inv hty0
  have hty : TypedVals (.i32 :: st') (r :: rs') := hrs ▸ hty0
  obtain ⟨cv, rfl⟩ := TypedVals.head_i32 hty
  have e : vals ([] ++ (stackAt (envOfVals ls) S).reverse) ++ [.plain (.brIf l)] =
      vals (rs'.reverse ++ [.i32 cv]) ++ [.plain (.brIf l)] := by rw [hrs]; simp
  rw [e] at hw' ⊢
  refine HWP.mono (fun s' F o ho => ⟨ho.1, fun _ _ => ?_⟩) (wp_brIf_frame (m := .part) hw')
  rw [ho.2]
  exact ⟨S.locals.map (den (envOfVals ls)), by simp [frameAt, List.map_map],
    hl ▸ typedVals_map_den _ _⟩

/-- `KeepsBr0` from the decidable check `brIfBodyOk`. -/
theorem KeepsBr0.of_check {lt : List IntType} {c : List Instr} (l : LabelIdx)
    (h : brIfBodyOk lt c = true) : KeepsBr0 lt (c ++ [.brIf l]) := by
  unfold brIfBodyOk at h
  split at h
  · rename_i S hS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hl, hs⟩ := h
    obtain ⟨t, st', ht⟩ : ∃ t st', S.stack.map Prod.fst = t :: st' := by
      cases hx : S.stack.map Prod.fst with
      | nil => simp [hx] at hs
      | cons t st' => exact ⟨t, st', rfl⟩
    have : t = .i32 := by simpa [ht] using hs
    subst this
    exact KeepsBr0.of_sexec_brIf l hS hl ht
  · cases h

theorem noParams_empty : NoParams .empty := fun _ => ⟨[], rfl⟩

theorem noParams_value (t : ValType) : NoParams (.value t) := fun mi => ⟨[mi.instVal t], rfl⟩

end Silmaril.Proofs.Wasm.Auto.Equiv