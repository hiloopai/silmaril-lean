module

public import Silmaril.Wasm.SingleThreaded.Thread

@[expose] public section

/-! # Step inversion for the single-threaded presentation

* `Step.noRedex`: the left-hand side of a host-free Core step has no host-call
  redex (`decompose?` is `none`, even under a value prefix and any suffix);
* `Step.not_quiet`: the left-hand side of any Core step is not a value sequence,
  a trap, or an uncaught `throw_ref` at the top.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Codes with no host-call redex under any value prefix and suffix. -/
def NoRedex (s : Store H) (l : List Admin) : Prop :=
  ∀ pre rest, decompose? s (vals pre ++ l ++ rest) = none

theorem splitVals_append_of_cons {l : List Admin} {ws : List Val} {d : Admin} {r : List Admin}
    (hs : splitVals l = (ws, d :: r)) (pre : List Val) (rest : List Admin) :
    splitVals (vals pre ++ l ++ rest) = (pre ++ ws, d :: (r ++ rest)) := by
  obtain ⟨hl, hd⟩ := splitVals_eq hs
  subst hl
  rw [show vals pre ++ (vals ws ++ d :: r) ++ rest = vals (pre ++ ws) ++ d :: (r ++ rest) by simp,
    splitVals_vals_cons hd]

theorem noRedex_of_split {s : Store H} {l : List Admin} {ws : List Val} {d : Admin}
    {r : List Admin} (hs : splitVals l = (ws, d :: r))
    (hh : ∀ vs rest, decompHead s vs d rest = none) : NoRedex s l := by
  intro pre rest
  rw [decompose?_of_split (splitVals_append_of_cons hs pre rest)]
  exact hh _ _

theorem splitVals_cons_plain_val {i : Instr} {v : Val} (h : (Admin.plain i).val? = some v)
    (as : List Admin) :
    splitVals (.plain i :: as) = (v :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val h as

@[simp] theorem splitVals_toAdmin_cons (v : Val) (as : List Admin) :
    splitVals (v.toAdmin :: as) = (v :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val (Admin.val?_toAdmin v) as

@[simp] theorem splitVals_ref_cons (r : Ref) (as : List Admin) :
    splitVals (.ref r :: as) = (.ref r :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val rfl as

@[simp] theorem splitVals_nil' : splitVals [] = ([], []) := rfl

@[simp] theorem splitVals_intConst_cons (t : IntType) (x : BitVec t.width) (as : List Admin) :
    splitVals (.plain (.intConst t x) :: as) =
      (.num ⟨.int t, x⟩ :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val rfl as

@[simp] theorem splitVals_floatConst_cons (t : FloatType) (x : BitVec t.width) (as : List Admin) :
    splitVals (.plain (.floatConst t x) :: as) =
      (.num ⟨.float t, x⟩ :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val rfl as

@[simp] theorem splitVals_vecConst_cons (x : V128) (as : List Admin) :
    splitVals (.plain (.vecConst x) :: as) = (.vec x :: (splitVals as).1, (splitVals as).2) :=
  splitVals_cons_val rfl as

theorem splitVals_plain_cons_nonval {i : Instr} (h1 : ∀ t x, i ≠ .intConst t x)
    (h2 : ∀ t x, i ≠ .floatConst t x) (h3 : ∀ x, i ≠ .vecConst x) (as : List Admin) :
    splitVals (.plain i :: as) = ([], .plain i :: as) := by
  apply splitVals_cons_nonval
  unfold Admin.val?
  split
  · rename_i t x heq; cases heq; exact absurd rfl (h1 t x)
  · rename_i t x heq; cases heq; exact absurd rfl (h2 t x)
  · rename_i x heq; cases heq; exact absurd rfl (h3 x)
  · cases ‹Admin.plain i = Admin.ref _›
  · rfl

@[simp] theorem splitVals_label_cons (n : Nat) (cont : List Instr) (b as : List Admin) :
    splitVals (.label n cont b :: as) = ([], .label n cont b :: as) := splitVals_cons_nonval rfl as

@[simp] theorem splitVals_handler_cons (n : Nat) (cs : List Catch) (b as : List Admin) :
    splitVals (.handler n cs b :: as) = ([], .handler n cs b :: as) := splitVals_cons_nonval rfl as

@[simp] theorem splitVals_frame_cons (n : Nat) (f : Frame) (b as : List Admin) :
    splitVals (.frame n f b :: as) = ([], .frame n f b :: as) := splitVals_cons_nonval rfl as

@[simp] theorem splitVals_callRefType_cons (d : DefType) (as : List Admin) :
    splitVals (.callRefType d :: as) = ([], .callRefType d :: as) := splitVals_cons_nonval rfl as

@[simp] theorem splitVals_returnCallRefType_cons (d : DefType) (as : List Admin) :
    splitVals (.returnCallRefType d :: as) = ([], .returnCallRefType d :: as) :=
  splitVals_cons_nonval rfl as

@[simp] theorem splitVals_trap_cons (as : List Admin) :
    splitVals (.trap :: as) = ([], .trap :: as) := splitVals_cons_nonval rfl as

/-- Closes `NoRedex s l` for a concrete `l` whose first non-value is inert. -/
macro "inert_tac" : tactic => `(tactic| (
  intro pre rest
  rw [decompose?_eq]
  simp [splitVals_plain_cons_nonval, splitVals_vals_append, splitVals_toAdmin_cons, splitVals_ref_cons,
    splitVals_intConst_cons, splitVals_floatConst_cons, splitVals_vecConst_cons,
    decompTop, decompHead, Admin.isCallRef, constI32]))


theorem decompHead_label (s : Store H) (vs : List Val) (n : Nat) (cont : List Instr)
    (body rest : List Admin) :
    decompHead s vs (.label n cont body) rest =
      (decompose? s body).map fun (E, a, h, args) => (.label vs n cont E rest, a, h, args) := rfl

theorem decompHead_handler (s : Store H) (vs : List Val) (n : Nat) (cs : List Catch)
    (body rest : List Admin) :
    decompHead s vs (.handler n cs body) rest =
      (decompose? s body).map fun (E, a, h, args) => (.handler vs n cs E rest, a, h, args) := rfl

theorem decompHead_frame (s : Store H) (vs : List Val) (n : Nat) (f : Frame)
    (body rest : List Admin) :
    decompHead s vs (.frame n f body) rest =
      (decompose? s body).map fun (E, a, h, args) => (.frame vs n f E rest, a, h, args) := rfl

/-- The layer lemma for a single structured instruction. -/
theorem noRedex_single {s : Store H} {d : Admin} (hd : d.val? = none)
    (hh : ∀ vs rest, decompHead s vs d rest = none) : NoRedex s [d] :=
  noRedex_of_split (splitVals_cons_nonval hd []) hh

theorem decompose?_none_of_noRedex {s : Store H} {l : List Admin} (h : NoRedex s l) :
    decompose? s l = none := by
  simpa [vals] using h [] []

theorem noRedex_label {s : Store H} {n : Nat} {cont : List Instr} {body : List Admin}
    (h : decompose? s body = none) : NoRedex s [.label n cont body] :=
  noRedex_single rfl (fun vs rest => by rw [decompHead_label, h]; rfl)

theorem noRedex_handler {s : Store H} {n : Nat} {cs : List Catch} {body : List Admin}
    (h : decompose? s body = none) : NoRedex s [.handler n cs body] :=
  noRedex_single rfl (fun vs rest => by rw [decompHead_handler, h]; rfl)

theorem noRedex_frame {s : Store H} {n : Nat} {f : Frame} {body : List Admin}
    (h : decompose? s body = none) : NoRedex s [.frame n f body] :=
  noRedex_single rfl (fun vs rest => by rw [decompHead_frame, h]; rfl)

/-- A code whose first non-value is `d`, with `d` never a redex head. -/
theorem decompose?_vals_cons_none {s : Store H} {vs : List Val} {d : Admin} {r : List Admin}
    (hd : d.val? = none) (hh : ∀ vs rest, decompHead s vs d rest = none) :
    decompose? s (vals vs ++ d :: r) = none := by
  rw [decompose?_of_split (splitVals_vals_cons hd r)]; exact hh _ _

theorem decompose?_vals_nil {s : Store H} {vs : List Val} : decompose? s (vals vs) = none :=
  decompose?_of_split_nil (splitVals_vals vs)

/-- `NoRedex` for `vals ws ++ d :: r` with an inert head `d`. -/
theorem noRedex_vals_cons {s : Store H} {ws : List Val} {d : Admin} {r : List Admin}
    (hd : d.val? = none) (hh : ∀ vs rest, decompHead s vs d rest = none) :
    NoRedex s (vals ws ++ d :: r) :=
  noRedex_of_split (splitVals_vals_cons hd r) hh

theorem decompHead_plain {s : Store H} {vs : List Val} {i : Instr} {rest : List Admin}
    (hi : (Admin.plain i).isCallRef = false) : decompHead s vs (.plain i) rest = none := by
  simp [decompHead, hi]

theorem decompHead_trap {s : Store H} {vs : List Val} {rest : List Admin} :
    decompHead s vs .trap rest = none := rfl

theorem decompHead_returnCallRef {s : Store H} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) : decompHead s vs c rest = none := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · rename_i x; exact decompHead_plain rfl
  · rfl
  · exact hc.elim

theorem val?_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : c.val? = none := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · rfl
  · rfl
  · exact hc.elim

theorem hostArity?_none_of_wasm {s : Store H} {a : Nat} {fi : FuncInst H} {code : Func}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) : hostArity? s a = none := by
  unfold hostArity?
  rw [hf]
  simp only [hcode]

/-- Left-hand sides of host-free steps have no host-call redex. -/
theorem Step.noRedex {P : Profile} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') : NoRedex c.store c.code := by
  induction h with
  | parametric h => cases h <;> inert_tac
  | numeric h => cases h <;> inert_tac
  | vector h => cases h <;> inert_tac
  | «variable» h => cases h <;> inert_tac
  | table h => cases h <;> inert_tac
  | memory h => cases h <;> inert_tac
  | reference h => cases h <;> inert_tac
  | aggregate h => cases h <;> inert_tac
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    intro pre rest'
    have := ih (pre ++ vs) (rest ++ rest')
    simpa [List.append_assoc] using this
  | ctxtLabel _ ih => exact noRedex_label (decompose?_none_of_noRedex ih)
  | ctxtHandler _ ih => exact noRedex_handler (decompose?_none_of_noRedex ih)
  | ctxtFrame _ ih => exact noRedex_frame (decompose?_none_of_noRedex ih)
  | labelVals => exact noRedex_label decompose?_vals_nil
  | handlerVals => exact noRedex_handler decompose?_vals_nil
  | frameVals _ => exact noRedex_frame decompose?_vals_nil
  | brLabelZero _ _ =>
    exact noRedex_label (by
      rw [← vals_append, List.append_assoc]
      exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_plain rfl))
  | brLabelSucc _ | returnLabel =>
    exact noRedex_label (by
      rw [List.append_assoc]
      exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_plain rfl))
  | brHandler | returnHandler =>
    exact noRedex_handler (by
      rw [List.append_assoc]
      exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_plain rfl))
  | returnFrame _ =>
    exact noRedex_frame (by
      rw [← vals_append, List.append_assoc]
      exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_plain rfl))
  | returnCallRefLabel hc =>
    exact noRedex_label (by
      rw [List.append_assoc]
      exact decompose?_vals_cons_none (val?_returnCallRef hc)
        (fun _ _ => decompHead_returnCallRef hc))
  | returnCallRefHandler hc =>
    exact noRedex_handler (by
      rw [List.append_assoc]
      exact decompose?_vals_cons_none (val?_returnCallRef hc)
        (fun _ _ => decompHead_returnCallRef hc))
  | returnCallRefFrameNull hc =>
    exact noRedex_frame (by
      rw [show ∀ (vs : List Val) (c : Admin) (rest : List Admin),
          vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest by
        intros; simp; rfl]
      exact decompose?_vals_cons_none (val?_returnCallRef hc)
        (fun _ _ => decompHead_returnCallRef hc))
  | returnCallRefFrameAddr hc =>
    exact noRedex_frame (by
      rw [show ∀ (vs' vs : List Val) (a : Nat) (c : Admin) (rest : List Admin),
          vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
            vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest by
        intros; simp; rfl]
      exact decompose?_vals_cons_none (val?_returnCallRef hc)
        (fun _ _ => decompHead_returnCallRef hc))
  | throwRefLabel => exact noRedex_label (decompose?_vals_cons_none (vs := [.ref (.exn _)])
      rfl (fun _ _ => decompHead_plain rfl))
  | throwRefFrame => exact noRedex_frame (decompose?_vals_cons_none (vs := [.ref (.exn _)])
      rfl (fun _ _ => decompHead_plain rfl))
  | throwRefHandlerEmpty | throwRefHandlerCatch _ _ | throwRefHandlerCatchRef _ _
    | throwRefHandlerCatchAll | throwRefHandlerCatchAllRef | throwRefHandlerNext _ =>
    exact noRedex_handler (decompose?_vals_cons_none (vs := [.ref (.exn _)])
      rfl (fun _ _ => decompHead_plain rfl))
  | trapLabel => exact noRedex_label (decompose?_vals_cons_none (vs := []) rfl
      (fun _ _ => decompHead_trap))
  | trapHandler => exact noRedex_handler (decompose?_vals_cons_none (vs := []) rfl
      (fun _ _ => decompHead_trap))
  | trapFrame => exact noRedex_frame (decompose?_vals_cons_none (vs := []) rfl
      (fun _ _ => decompHead_trap))
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | @callRefNull s f c hc =>
    intro pre rest
    rw [show vals pre ++ [Admin.ref .null, c] ++ rest = vals (pre ++ [.ref .null]) ++ c :: rest by
      simp; rfl]
    rw [decompose?_of_split (splitVals_vals_cons (Admin.val?_of_IsCallRef hc) _),
      decompHead_of_IsCallRef hc]
    simp [topRedex]
  | @callRefFunc s f c vs a fi ps rs code hc hf he hn hcode =>
    intro pre rest
    rw [show vals pre ++ (vals vs ++ [Admin.ref (.func a), c]) ++ rest =
      vals (pre ++ vs ++ [.ref (.func a)]) ++ c :: rest by simp; rfl]
    rw [decompose?_of_split (splitVals_vals_cons (Admin.val?_of_IsCallRef hc) _),
      decompHead_of_IsCallRef hc]
    simp [topRedex, hostArity?_none_of_wasm hf hcode]
  | throwRefInstrs _ =>
    intro pre rest
    rw [show ∀ (vs : List Val) (a : Nat) (r : List Admin),
        vals pre ++ (vals vs ++ throwing a ++ r) ++ rest =
          vals (pre ++ vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: (r ++ rest) by
      intros; simp [throwing]; rfl]
    exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_plain rfl)
  | trapInstrs _ =>
    intro pre rest
    rw [show ∀ (vs : List Val) (r : List Admin),
        vals pre ++ (vals vs ++ [Admin.trap] ++ r) ++ rest =
          vals (pre ++ vs) ++ Admin.trap :: (r ++ rest) by
      intros; simp]
    exact decompose?_vals_cons_none rfl (fun _ _ => decompHead_trap)
  | block _ _ | loop _ _ | tryTable _ _ | throw _ _ _ =>
    exact noRedex_vals_cons (r := []) rfl (fun _ _ => decompHead_plain rfl)
  | _ => inert_tac

/-! ## Quiet codes: values, a trap, an uncaught exception -/

/-- Codes that are values, a trap, a bare `throw_ref`, or an uncaught exception. -/
def Quiet (l : List Admin) : Prop :=
  (splitVals l).2 = [] ∨ splitVals l = ([], [.trap]) ∨ splitVals l = ([], [.plain .throwRef]) ∨
    ∃ a, splitVals l = ([.ref (.exn a)], [.plain .throwRef])

theorem quiet_vals (vs : List Val) : Quiet (vals vs) :=
  Or.inl (by rw [splitVals_vals])

theorem quiet_trap : Quiet [.trap] := Or.inr (Or.inl rfl)

theorem quiet_throwing (a : Nat) : Quiet (throwing a) := Or.inr (Or.inr (Or.inr ⟨a, rfl⟩))

/-- Closes `¬ Quiet l` for a concrete `l`. -/
macro "unquiet_tac" : tactic => `(tactic| (
  simp [splitVals_plain_cons_nonval, Quiet, splitVals_vals_append, splitVals_toAdmin_cons, splitVals_ref_cons,
    splitVals_intConst_cons, splitVals_floatConst_cons, splitVals_vecConst_cons,
    constI32, throwing]))

/-- Left-hand sides of steps are not quiet. -/
theorem Step.not_quiet {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : ¬ Quiet c.code := by
  induction h with
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    simp only at ih ⊢
    rcases hsp : splitVals is with ⟨ws, _ | ⟨d, r⟩⟩
    · exact absurd (Or.inl (by rw [hsp])) ih
    · have hw := splitVals_append_of_cons hsp vs rest
      rw [List.append_assoc] at hw ⊢
      rw [← List.append_assoc] at hw ⊢
      intro hq
      rcases hq with hq | hq | hq | ⟨a, hq⟩
      · rw [hw] at hq; cases hq
      · rw [hw] at hq
        simp only [Prod.mk.injEq, List.append_eq_nil_iff, List.cons.injEq] at hq
        obtain ⟨⟨rfl, rfl⟩, rfl, -, rfl⟩ := hq
        simp at hne
      · rw [hw] at hq
        simp only [Prod.mk.injEq, List.append_eq_nil_iff, List.cons.injEq] at hq
        obtain ⟨⟨rfl, rfl⟩, rfl, -, rfl⟩ := hq
        simp at hne
      · rw [hw] at hq
        simp only [Prod.mk.injEq, List.cons.injEq, List.append_eq_nil_iff] at hq
        obtain ⟨hvw, rfl, ⟨rfl, rfl⟩⟩ := hq
        have hvs : vs ≠ [] := by simpa using hne
        rcases List.append_eq_singleton_iff.mp hvw with ⟨rfl, -⟩ | ⟨-, rfl⟩
        · exact hvs rfl
        · exact ih (Or.inr (Or.inr (Or.inl hsp)))
  | @trapInstrs s f vs rest hne =>
    simp only [Quiet]
    rw [List.append_assoc, List.singleton_append, splitVals_vals_cons (d := .trap) rfl]
    rintro (hq | hq | hq | ⟨a, hq⟩) <;> simp_all
  | throwRefInstrs hne =>
    simp only [Quiet]
    rw [List.append_assoc, show ∀ (vs : List Val) (a : Nat) (r : List Admin),
        vals vs ++ (throwing a ++ r) = vals (vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: r by
      intros; simp [throwing]; rfl, splitVals_vals_cons (d := .plain .throwRef) rfl]
    rintro (hq | hq | hq | ⟨a', hq⟩)
    · simp at hq
    · simp at hq
    · simp at hq
    · simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hq
      obtain ⟨h1, h2⟩ := hq
      rcases List.append_eq_singleton_iff.mp h1 with ⟨rfl, -⟩ | ⟨-, h3⟩
      · simp_all
      · simp at h3
  | parametric h => cases h <;> unquiet_tac
  | numeric h => cases h <;> unquiet_tac
  | vector h => cases h <;> unquiet_tac
  | «variable» h => cases h <;> unquiet_tac
  | table h => cases h <;> unquiet_tac
  | memory h => cases h <;> unquiet_tac
  | reference h => cases h <;> unquiet_tac
  | aggregate h => cases h <;> unquiet_tac
  | callRefNull hc =>
    have h := splitVals_cons_nonval (Admin.val?_of_IsCallRef hc) []
    unquiet_tac
    simp [h]
  | callRefFunc hc =>
    have h := splitVals_cons_nonval (Admin.val?_of_IsCallRef hc) []
    unquiet_tac
    simp [h]
    rintro _ _ rfl
    exact hc
  | callRefHost hc =>
    have h := splitVals_cons_nonval (Admin.val?_of_IsCallRef hc) []
    unquiet_tac
    simp [h]
    rintro _ _ rfl
    exact hc
  | callRefHostDiv hc =>
    have h := splitVals_cons_nonval (Admin.val?_of_IsCallRef hc) []
    unquiet_tac
    simp [h]
    rintro _ _ rfl
    exact hc
  | _ => unquiet_tac

end Silmaril.Wasm.SingleThreaded
