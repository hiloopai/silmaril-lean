module

public import Silmaril.Raw.Wasm.Auto.Equiv.Ctl.Inv
public import Silmaril.Proofs.Wasm.Auto.Equiv.Basic

/-!
# Equivalence in context: congruence rules

From the inversion rules of `Silmaril.Raw.Wasm.Auto.Equiv.Ctl.Inv`:

* `wp_seq_iff`, `wp_label_iff`, `wp_plug_iff`: the weakest precondition of code in a label
  context is that of the code with the context's postcondition;
* `wp_block_iff`, `wp_if_iff`: a `block` (no parameters) is its label, an `if` is the block
  of the taken branch;
* `CEquiv` is an equivalence relation, holds for `SegEquiv` (the straight-line checker),
  composes to the right (`append`) and to the left after code whose normal exits are typed
  (`prepend`, with `Keeps`), and is a congruence for `block` and `if` (`block`, `if_`);
* `Keeps.brIf`, `Keeps.of_sexec`, `Keeps.append`: typing facts for `br_if` and for
  symbolically executed straight-line code;
* **`CEquiv.loop`**: equivalent loop bodies give loops with the same partial-correctness
  weakest precondition (`PEquiv`), by Löb induction on the step index of `HWP`, when the
  body keeps the locals typed at its back edges (`KeepsBr0`).

The proofs are kept here unrefined; the statements are re-exported by
`Silmaril.Wasm.Auto.Equiv.Thms`.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Weakest preconditions in context -/

theorem wp_mono {m : Corr} {s : Store H} {f : Frame} {c : List Admin} {Q Q' : Post H}
    (hq : ∀ s f o, Q s f o → Q' s f o) (h : Wp m P host s f c Q) : Wp m P host s f c Q' := by
  cases m
  · exact HWP.mono hq h
  · exact TSafe.post_mono h hq

theorem wp_seq_iff {m : Corr} {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H} :
    Wp m P host s f (c₁ ++ c₂) Q ↔ Wp m P host s f c₁ (seqPostM m P host c₂ Q) := by
  cases m
  · exact ⟨hwp_seq_inv, HWP.seq⟩
  · exact ⟨twp_seq_inv, TWP.seq⟩

theorem wp_label_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {k : Nat}
    {cont : List Instr} {b : List Admin} {Q : Post H} (hus : NoFuncTop us) :
    Wp m P host s f (vals us ++ [.label k cont b]) Q ↔
      Wp m P host s f b (labelPostM m P host k cont us Q) := by
  cases m
  · exact ⟨hwp_label_inv hus, HWP.label⟩
  · exact ⟨twp_label_inv hus, fun h => TSafe.label h⟩

/-- **Code in a label context.** -/
theorem wp_plug_iff {m : Corr} {s : Store H} {f : Frame} {x : List Admin} :
    ∀ {E : LCtx} {Q : Post H}, E.Ok →
      (Wp m P host s f (E.plug x) Q ↔ Wp m P host s f x (E.post m P host Q))
  | .hole, _, _ => Iff.rfl
  | .label us k cont E rest, Q, ⟨hus, hE⟩ => by
    show Wp m P host s f (vals us ++ [.label k cont (E.plug x)] ++ rest) Q ↔ _
    rw [wp_seq_iff, wp_label_iff hus]
    exact wp_plug_iff hE

/-- The values below a typed stack top do not end with a function reference. -/
theorem noFuncTop_append {us rs : List Val} {st : List IntType} (hus : NoFuncTop us)
    (hrs : TypedVals st rs) : NoFuncTop (us ++ rs.reverse) := by
  intro a h
  rcases rs with _ | ⟨r, rs⟩
  · exact hus a (by simpa using h)
  · obtain ⟨hlen, hty⟩ := hrs
    have h0 : 0 < st.length := by simp at hlen; omega
    obtain ⟨x, hx⟩ := hty 0 h0
    have : r = .ref (.func a) := by simpa using h
    rw [this] at hx
    cases hx

/-- A `block` without parameters is its label. -/
theorem wp_block_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {bt : BlockType}
    {a : List Instr} {rest : List Admin} {Q : Post H} {t₂ : List Validation.CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) (hus : NoFuncTop us) :
    Wp m P host s f (vals us ++ .plain (.block bt a) :: rest) Q ↔
      Wp m P host s f (vals us ++ [.label t₂.length [] (expression a)] ++ rest) Q := by
  constructor
  · intro h
    have hst : Step P host ⟨s, f, vals us ++ .plain (.block bt a) :: rest⟩
        ⟨s, f, vals us ++ [.label t₂.length [] (expression a)] ++ rest⟩ := by
      have := Sim.Step.vals_left (Sim.Step.append_right
        (Step.block (P := P) (host := host) (s := s) (f := f) (body := a) (vs := []) hbt rfl) rest) us
      simpa using this
    exact wp_step_inv h hst
  · intro h
    have h₁ : Wp m P host s f (expression a)
        (labelPostM m P host t₂.length [] us (seqPostM m P host rest Q)) := by
      have := (wp_plug_iff (m := m) (P := P) (host := host) (s := s) (f := f)
        (x := expression a) (E := .label us t₂.length [] .hole rest) (Q := Q) ⟨hus, trivial⟩).mp
        (by simpa [LCtx.plug] using h)
      simpa [LCtx.post] using this
    cases m
    · simpa using HWP.block (us := us) (vs := []) hbt rfl (by simpa [labelPostM, seqPostM] using h₁)
    · simpa using TWP.block (us := us) (vs := []) hbt rfl (by simpa [labelPostM, seqPostM] using h₁)

/-- An `if` is the block of the taken branch. -/
theorem wp_if_iff {m : Corr} {s : Store H} {f : Frame} {us : List Val} {c : BitVec 32}
    {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H} :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q ↔
      Wp m P host s f (vals us ++ .plain (.block bt (if c ≠ 0 then b₁ else b₂)) :: rest) Q := by
  have e : ∀ x : Admin, vals (us ++ [.i32 c]) ++ x :: rest = vals us ++ ([constI32 c, x] ++ rest) :=
    fun x => by
      simp only [vals, List.map_append, List.map_cons, List.map_nil, constI32, List.append_assoc,
        List.cons_append, List.nil_append]
  constructor
  · show Wp m P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q →
      Wp m P host s f (vals us ++ .plain (.block bt (if c ≠ 0 then b₁ else b₂)) :: rest) Q
    intro h₀
    have h : Wp m P host s f (vals us ++ ([constI32 c, .plain (.if_ bt b₁ b₂)] ++ rest)) Q :=
      e _ ▸ h₀
    by_cases hc : c = 0
    · subst hc
      have hst := Sim.Step.vals_left (Sim.Step.append_right
          (Step.ifFalse (P := P) (host := host) (s := s) (f := f) (bt := bt) (b₁ := b₁) (b₂ := b₂)) rest) us
      have hb : (if (0 : BitVec 32) ≠ 0 then b₁ else b₂) = b₂ := ite_eq_right (by simp)
      rw [hb]
      exact wp_step_inv h hst
    · have hst := Sim.Step.vals_left (Sim.Step.append_right
          (Step.ifTrue (P := P) (host := host) (s := s) (f := f) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc) rest) us
      have hb : (if c ≠ 0 then b₁ else b₂) = b₁ := ite_eq_left hc
      rw [hb]
      exact wp_step_inv h hst
  · intro h
    cases m
    · refine HWP.if_ (fun hc => ?_) (fun hc => ?_)
      · have hb : (if c ≠ 0 then b₁ else b₂) = b₁ := ite_eq_left hc
        exact hb ▸ h
      · have hb : (if c ≠ 0 then b₁ else b₂) = b₂ := ite_eq_right (by simp [hc])
        exact hb ▸ h
    · exact TWP.if_ h

/-! ## `CEquiv` -/

theorem TypedVals.tail {t : IntType} {ts : List IntType} {r : Val} {rs : List Val}
    (h : TypedVals (t :: ts) (r :: rs)) : TypedVals ts rs :=
  ⟨by simpa using h.1, fun i hi => h.2 (i + 1) (by simpa using hi)⟩

theorem TypedVals.head_i32 {ts : List IntType} {r : Val} {rs : List Val}
    (h : TypedVals (.i32 :: ts) (r :: rs)) : ∃ c : BitVec 32, r = .i32 c := by
  obtain ⟨c, hc⟩ := h.2 0 (by simp)
  exact ⟨c, hc⟩

theorem TypedVals.cons_inv {t : IntType} {ts : List IntType} {rs : List Val}
    (h : TypedVals (t :: ts) rs) : ∃ r rs', rs = r :: rs' := by
  rcases rs with _ | ⟨r, rs'⟩
  · have := h.1; simp at this
  · exact ⟨r, rs', rfl⟩

theorem CEquiv.refl (lt st : List IntType) (a : List Instr) : CEquiv lt st a a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem CEquiv.symm {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b) :
    CEquiv lt st b a :=
  fun m P _ host s f rs us rest Q hf hrs hus => (h m P host s f rs us rest Q hf hrs hus).symm

theorem CEquiv.trans {lt st : List IntType} {a b c : List Instr} (h₁ : CEquiv lt st a b)
    (h₂ : CEquiv lt st b c) : CEquiv lt st a c :=
  fun m P _ host s f rs us rest Q hf hrs hus =>
    (h₁ m P host s f rs us rest Q hf hrs hus).trans (h₂ m P host s f rs us rest Q hf hrs hus)

theorem CEquiv.part {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b) :
    PEquiv lt st a b :=
  fun P _ host s f rs us rest Q hf hrs hus => h .part P host s f rs us rest Q hf hrs hus

/-- **The straight-line checker's equivalence holds in typed contexts.** -/
theorem SegEquiv.cequiv {lt st : List IntType} {a b : List Instr} (h : SegEquiv lt st a b) :
    CEquiv lt st a b := by
  intro m P H host s f rs us rest Q hf hrs _
  obtain ⟨ls, hls, hlt⟩ := hf
  exact Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.typed h m P host s hls hlt hrs us rest Q

/-- Equivalent code, in any label context. -/
theorem CEquiv.plug {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b)
    {m : Corr} {s : Store H} {f : Frame} {rs us : List Val} {rest : List Admin} {E : LCtx}
    {Q : Post H} (hE : E.Ok) (hf : TypedFrame lt f) (hrs : TypedVals st rs) (hus : NoFuncTop us) :
    Wp m P host s f (E.plug (cfgCode us rs a rest)) Q ↔
      Wp m P host s f (E.plug (cfgCode us rs b rest)) Q := by
  rw [wp_plug_iff hE, wp_plug_iff hE]
  exact h m P host s f rs us rest _ hf hrs hus

theorem cfgCode_append (us rs : List Val) (a c : List Instr) (rest : List Admin) :
    cfgCode us rs (a ++ c) rest = cfgCode us rs a (expression c ++ rest) := by
  simp [cfgCode, expression]

/-- **Sequential composition, right.** -/
theorem CEquiv.append {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b)
    (c : List Instr) : CEquiv lt st (a ++ c) (b ++ c) := by
  intro m P H host s f rs us rest Q hf hrs hus
  rw [cfgCode_append, cfgCode_append]
  exact h m P host s f rs us _ Q hf hrs hus

theorem seqPostM_ne_normal {m : Corr} {c : List Admin} {Q : Post H} {s : Store H} {F : Frame}
    {o : Outcome} (ho : ∀ vs, o ≠ .normal vs) : seqPostM m P host c Q s F o ↔ Q s F o := by
  cases m <;> rcases o with vs | _ | _ | _ | _ | _ <;> first | exact (ho vs rfl).elim | exact Iff.rfl

theorem seqPostM_normal {m : Corr} {c : List Admin} {Q : Post H} {s : Store H} {F : Frame}
    {vs : List Val} : seqPostM m P host c Q s F (.normal vs) ↔ Wp m P host s F (vals vs ++ c) Q := by
  cases m <;> exact Iff.rfl

theorem cfgCode_split (us rs : List Val) (c a : List Instr) (rest : List Admin) :
    cfgCode us rs (c ++ a) rest = cfgCode us rs c [] ++ (expression a ++ rest) := by
  simp [cfgCode, expression]

/-- One direction of `prepend`. -/
theorem prepend_imp {lt st lt' st' : List IntType} {c a b : List Instr} (hc : Keeps lt st c lt' st')
    (h : CEquiv lt' st' a b) {m : Corr} {s : Store H} {f : Frame} {rs us : List Val}
    {rest : List Admin} {Q : Post H} (hf : TypedFrame lt f) (hrs : TypedVals st rs)
    (hus : NoFuncTop us) (hw : Wp m P host s f (cfgCode us rs (c ++ a) rest) Q) :
    Wp m P host s f (cfgCode us rs (c ++ b) rest) Q := by
  rw [cfgCode_split] at hw ⊢
  rw [wp_seq_iff] at hw ⊢
  have h₁ := hc m P host s f rs us _ hf hrs hw
  refine wp_mono (fun s F o ho => ?_) h₁
  obtain ⟨hq, ht⟩ := ho
  rcases o with vs | _ | _ | _ | _ | _
  · obtain ⟨hF, rs', hrs', rfl⟩ := ht vs rfl
    have hq' : Wp m P host s F (cfgCode us rs' a rest) Q := by
      simpa [cfgCode] using (seqPostM_normal (P := P) (host := host)).mp hq
    have := (h m P host s F rs' us rest Q hF hrs' hus).mp hq'
    exact (seqPostM_normal (P := P) (host := host)).mpr (by simpa [cfgCode] using this)
  all_goals exact (seqPostM_ne_normal (by simp)).mpr ((seqPostM_ne_normal (by simp)).mp hq)

/-- **Sequential composition, left**, after code whose normal exits are typed. -/
theorem CEquiv.prepend {lt st lt' st' : List IntType} {c a b : List Instr}
    (hc : Keeps lt st c lt' st') (h : CEquiv lt' st' a b) : CEquiv lt st (c ++ a) (c ++ b) :=
  fun _ _ _ _ _ _ _ _ _ _ hf hrs hus =>
    ⟨prepend_imp hc h hf hrs hus, prepend_imp hc (CEquiv.symm h) hf hrs hus⟩

/-- **`block`** (no parameters: `empty` or a value type). -/
theorem CEquiv.block {lt st : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂)) (h : CEquiv lt [] a b) :
    CEquiv lt st [.block bt a] [.block bt b] := by
  intro m P H host s f rs us rest Q hf hrs hus
  obtain ⟨t₂, ht⟩ := hbt f.module
  have hU := noFuncTop_append hus hrs
  have e : ∀ x : List Instr, cfgCode us rs [.block bt x] rest =
      vals (us ++ rs.reverse) ++ .plain (.block bt x) :: rest := fun x => by
    simp [cfgCode, expression]
  rw [e, e, wp_block_iff ht hU, wp_block_iff ht hU]
  have hE : LCtx.Ok (.label (us ++ rs.reverse) t₂.length [] .hole rest) := ⟨hU, trivial⟩
  have := CEquiv.plug h (m := m) (P := P) (host := host) (s := s) (f := f) (rs := []) (us := [])
    (rest := []) (Q := Q) hE hf ⟨rfl, fun i hi => absurd hi (by simp)⟩ (by simp [NoFuncTop])
  simpa [LCtx.plug, cfgCode] using this

/-- **`if`** (no parameters). -/
theorem CEquiv.if_ {lt st : List IntType} {a₁ a₂ b₁ b₂ : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂)) (h₁ : CEquiv lt [] a₁ b₁)
    (h₂ : CEquiv lt [] a₂ b₂) : CEquiv lt (.i32 :: st) [.if_ bt a₁ a₂] [.if_ bt b₁ b₂] := by
  intro m P H host s f rs us rest Q hf hrs hus
  obtain ⟨r, rs', rfl⟩ := TypedVals.cons_inv hrs
  obtain ⟨c, rfl⟩ := TypedVals.head_i32 hrs
  have hrs' : TypedVals st rs' := TypedVals.tail hrs
  have e : ∀ x y : List Instr, cfgCode us (.i32 c :: rs') [.if_ bt x y] rest =
      vals (us ++ rs'.reverse ++ [.i32 c]) ++ .plain (.if_ bt x y) :: rest := fun x y => by
    simp [cfgCode, expression]
  rw [e, e, wp_if_iff, wp_if_iff]
  have hb : ∀ x y, cfgCode us rs' [.block bt (if c ≠ 0 then x else y)] rest =
      vals (us ++ rs'.reverse) ++ .plain (.block bt (if c ≠ 0 then x else y)) :: rest := fun x y => by
    simp [cfgCode, expression]
  have hsel : CEquiv lt [] (if c ≠ 0 then a₁ else a₂) (if c ≠ 0 then b₁ else b₂) := by
    by_cases hc : c = 0
    · rw [ite_eq_right (by simp [hc]), ite_eq_right (by simp [hc])]; exact h₂
    · rw [ite_eq_left hc, ite_eq_left hc]; exact h₁
  have hblk := CEquiv.block (st := st) hbt hsel
  have := hblk m P host s f rs' us rest Q hf hrs' hus
  rw [hb, hb] at this
  exact this

/-! ## Typing facts -/

/-- `br_if` pops an `i32` and keeps the frame. -/
theorem Keeps.brIf (lt st : List IntType) (l : LabelIdx) : Keeps lt (.i32 :: st) [.brIf l] lt st := by
  intro m P H host s f rs us Q hf hrs hw
  obtain ⟨r, rs', rfl⟩ := TypedVals.cons_inv hrs
  obtain ⟨c, rfl⟩ := TypedVals.head_i32 hrs
  have hrs' : TypedVals st rs' := TypedVals.tail hrs
  have e : cfgCode us (.i32 c :: rs') [.brIf l] [] =
      vals (us ++ rs'.reverse ++ [.i32 c]) ++ .plain (.brIf l) :: [] := by
    simp [cfgCode, expression]
  rw [e] at hw ⊢
  have e₂ : ∀ x : Admin, vals (us ++ rs'.reverse ++ [.i32 c]) ++ [x] =
      vals (us ++ rs'.reverse) ++ [constI32 c, x] := fun x => by
    simp only [vals, List.map_append, List.map_cons, List.map_nil, constI32, List.append_assoc,
      List.cons_append, List.nil_append]
  by_cases hc0 : c = 0
  · show Wp m P host s f (vals (us ++ rs'.reverse ++ [.i32 c]) ++ [.plain (.brIf l)])
      (TypedExit lt st us Q)
    subst hc0
    have hst : Step P host ⟨s, f, vals (us ++ rs'.reverse ++ [.i32 0]) ++ .plain (.brIf l) :: []⟩
        ⟨s, f, vals (us ++ rs'.reverse)⟩ := by
      have := Sim.Step.vals_left (Step.brIfFalse (P := P) (host := host) (s := s) (f := f) (l := l))
        (us ++ rs'.reverse)
      rw [e₂]
      simpa using this
    have hq := wp_exit_post (wp_step_inv hw hst) (o := .normal (us ++ rs'.reverse)) rfl
    have hq' : TypedExit lt st us Q s f (.normal (us ++ rs'.reverse)) :=
      ⟨hq, fun vs hvs => ⟨hf, rs', hrs', by cases hvs; rfl⟩⟩
    cases m
    · exact HWP.brIf (fun h => (h rfl).elim) (fun _ => by simpa using HWP.of_vals hq')
    · exact TWP.brIf (fun h => (h rfl).elim) (fun _ => by
        have := TSafe.exit (P := P) (host := host) (c := ⟨s, f, vals (us ++ rs'.reverse)⟩) (.normal _) rfl hq'
        simpa [TWP] using this)
  · show Wp m P host s f (vals (us ++ rs'.reverse ++ [.i32 c]) ++ [.plain (.brIf l)])
      (TypedExit lt st us Q)
    have hst : Step P host ⟨s, f, vals (us ++ rs'.reverse ++ [.i32 c]) ++ .plain (.brIf l) :: []⟩
        ⟨s, f, vals (us ++ rs'.reverse) ++ [.plain (.br l)]⟩ := by
      have := Sim.Step.vals_left (Step.brIfTrue (P := P) (host := host) (s := s) (f := f) (l := l) hc0)
        (us ++ rs'.reverse)
      rw [e₂]
      simpa using this
    have hex : Exits (.br l.toNat (us ++ rs'.reverse)) (vals (us ++ rs'.reverse) ++ [.plain (.br l)]) :=
      ⟨l, [], rfl, rfl⟩
    have hq := wp_exit_post (wp_step_inv hw hst) hex
    have hq' : TypedExit lt st us Q s f (.br l.toNat (us ++ rs'.reverse)) :=
      ⟨hq, fun vs hvs => by cases hvs⟩
    cases m
    · exact HWP.brIf (fun _ => HWP.of_exits hex hq') (fun h => (hc0 h).elim)
    · exact TWP.brIf (fun _ => hq') (fun h => (hc0 h).elim)

end Silmaril.Proofs.Wasm.Auto.Equiv