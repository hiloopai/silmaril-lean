module

public import Silmaril.Wasm.Auto.ESeg.Defs
public import Silmaril.Proofs.Wasm.Auto.ESeg.Check
public import Silmaril.Wasm.Auto.XExec.Thms

/-! # Lifting with `select` and from function entry: the symbolic run is the concrete run

* `selTerm_eval`: on `i32` values, `selTerm a b c` is `select`;
* `lstepSel_exec`, `lstepsSel_exec`: one instruction, a sequence (the `select` case is new; every
  other instruction is `Silmaril.Proofs.Wasm.Auto.ESeg.lstep_exec`);
* `liftSel_exec`: in a frame typed by `Γ`, `execS` of a lifted segment is what its summary denotes;
* `den_entry`, `liftEntrySel_exec`: the same for a body lifted from function entry, in an entry
  frame.

Unrefined proofs (case splits on the instruction and on the denotation).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec

variable {f : Frame}

/-! ## `select` as a term -/

theorem sel_bits (x y k : BitVec 32) :
    y ^^^ ((x ^^^ y) &&& (0 - bool32 (k != 0))) = if k = 0 then y else x := by
  by_cases hk : k = 0
  · subst hk; simp [bool32]
  · have h1 : (k != 0) = true := by simpa using hk
    rw [h1, ite_eq_right_of_eq_false _ _ (eq_false hk)]
    simp only [bool32, ↓reduceIte]
    have hm : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    rw [hm, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm y x, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

theorem selTerm_eval {a b c : Term} {x y k : BitVec 32} (ha : a.eval f = some (Val.i32 x))
    (hb : b.eval f = some (Val.i32 y)) (hc : c.eval f = some (Val.i32 k)) :
    (selTerm a b c).eval f = some (if k = 0 then Val.i32 y else Val.i32 x) := by
  have h1 : (Term.rel .i32 .ne c (.const .i32 0)).eval f = some (Val.i32 (bool32 (k != 0))) := by
    simp only [Term.eval, hc]; rfl
  have h2 : (Term.bin .i32 .sub (.const .i32 0) (.rel .i32 .ne c (.const .i32 0))).eval f =
      some (Val.i32 (0 - bool32 (k != 0))) := by
    show binV .i32 .sub ((Term.const .i32 0).eval f)
      ((Term.rel .i32 .ne c (.const .i32 0)).eval f) = _
    rw [h1]; rfl
  have h3 : (Term.bin .i32 .xor a b).eval f = some (Val.i32 (x ^^^ y)) := by
    simp only [Term.eval, ha, hb]; rfl
  have h4 : (Term.bin .i32 .and (.bin .i32 .xor a b)
      (.bin .i32 .sub (.const .i32 0) (.rel .i32 .ne c (.const .i32 0)))).eval f =
      some (Val.i32 ((x ^^^ y) &&& (0 - bool32 (k != 0)))) := by
    show binV .i32 .and ((Term.bin .i32 .xor a b).eval f)
      ((Term.bin .i32 .sub (.const .i32 0) (.rel .i32 .ne c (.const .i32 0))).eval f) = _
    rw [h2, h3]; rfl
  have h5 : (selTerm a b c).eval f =
      some (Val.i32 (y ^^^ ((x ^^^ y) &&& (0 - bool32 (k != 0))))) := by
    show binV .i32 .xor (b.eval f) ((Term.bin .i32 .and (.bin .i32 .xor a b)
      (.bin .i32 .sub (.const .i32 0) (.rel .i32 .ne c (.const .i32 0)))).eval f) = _
    rw [h4, hb]; rfl
  rw [h5, sel_bits]
  split <;> rfl

/-! ## Covers and lengths -/

/-- Inversion of `lstepSel` at a `select`: three `i32` operands on the stack, replaced by their
`selTerm`. -/
theorem lstepSel_select_inv {Γ : List IntType} {st ls gs : List Term} {ts : Option (List ValType)}
    {S' : Sym} (h : lstepSel Γ ⟨st, ls, gs⟩ (.select ts) = some S') :
    ∃ c b a st', st = c :: b :: a :: st' ∧ a.typeOf Γ = some .i32 ∧ b.typeOf Γ = some .i32 ∧
      c.typeOf Γ = some .i32 ∧ S' = ⟨selTerm a b c :: st', ls, gs⟩ := by
  simp only [lstepSel] at h
  rcases st with _ | ⟨c, _ | ⟨b, _ | ⟨a, st⟩⟩⟩ <;> simp only [reduceCtorEq] at h
  split at h
  · rename_i hty
    cases h
    exact ⟨c, b, a, st, rfl, hty.1, hty.2.1, hty.2.2, rfl⟩
  · cases h

theorem lstepSel_covered {Γ : List IntType} {S S' : Sym} {i : Instr}
    (h : lstepSel Γ S i = some S') :
    Covered S S' := by
  by_cases hi : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hi
    rcases S with ⟨st, ls, gs⟩
    obtain ⟨c, b, a, st', rfl, -, -, -, rfl⟩ := lstepSel_select_inv h
    intro e he
    simp only [Sym.terms, List.mem_append, List.mem_cons] at he
    rcases he with (he | he) | (rfl | rfl | rfl | he)
    · exact self_cover (by simp [Sym.terms, he])
    · exact self_cover (by simp [Sym.terms, he])
    · exact ⟨selTerm a b e, by simp [Sym.terms], [1, 1, 1, 0], by simp [selTerm, Term.get?]⟩
    · exact ⟨selTerm a e c, by simp [Sym.terms], [0], by simp [selTerm, Term.get?]⟩
    · exact ⟨selTerm e b c, by simp [Sym.terms], [1, 0, 0], by simp [selTerm, Term.get?]⟩
    · exact self_cover (by simp [Sym.terms, he])
  · have h' : lstep S i = some S' := by
      cases i <;> first | exact h | exact (hi ⟨_, rfl⟩).elim
    exact lstep_covered h'

theorem lstepSel_eq {Γ : List IntType} {S : Sym} {i : Instr} (hi : ∀ ts, i ≠ .select ts) :
    lstepSel Γ S i = lstep S i := by
  cases i <;> first | rfl | exact absurd rfl (hi _)

theorem lstepSel_locs_length {Γ : List IntType} {S S' : Sym} {i : Instr}
    (h : lstepSel Γ S i = some S') : S'.locs.length = S.locs.length := by
  by_cases hi : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hi
    rcases S with ⟨st, ls, gs⟩
    obtain ⟨c, b, a, st', rfl, -, -, -, rfl⟩ := lstepSel_select_inv h
    rfl
  · rw [lstepSel_eq (fun ts he => hi ⟨ts, he⟩)] at h
    exact lstep_locs_length h

/-! ## One step, a sequence -/

theorem typed_i32 {Γ : List IntType} (hf : FrameOk Γ f) {e : Term} {v : Val}
    (ht : e.typeOf Γ = some .i32) (hv : e.eval f = some v) : ∃ x, v = Val.i32 x := by
  obtain ⟨x, hx⟩ := typed_some hf ht (by simp [hv])
  rw [hv] at hx
  exact ⟨x, Option.some.inj hx⟩

/-- `select` on three `i32` values. -/
theorem selectV_i32 (x y k : BitVec 32) (vs : List Val) :
    selectV (Val.i32 k :: Val.i32 y :: Val.i32 x :: vs) =
      some ((if k = 0 then Val.i32 y else Val.i32 x) :: vs) := by
  by_cases hk : k = 0
  · subst hk
    simp only [selectV, Val.i32, popInt]
    split <;> split <;> rename_i h1 h2
    · rfl
    · exact absurd trivial h2
    · exact absurd rfl h1
    · exact absurd trivial h2
  · simp [selectV, Val.i32, popInt]
    rfl

/-- **`select` on a symbolic stack** of three `i32` terms. -/
theorem select_exec {H : Type} {Γ : List IntType} (hf : FrameOk Γ f) {a b c : Term}
    {st lc gd : List Term} {ts : Option (List ValType)} (hta : a.typeOf Γ = some .i32)
    (htb : b.typeOf Γ = some .i32) (htc : c.typeOf Γ = some .i32) (s : Store H) (rs : List Val) :
    (den f ⟨c :: b :: a :: st, lc, gd⟩).bind (fun p => exec1S s p.1 (p.2 ++ rs) (.select ts)) =
      (den f ⟨selTerm a b c :: st, lc, gd⟩).map fun p => (s, p.1, p.2 ++ rs) := by
  have h : lstepSel Γ ⟨c :: b :: a :: st, lc, gd⟩ (.select ts) =
      some ⟨selTerm a b c :: st, lc, gd⟩ := by
    simp [lstepSel, hta, htb, htc]
  match hd : den f ⟨c :: b :: a :: st, lc, gd⟩ with
  | none => rw [covered_none (lstepSel_covered h) hd]; rfl
  | some p =>
    obtain ⟨gs, ls, vs, hg, hl, hv, rfl⟩ := den_eq_some hd
    obtain ⟨vc, vs₁, hvc, hvs₁, rfl⟩ := evalL_cons_inv hv
    obtain ⟨vb, vs₂, hvb, hvs₂, rfl⟩ := evalL_cons_inv hvs₁
    obtain ⟨va, vst, hva, hvst, rfl⟩ := evalL_cons_inv hvs₂
    obtain ⟨k, rfl⟩ := typed_i32 hf htc hvc
    obtain ⟨y, rfl⟩ := typed_i32 hf htb hvb
    obtain ⟨x, rfl⟩ := typed_i32 hf hta hva
    have hsel : (selTerm a b c).eval f = some (if k = 0 then Val.i32 y else Val.i32 x) :=
      selTerm_eval hva hvb hvc
    rw [Option.bind_some,
      den_of (S := ⟨selTerm a b c :: st, lc, gd⟩) hg hl (evalL_cons_some hsel hvst)]
    simp only [exec1S, List.cons_append, Option.map_some, selectV_i32]

/-- **One instruction with `select`.** -/
theorem lstepSel_exec {H : Type} {Γ : List IntType} (hf : FrameOk Γ f) {S S' : Sym} {i : Instr}
    (h : lstepSel Γ S i = some S') (s : Store H) (rs : List Val)
    (hlen : S.locs.length ≤ f.locals.length) :
    (den f S).bind (fun p => exec1S s p.1 (p.2 ++ rs) i) =
      (den f S').map fun p => (s, p.1, p.2 ++ rs) := by
  by_cases hi : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hi
    rcases S with ⟨st, lc, gd⟩
    obtain ⟨c, b, a, st', rfl, hta, htb, htc, rfl⟩ := lstepSel_select_inv h
    exact select_exec hf hta htb htc s rs
  · rw [lstepSel_eq (fun ts he => hi ⟨ts, he⟩)] at h
    have k := lstep_exec (f := f) h s rs hlen
    rw [← k]
    cases den f S with
    | none => rfl
    | some p => simp only [Option.bind_some]; exact exec1S_of_ne (fun ts he => hi ⟨ts, he⟩)

/-- **A sequence of instructions with `select`.** -/
theorem lstepsSel_exec {H : Type} {Γ : List IntType} (hf : FrameOk Γ f) (s : Store H)
    (rs : List Val) :
    ∀ {is : List Instr} {S S' : Sym}, lstepsSel Γ S is = some S' → S.locs.length ≤ f.locals.length →
      (den f S).bind (fun p => execS s p.1 (p.2 ++ rs) is) =
        (den f S').map fun p => (s, p.1, p.2 ++ rs)
  | [], S, S', h, _ => by
    cases h
    cases den f S <;> rfl
  | i :: is, S, S', h, hlen => by
    simp only [lstepsSel] at h
    split at h
    · rename_i S₁ h₁
      have k₁ := lstepSel_exec hf h₁ s rs hlen
      have hlen₁ : S₁.locs.length ≤ f.locals.length := by
        rw [lstepSel_locs_length h₁]; exact hlen
      have k₂ := lstepsSel_exec hf s rs h hlen₁
      rw [← k₂]
      cases hd : den f S with
      | none =>
        have h1 : den f S₁ = none := by
          cases h' : den f S₁ with
          | none => rfl
          | some q => rw [hd, h'] at k₁; simp at k₁
        rw [h1]; rfl
      | some p =>
        rw [hd, Option.bind_some] at k₁
        rw [Option.bind_some, execS_cons]
        cases he : exec1S s p.1 (p.2 ++ rs) i with
        | none =>
          rw [he] at k₁
          have : den f S₁ = none := by
            cases h' : den f S₁ with
            | none => rfl
            | some q => rw [h'] at k₁; cases k₁
          rw [this]; rfl
        | some r =>
          rw [he] at k₁
          obtain ⟨q, hq, hr⟩ := Option.map_eq_some_iff.mp k₁.symm
          rw [hq, Option.bind_some]
          subst hr
          rfl
    · cases h

/-! ## Initial states -/

theorem len_le_of_frameOk {Γ : List IntType} (hl : Γ.length < 2 ^ 32) (hf : FrameOk Γ f) :
    Γ.length ≤ f.locals.length := by
  rcases Nat.eq_zero_or_pos Γ.length with h0 | hpos
  · omega
  · obtain ⟨t, ht⟩ : ∃ t, Γ[Γ.length - 1]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨x, hx⟩ := hf _ t ht
    simp only [localVal?, Frame.local?, lidx_toNat (by omega : Γ.length - 1 < 2 ^ 32)] at hx
    split at hx
    · rename_i v hv
      have := (List.getElem?_eq_some_iff.mp hv).1
      omega
    · cases hx

/-- **Lifting with `select` is sound.** -/
theorem liftSel_exec {Γ : List IntType} {a : List Instr} {A : Sym} (hl : Γ.length < 2 ^ 32)
    (h : liftSel Γ a = some A) {H : Type} (s : Store H) (rs : List Val) (hf : FrameOk Γ f) :
    execS s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) := by
  have hlen : (Sym.init Γ.length).locs.length ≤ f.locals.length := by
    simpa [Sym.init] using len_le_of_frameOk hl hf
  have k := lstepsSel_exec hf s rs h hlen
  rw [den_init hl hf, Option.bind_some] at k
  simpa using k

theorem evalL_append {es₁ es₂ : List Term} :
    evalL f (es₁ ++ es₂) = (evalL f es₁).bind fun v₁ => (evalL f es₂).map (v₁ ++ ·) := by
  induction es₁ with
  | nil =>
    simp only [List.nil_append, evalL, Option.bind_some, List.nil_append]
    cases evalL f es₂ <;> rfl
  | cons e es ih =>
    simp only [List.cons_append, evalL, ih]
    cases e.eval f <;> cases evalL f es <;> cases evalL f es₂ <;> rfl

theorem evalL_map_congr {α : Type} {l : List α} {g h : α → Term}
    (hgh : ∀ x ∈ l, (g x).eval f = (h x).eval f) : evalL f (l.map g) = evalL f (l.map h) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, evalL]
    rw [hgh x (by simp), ih (fun y hy => hgh y (by simp [hy]))]

theorem evalL_zeros : ∀ (ds : List IntType) (n : Nat),
    (∀ j t, ds[j]? = some t → localVal? f (lidx (n + j)) = some (intVal t 0)) →
      evalL f ((List.range ds.length).map fun j => Term.lget (n + j)) =
        evalL f (ds.map fun t => Term.const t 0)
  | [], _, _ => rfl
  | t :: ds, n, h => by
    have h0 : (Term.lget (n + 0)).eval f = (Term.const t 0).eval f := by
      rw [show (Term.lget (n + 0)).eval f = localVal? f (lidx (n + 0)) from rfl, h 0 t rfl]; rfl
    have h' : ∀ j u, ds[j]? = some u → localVal? f (lidx (n + 1 + j)) = some (intVal u 0) := by
      intro j u hu
      rw [show n + 1 + j = n + (j + 1) by omega]
      exact h (j + 1) u hu
    have ih := evalL_zeros ds (n + 1) h'
    have hmap : ((List.range ds.length).map fun j => Term.lget (n + (j + 1))) =
        (List.range ds.length).map fun j => Term.lget (n + 1 + j) := by
      apply List.map_congr_left; intro j _; rw [show n + (j + 1) = n + 1 + j by omega]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, evalL, List.map]
    rw [h0, hmap, ih]

theorem den_entry {Γ ds : List IntType} (hl : (Γ ++ ds).length < 2 ^ 32)
    (hf : EntryFrame Γ ds f) : den f (Sym.entry Γ.length ds) = some (f, []) := by
  have hinit := den_init hl hf.1
  have hlocs : (Sym.init (Γ ++ ds).length).locs =
      (List.range Γ.length).map Term.lget ++
        (List.range ds.length).map fun j => Term.lget (Γ.length + j) := by
    simp only [Sym.init, List.length_append, List.range_add, List.map_append, List.map_map,
      Function.comp_def]
  have hev : evalL f (Sym.entry Γ.length ds).locs = evalL f (Sym.init (Γ ++ ds).length).locs := by
    rw [hlocs]
    simp only [Sym.entry]
    rw [evalL_append, evalL_append, evalL_zeros ds Γ.length hf.2]
  simp only [den] at hinit ⊢
  rw [hev]
  simpa [Sym.entry, Sym.init, evalL] using hinit

/-- **Lifting from function entry is sound.** -/
theorem liftEntrySel_exec {Γ ds : List IntType} {a : List Instr} {A : Sym}
    (hl : (Γ ++ ds).length < 2 ^ 32) (h : liftEntrySel Γ ds a = some A) {H : Type} (s : Store H)
    (rs : List Val) (hf : EntryFrame Γ ds f) :
    execS s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) := by
  have hlen : (Sym.entry Γ.length ds).locs.length ≤ f.locals.length := by
    simpa [Sym.entry] using len_le_of_frameOk hl hf.1
  have k := lstepsSel_exec hf.1 s rs h hlen
  rw [den_entry hl hf, Option.bind_some] at k
  simpa using k

end Silmaril.Proofs.Wasm.Auto.ESeg
