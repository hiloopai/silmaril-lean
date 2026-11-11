module

public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# Symbolic execution of function bodies: the forward rule

`twp_xexec`: if `xexec` runs a body from the symbolic state `S` to `S'`, then for every
environment `ρ`, the total-correctness weakest precondition (`TWP`, every profile and host
relation) of the body at the concrete state `S` denotes follows from that of the final state.
Straight-line instructions reuse `Silmaril.Wasm.Auto.Equiv.wp_sstep`; `select` uses the every-run
`select` rules, `block` and `if` the total rules `TWP.block` and `TWP.if_`.

New proofs (one inversion lemma and one forward rule per structured instruction), used by
`Silmaril.Proofs.Wasm.Auto.Bridge.Func`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)

variable {H : Type} {P : Profile} {host : HostSemantics H} {ρ : Env}

/-! ## `select` terms and merges -/

theorem ev_selT (t : IntType) (a b c : Term) :
    ev ρ t (selT a b c) = if ev ρ .i32 c ≠ 0 then ev ρ t a else ev ρ t b := by
  simp only [selT, ev, binV_add, binV_sub, binV_mul, intRelOp, bool32]
  generalize ev ρ .i32 c = x
  by_cases hx : x = 0
  · subst hx
    cases t <;> simp
  · have h1 : (x = 0#IntType.i32.width) = False := eq_false hx
    simp only [h1, hx, ne_eq, not_false_eq_true, ite_true, bne_iff_ne]
    cases t
    · exact (show ∀ y z : BitVec 32, z + (y - z) * (1 : BitVec 32).setWidth 32 = y by
        intro y z; simp) _ _
    · exact (show ∀ y z : BitVec 64, z + (y - z) * (1 : BitVec 32).setWidth 64 = y by
        intro y z; simp) _ _

theorem den_selT (t : IntType) (a b c : Term) :
    den ρ (t, selT a b c) = if ev ρ .i32 c ≠ 0 then den ρ (t, a) else den ρ (t, b) := by
  simp only [den, ev_selT]
  split <;> rfl

theorem den_mergeSlot {c : Term} {p q r : IntType × Term} (h : mergeSlot c p q = some r) :
    den ρ r = if ev ρ .i32 c ≠ 0 then den ρ p else den ρ q := by
  unfold mergeSlot at h
  split at h
  · rename_i ht
    cases h
    rcases p with ⟨t, a⟩
    rcases q with ⟨t', b⟩
    obtain rfl : t = t' := ht
    split
    · rename_i hab
      obtain rfl : a = b := hab
      split <;> rfl
    · exact den_selT t a b c
  · cases h

theorem mergeSlots_den {c : Term} :
    ∀ {xs ys zs : List (IntType × Term)}, mergeSlots c xs ys = some zs →
      zs.map (den ρ) = if ev ρ .i32 c ≠ 0 then xs.map (den ρ) else ys.map (den ρ)
  | [], [], zs, h => by
    cases h
    split <;> rfl
  | p :: ps, q :: qs, zs, h => by
    simp only [mergeSlots] at h
    split at h
    · rename_i r rs hr hrs
      cases h
      rw [List.map_cons, den_mergeSlot hr, mergeSlots_den hrs]
      split <;> rfl
    · cases h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [mergeSlots] at h

theorem frameAt_merge {c : Term} {xs ys zs : List (IntType × Term)}
    (h : mergeSlots c xs ys = some zs) (f : Frame) (st₁ st₂ : List (IntType × Term))
    (hc : ev ρ .i32 c ≠ 0) : frameAt f ρ ⟨zs, st₁⟩ = frameAt f ρ ⟨xs, st₂⟩ := by
  have hz := mergeSlots_den (ρ := ρ) h
  simp only [ne_eq, hc, not_false_eq_true, ite_true] at hz
  have hz' : zs.map (fun p => some (den ρ p)) = xs.map (fun p => some (den ρ p)) := by
    have := congrArg (List.map some) hz
    simp only [List.map_map] at this
    exact this
  simp only [frameAt, hz']

theorem frameAt_merge' {c : Term} {xs ys zs : List (IntType × Term)}
    (h : mergeSlots c xs ys = some zs) (f : Frame) (st₁ st₂ : List (IntType × Term))
    (hc : ev ρ .i32 c = 0) : frameAt f ρ ⟨zs, st₁⟩ = frameAt f ρ ⟨ys, st₂⟩ := by
  have hz := mergeSlots_den (ρ := ρ) h
  simp only [ne_eq, hc, not_true_eq_false, ite_false] at hz
  have hz' : zs.map (fun p => some (den ρ p)) = ys.map (fun p => some (den ρ p)) := by
    have := congrArg (List.map some) hz
    simp only [List.map_map] at this
    exact this
  simp only [frameAt, hz']

/-! ## Blocks -/

theorem blockType_of_blockRes {bt : BlockType} {ts : List IntType} (h : blockRes? bt = some ts)
    (m : ModuleInst) : ∃ t₂, m.blockType? bt = some ([], t₂) := by
  cases bt with
  | empty => exact ⟨[], rfl⟩
  | value t => exact ⟨[m.instVal t], rfl⟩
  | typeIdx x => simp [blockRes?] at h

/-- **A block whose body runs to the values `vs` at frame `F`.** -/
theorem twp_block_vals {bt : BlockType} {ts : List IntType} {body : List Instr} {s : Store H}
    {f F : Frame} {us vs : List Val} {rest : List Admin} {Q : Post H}
    (hbt : blockRes? bt = some ts)
    (hbody : ∀ Q' : Post H, TWP P host s F (vals vs) Q' → TWP P host s f (expression body) Q')
    (hw : TWP P host s F (vals (us ++ vs) ++ rest) Q) :
    TWP P host s f (vals us ++ .plain (.block bt body) :: rest) Q := by
  obtain ⟨t₂, hbt'⟩ := blockType_of_blockRes hbt f.module
  have h := TWP.block (P := P) (host := host) (s := s) (us := us) (vs := []) (rest := rest) (Q := Q)
    (body := body) hbt' rfl (by
      have h₁ := hbody (labelPostT P host t₂.length [] us (seqPostT P host rest Q))
        (Wp.of_vals (m := .total) (by simpa [labelPostT, labelPostK, seqPostT, TWP] using hw))
      simpa [vals] using h₁)
  simpa using h

/-! ## One instruction -/

/-- A nested body from an empty stack, as `twp_block_vals` wants it. -/
theorem BodyOk.body {rec : SState → List Instr → Option SState} (ih : BodyOk P host ρ rec)
    {ls : List (IntType × Term)} {st : List (IntType × Term)} {A : SState} {body : List Instr}
    (h : rec ⟨ls, []⟩ body = some A) (s : Store H) (f : Frame) (Q' : Post H)
    (hw : TWP P host s (frameAt f ρ A) (vals (stackAt ρ A).reverse) Q') :
    TWP P host s (frameAt f ρ ⟨ls, st⟩) (expression body) Q' := by
  have := ih h s f [] [] Q' (by simpa using hw)
  simpa [codeAt, stackAt, frameAt] using this

theorem stackAt_append (xs ys : List (IntType × Term)) (ls : List (IntType × Term)) :
    stackAt ρ ⟨ls, xs ++ ys⟩ = stackAt ρ ⟨[], xs⟩ ++ stackAt ρ ⟨[], ys⟩ := by
  simp [stackAt]

theorem twp_select {ls st : List (IntType × Term)} {t : IntType} {a b c : Term}
    {ts : Option (List ValType)} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin}
    {Q : Post H}
    (hw : TWP P host s (frameAt f ρ ⟨ls, (t, selT a b c) :: st⟩)
      (vals (us ++ (stackAt ρ ⟨ls, (t, selT a b c) :: st⟩).reverse) ++ rest) Q) :
    TWP P host s (frameAt f ρ ⟨ls, (.i32, c) :: (t, b) :: (t, a) :: st⟩)
      (vals (us ++ (stackAt ρ ⟨ls, (.i32, c) :: (t, b) :: (t, a) :: st⟩).reverse) ++
        .plain (.select ts) :: rest) Q := by
  have hst : (stackAt ρ ⟨ls, (.i32, c) :: (t, b) :: (t, a) :: st⟩).reverse =
      (stackAt ρ ⟨ls, st⟩).reverse ++ [den ρ (t, a), den ρ (t, b), Val.i32 (ev ρ .i32 c)] := by
    simp [stackAt, den, Val.i32]
  have hst' : (stackAt ρ ⟨ls, (t, selT a b c) :: st⟩).reverse =
      (stackAt ρ ⟨ls, st⟩).reverse ++ [den ρ (t, selT a b c)] := by
    simp [stackAt]
  rw [frameAt_stack f ls _ st] at hw ⊢
  rw [hst', den_selT] at hw
  rw [hst, ← List.append_assoc]
  by_cases hc : ev ρ .i32 c = 0
  · simp only [ne_eq, hc, not_true_eq_false, ite_false] at hw
    rw [hc]
    exact Wp.selectFalse (m := .total) (by simpa using hw)
  · simp only [ne_eq, hc, not_false_eq_true, ite_true] at hw
    exact Wp.selectTrue (m := .total) hc (by simpa using hw)

theorem xone_default {rec : SState → List Instr → Option SState} {S : SState} {i : Instr}
    (hs : ¬ ∃ ts, i = .select ts) (hb : ¬ ∃ bt body, i = .block bt body)
    (hi : ¬ ∃ bt b₁ b₂, i = .if_ bt b₁ b₂) : xone rec S i = sstep S i := by
  cases i <;> first
    | rfl
    | exact absurd ⟨_, rfl⟩ hs
    | exact absurd ⟨_, _, rfl⟩ hb
    | exact absurd ⟨_, _, _, rfl⟩ hi

/-- Inversion of `xone` at a `select`. -/
theorem xone_select_inv {rec : SState → List Instr → Option SState} {ls st : List (IntType × Term)}
    {ts : Option (List ValType)} {S' : SState} (h : xone rec ⟨ls, st⟩ (.select ts) = some S') :
    ∃ t c b a st', st = (.i32, c) :: (t, b) :: (t, a) :: st' ∧
      S' = ⟨ls, (t, selT a b c) :: st'⟩ := by
  simp only [xone] at h
  split at h <;> try contradiction
  rename_i t₃ c t₂ b t₁ a st'
  split at h <;> try contradiction
  rename_i hc
  obtain ⟨rfl, rfl, -⟩ := hc
  cases h
  exact ⟨_, _, _, _, _, rfl, rfl⟩

/-- Inversion of `xone` at a `block`. -/
theorem xone_block_inv {rec : SState → List Instr → Option SState} {ls st : List (IntType × Term)}
    {bt : BlockType} {body : List Instr} {S' : SState}
    (h : xone rec ⟨ls, st⟩ (.block bt body) = some S') :
    ∃ ts A, blockRes? bt = some ts ∧ rec ⟨ls, []⟩ body = some A ∧
      S' = ⟨A.locals, A.stack ++ st⟩ := by
  simp only [xone] at h
  split at h <;> try contradiction
  rename_i ts A hts hA
  split at h <;> try contradiction
  cases h
  exact ⟨ts, A, hts, hA, rfl⟩

/-- Inversion of `xone` at an `if`. -/
theorem xone_if_inv {rec : SState → List Instr → Option SState} {ls st : List (IntType × Term)}
    {bt : BlockType} {b₁ b₂ : List Instr} {S' : SState}
    (h : xone rec ⟨ls, st⟩ (.if_ bt b₁ b₂) = some S') :
    ∃ c st' ts A B lz rz, st = (.i32, c) :: st' ∧ blockRes? bt = some ts ∧
      rec ⟨ls, []⟩ b₁ = some A ∧ rec ⟨ls, []⟩ b₂ = some B ∧
      mergeSlots c A.locals B.locals = some lz ∧ mergeSlots c A.stack B.stack = some rz ∧
      S' = ⟨lz, rz ++ st'⟩ := by
  simp only [xone] at h
  split at h <;> try contradiction
  rename_i t c st' ts hts
  split at h <;> try contradiction
  rename_i ht
  subst ht
  split at h <;> try contradiction
  rename_i A B hA hB
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i lz rz hl hr
  cases h
  exact ⟨c, st', ts, A, B, lz, rz, rfl, hts, hA, hB, hl, hr, rfl⟩

/-- **The forward rule for a `block`.** -/
theorem twp_xone_block {rec : SState → List Instr → Option SState} (ih : BodyOk P host ρ rec)
    {ls st : List (IntType × Term)} {bt : BlockType} {body : List Instr} {S' : SState}
    (h : xone rec ⟨ls, st⟩ (.block bt body) = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) (Q : Post H)
    (hw : TWP P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    TWP P host s (frameAt f ρ ⟨ls, st⟩)
      (vals (us ++ (stackAt ρ ⟨ls, st⟩).reverse) ++ .plain (.block bt body) :: rest) Q := by
  obtain ⟨ts, A, hts, hA, rfl⟩ := xone_block_inv h
  have hst : (stackAt ρ ⟨A.locals, A.stack ++ st⟩).reverse =
      (stackAt ρ ⟨ls, st⟩).reverse ++ (stackAt ρ A).reverse := by
    simp [stackAt]
  have hw' : TWP P host s (frameAt f ρ A)
      (vals (us ++ (stackAt ρ ⟨ls, st⟩).reverse ++ (stackAt ρ A).reverse) ++ rest) Q := by
    rw [List.append_assoc, ← hst]
    exact hw
  exact twp_block_vals hts (fun Q' hQ' => BodyOk.body ih hA s f Q' hQ') hw'

/-- **The forward rule for an `if`**: the branch taken, its locals and stack merged by
`mergeSlots`. -/
theorem twp_xone_if {rec : SState → List Instr → Option SState} (ih : BodyOk P host ρ rec)
    {ls st : List (IntType × Term)} {bt : BlockType} {b₁ b₂ : List Instr} {S' : SState}
    (h : xone rec ⟨ls, st⟩ (.if_ bt b₁ b₂) = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) (Q : Post H)
    (hw : TWP P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    TWP P host s (frameAt f ρ ⟨ls, st⟩)
      (vals (us ++ (stackAt ρ ⟨ls, st⟩).reverse) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  obtain ⟨c, st', ts, A, B, lz, rz, rfl, hts, hA, hB, hl, hr, rfl⟩ := xone_if_inv h
  have hst₀ : (stackAt ρ ⟨ls, (.i32, c) :: st'⟩).reverse =
      (stackAt ρ ⟨ls, st'⟩).reverse ++ [Val.i32 (ev ρ .i32 c)] := by
    simp [stackAt, den, Val.i32]
  have hst₁ : (stackAt ρ ⟨lz, rz ++ st'⟩).reverse =
      (stackAt ρ ⟨ls, st'⟩).reverse ++ (rz.map (den ρ)).reverse := by
    simp [stackAt]
  have hrz : rz.map (den ρ) =
      if ev ρ .i32 c ≠ 0 then A.stack.map (den ρ) else B.stack.map (den ρ) := mergeSlots_den hr
  have hw₁ : TWP P host s (frameAt f ρ ⟨lz, rz ++ st'⟩)
      (vals (us ++ (stackAt ρ ⟨ls, st'⟩).reverse ++ (rz.map (den ρ)).reverse) ++ rest) Q := by
    rw [List.append_assoc, ← hst₁]
    exact hw
  rw [hst₀, ← List.append_assoc]
  refine TWP.if_ ?_
  rw [frameAt_stack f ls _ st']
  by_cases hc : ev ρ .i32 c = 0
  · show TWP P host s (frameAt f ρ ⟨ls, st'⟩) (vals (us ++ (stackAt ρ ⟨ls, st'⟩).reverse) ++
      .plain (.block bt (if ev ρ .i32 c ≠ 0 then b₁ else b₂)) :: rest) Q
    have hrz' : rz.map (den ρ) = B.stack.map (den ρ) := by
      simpa only [ne_eq, hc, not_true_eq_false, ite_false] using hrz
    have hw₂ : TWP P host s (frameAt f ρ ⟨B.locals, B.stack⟩)
        (vals (us ++ (stackAt ρ ⟨ls, st'⟩).reverse ++ (B.stack.map (den ρ)).reverse) ++ rest)
        Q := by
      rw [← hrz', ← frameAt_merge' hl f (rz ++ st') B.stack hc]
      exact hw₁
    split
    next hne => exact absurd hc hne
    next => exact twp_block_vals hts (fun Q' hQ' => BodyOk.body ih hB s f Q' hQ') hw₂
  · show TWP P host s (frameAt f ρ ⟨ls, st'⟩) (vals (us ++ (stackAt ρ ⟨ls, st'⟩).reverse) ++
      .plain (.block bt (if ev ρ .i32 c ≠ 0 then b₁ else b₂)) :: rest) Q
    have hrz' : rz.map (den ρ) = A.stack.map (den ρ) := by
      simpa only [ne_eq, hc, not_false_eq_true, ite_true] using hrz
    have hw₂ : TWP P host s (frameAt f ρ ⟨A.locals, A.stack⟩)
        (vals (us ++ (stackAt ρ ⟨ls, st'⟩).reverse ++ (A.stack.map (den ρ)).reverse) ++ rest)
        Q := by
      rw [← hrz', ← frameAt_merge hl f (rz ++ st') A.stack hc]
      exact hw₁
    split
    next => exact twp_block_vals hts (fun Q' hQ' => BodyOk.body ih hA s f Q' hQ') hw₂
    next hne => exact absurd (not_not.mp hne) hc

/-- **The forward rule for one instruction.** -/
theorem twp_xone {rec : SState → List Instr → Option SState} (ih : BodyOk P host ρ rec)
    {S S' : SState} {i : Instr} (h : xone rec S i = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) (Q : Post H)
    (hw : TWP P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    TWP P host s (frameAt f ρ S) (vals (us ++ (stackAt ρ S).reverse) ++ .plain i :: rest) Q := by
  rcases S with ⟨ls, st⟩
  by_cases hs : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hs
    obtain ⟨t, c, b, a, st', rfl, rfl⟩ := xone_select_inv h
    exact twp_select hw
  by_cases hb : ∃ bt body, i = .block bt body
  · obtain ⟨bt, body, rfl⟩ := hb
    exact twp_xone_block ih h s f us rest Q hw
  by_cases hi : ∃ bt b₁ b₂, i = .if_ bt b₁ b₂
  · obtain ⟨bt, b₁, b₂, rfl⟩ := hi
    exact twp_xone_if ih h s f us rest Q hw
  exact wp_sstep (m := .total) (xone_default hs hb hi ▸ h) s f us rest hw

/-- **The forward rule for symbolic execution of a body.** -/
theorem twp_xexec (n : Nat) : BodyOk P host ρ (xexec n) := by
  induction n with
  | zero =>
    intro S S' a h
    simp [xexec] at h
  | succ n ih =>
    intro S S' a h s f us rest Q hw
    cases a with
    | nil =>
      have hS : S = S' := by simpa only [xexec, Option.some.injEq] using h
      subst hS
      simpa [codeAt] using hw
    | cons i is =>
      cases h₁ : xone (xexec n) S i with
      | none => simp [xexec, h₁] at h
      | some S₁ =>
        have h' : xexec n S₁ is = some S' := by simpa [xexec, h₁] using h
        have h₂ : TWP P host s (frameAt f ρ S₁) (codeAt ρ S₁ us is rest) Q := ih h' s f us rest Q hw
        have h₃ := twp_xone ih h₁ s f us (expression is ++ rest) Q (by simpa [codeAt] using h₂)
        simpa [codeAt, expression] using h₃

end Silmaril.Proofs.Wasm.Auto.Bridge