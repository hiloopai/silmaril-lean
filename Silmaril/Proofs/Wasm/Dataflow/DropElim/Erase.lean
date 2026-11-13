module

public import Silmaril.Wasm.Dataflow.DropElim.Defs
public import Silmaril.Wasm.Dataflow.Fragment.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Mathlib.Data.List.Chain

/-!
# an earlier step of the two-pass DCE: the erasure relation

* `dropElim_erase`: the pass is an erasure;
* `Erase.result`, `Erase.returning`: results and pending returns are erased only to
  themselves;
* `Erase.split`: an erasure splits at its first active rewrite (`Erase.Atom`), with the
  values before it unchanged;
* `Erase.exit_prefix`: erasure keeps a branch, return or tail-call exit and the values
  before it; only the unreachable suffix can change.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

theorem Erase.cons {a a' : List Admin} {b : Admin} {bs bs' : List Admin}
    (h : Erase [b] a) (hs : Erase bs bs') (ha : a' = a ++ bs') : Erase (b :: bs) a' := by
  subst ha
  exact Erase.append (a := [b]) h hs

/-- Any code is erased to itself. -/
theorem Erase.refl : ∀ c : List Admin, Erase c c
  | [] => .nil
  | a :: as => Erase.cons (.keep a) (Erase.refl as) rfl

@[simp] theorem adminPureArity_toAdmin (v : Val) : adminPureArity? v.toAdmin = some 0 := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

/-- A value followed by `drop` is erased. -/
theorem Erase.val_drop (v : Val) : Erase [v.toAdmin, .plain .drop] [] :=
  Erase.pure (adminPureArity_toAdmin v)

/-! ## The pass is an erasure -/

/-- A dropped removable producer in source code. -/
theorem erase_pure_drop {i : Instr} {n : Nat} (hn : pureArity? i = some n) {is is' : List Instr}
    (h : Erase (expression is) (expression is')) :
    Erase (expression (i :: .drop :: is)) (expression (List.replicate n .drop ++ is')) := by
  have hp : adminPureArity? (.plain i) = some n := by simpa [adminPureArity?] using hn
  simpa [expression, List.map_replicate] using Erase.append (Erase.pure hp) h

/-- The source transform of `i :: j :: is` away from a dropped producer. -/
theorem dropElimSeq_cons_cons {i j : Instr} {is : List Instr}
    (h : pureArity? i = none ∨ isDrop j = false) :
    dropElimSeq (i :: j :: is) = dropElimInstr i :: dropElimSeq (j :: is) := by
  rcases h with h | h <;> simp [dropElimSeq, h]
  split <;> rfl

theorem isDrop_eq_true {j : Instr} (h : isDrop j = true) : j = .drop := by
  cases j <;> first | rfl | simp [isDrop] at h

mutual
/-- One instruction is erased to its pass-2 image. -/
theorem erase_dropElimInstr (i : Instr) : Erase [.plain i] [.plain (dropElimInstr i)] := by
  cases i <;> first
    | exact .keep _
    | (simp only [dropElimInstr]; exact .block _ (erase_dropElimSeq _))
    | (simp only [dropElimInstr]; exact .loop _ (erase_dropElimSeq _))
    | (simp only [dropElimInstr]; exact .if_ _ (erase_dropElimSeq _) (erase_dropElimSeq _))
termination_by sizeOf i

/-- An instruction sequence is erased to its pass-2 image. -/
theorem erase_dropElimSeq (b : List Instr) :
    Erase (expression b) (expression (dropElimSeq b)) := by
  match b with
  | [] => exact .nil
  | [i] => simpa [dropElimSeq, expression] using erase_dropElimInstr i
  | i :: j :: is =>
      by_cases hd : ∃ n, pureArity? i = some n ∧ isDrop j = true
      · obtain ⟨n, hn, hj⟩ := hd
        have hj' : j = .drop := isDrop_eq_true hj
        subst hj'
        have he : dropElimSeq (i :: .drop :: is) = List.replicate n .drop ++ dropElimSeq is := by
          simp [dropElimSeq, hn, isDrop]
        rw [he]
        exact erase_pure_drop hn (erase_dropElimSeq is)
      · have hk : pureArity? i = none ∨ isDrop j = false := by
          cases hn : pureArity? i <;> simp_all
        rw [dropElimSeq_cons_cons hk]
        exact Erase.cons (erase_dropElimInstr i) (erase_dropElimSeq (j :: is))
          (by simp [expression])
termination_by sizeOf b
end

/-- The source function is an erasure. -/
theorem dropElim_erase (e : Expr) : Erase (expression e) (expression (dropElim e)) :=
  erase_dropElimSeq e

/-! ## Results -/

/-- The administrative instructions that erasure cannot rewrite on their own. -/
def InertAdmin (a : Admin) : Prop :=
  a.val? ≠ none ∨ a = .plain .throwRef ∨ a = .plain .return_

/-- On terminal-shaped inert code with no `THROW_REF` before another instruction, erasure
is the identity. The adjacency condition is essential: `throwing a ++ [return]` is erased to
`throwing a`. -/
theorem Erase.eq_of_inert {c d : List Admin} (h : Erase c d) (hc : ∀ a ∈ c, InertAdmin a)
    (ht : c.IsChain fun a _ => a ≠ .plain .throwRef) : d = c := by
  induction h with
  | nil => rfl
  | append _ _ ih₁ ih₂ =>
      rw [ih₁ (fun a ha => hc a (List.mem_append_left _ ha)) ht.left_of_append,
        ih₂ (fun a ha => hc a (List.mem_append_right _ ha)) ht.right_of_append]
  | keep => rfl
  | pure => exact absurd (hc (.plain .drop) (by simp)) (by simp [InertAdmin, Admin.val?])
  | block bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [InertAdmin, Admin.val?])
  | loop bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [InertAdmin, Admin.val?])
  | if_ bt => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [InertAdmin, Admin.val?])
  | label n => exact absurd (hc _ (List.mem_singleton_self _)) (by simp [InertAdmin, Admin.val?])
  | trap => exact absurd (hc .trap (by simp)) (by simp [InertAdmin, Admin.val?])
  | throwRef a rest =>
      cases rest with
      | nil => rfl
      | cons b rest => simp [throwing] at ht

theorem Erase.eq_nil {d : List Admin} (h : Erase [] d) : d = [] :=
  h.eq_of_inert (by simp) (by simp)

theorem Erase.eq_trap {c d : List Admin} (h : Erase c d) (hc : c = [.trap]) : d = [.trap] := by
  induction h with
  | nil => simp at hc
  | append ha hb ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ha.eq_nil, ih₂ rfl]; rfl
      · rw [ih₁ rfl, hb.eq_nil]; rfl
  | keep => exact hc
  | trap => rfl
  | throwRef => simp [throwing] at hc
  | _ => simp at hc

theorem chain_vals_append (vs : List Val) {rest : List Admin}
    (hr : rest.IsChain fun a _ => a ≠ .plain .throwRef) :
    (vals vs ++ rest).IsChain fun a _ => a ≠ .plain .throwRef := by
  induction vs with
  | nil => exact hr
  | cons v vs ih =>
      apply List.IsChain.cons ih
      intro y _ he
      have hv := Admin.val?_toAdmin v
      rw [he] at hv
      cases hv

theorem inert_vals_append {vs : List Val} {rest : List Admin} (hr : ∀ a ∈ rest, InertAdmin a) :
    ∀ a ∈ vals vs ++ rest, InertAdmin a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact .inl (SingleThreaded.Det.mem_vals ha)
  · exact hr a ha

/-- Erasure fixes results, including thrown exceptions. -/
theorem Erase.result {r : Result} {d : List Admin} (h : Erase r.toAdmin d) : d = r.toAdmin := by
  cases r with
  | values vs =>
      exact Erase.eq_of_inert (c := vals vs) h (fun a ha => .inl (SingleThreaded.Det.mem_vals ha))
        (by simpa using chain_vals_append vs (rest := []) (by simp))
  | throw x =>
      refine h.eq_of_inert (fun a ha => ?_) (by simp [Result.toAdmin])
      simp only [Result.toAdmin, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inl (by simp [Admin.val?])
      · exact .inr (.inl rfl)
  | trap => exact h.eq_trap rfl

/-- Erasure fixes pending returns and their values. -/
theorem Erase.returning {vs : List Val} {d : List Admin}
    (h : Erase (vals vs ++ [.plain .return_]) d) : d = vals vs ++ [.plain .return_] :=
  h.eq_of_inert (inert_vals_append (by simp [InertAdmin]))
    (chain_vals_append vs (by simp))

/-! ## The first active rewrite -/

/-- The shape of an erasure split at its first active rewrite: all values (unchanged), or
unchanged values, an active rewrite and an erased rest. -/
def Erase.SplitForm (c d : List Admin) : Prop :=
  (∃ vs, c = vals vs ∧ d = vals vs) ∨
    ∃ (vs : List Val) (x y rest rest' : List Admin),
      c = vals vs ++ x ++ rest ∧ d = vals vs ++ y ++ rest' ∧ Erase.Atom x y ∧ Erase rest rest'

theorem Erase.SplitForm.atom {x y : List Admin} (h : Erase.Atom x y) : Erase.SplitForm x y :=
  .inr ⟨[], x, y, [], [], by simp, by simp, h, .nil⟩

theorem Erase.SplitForm.append {a a' b b' : List Admin} (ha : Erase.SplitForm a a')
    (hb : Erase.SplitForm b b') (hb' : Erase b b') : Erase.SplitForm (a ++ b) (a' ++ b') := by
  rcases ha with ⟨vs, rfl, rfl⟩ | ⟨vs, x, y, rest, rest', rfl, rfl, hxy, hr⟩
  · rcases hb with ⟨ws, rfl, rfl⟩ | ⟨ws, x, y, rest, rest', rfl, rfl, hxy, hr⟩
    · exact .inl ⟨vs ++ ws, by simp, by simp⟩
    · exact .inr ⟨vs ++ ws, x, y, rest, rest', by simp, by simp, hxy, hr⟩
  · exact .inr ⟨vs, x, y, rest ++ _, rest' ++ _, by simp, by simp, hxy, .append hr hb'⟩

theorem Erase.SplitForm.keep (a : Admin) : Erase.SplitForm [a] [a] := by
  cases hv : a.val? with
  | some v =>
    exact .inl ⟨[v], by simp [vals, Admin.eq_of_val? hv], by simp [vals, Admin.eq_of_val? hv]⟩
  | none => exact .atom (.keep a hv)

/-- Split at the first active rewrite. Earlier values are unchanged. -/
theorem Erase.split {c d : List Admin} (h : Erase c d) : Erase.SplitForm c d := by
  induction h with
  | nil => exact .inl ⟨[], rfl, rfl⟩
  | append _ hb ih₁ ih₂ => exact ih₁.append ih₂ hb
  | keep a => exact .keep a
  | pure h => exact .atom (.pure h)
  | block bt h => exact .atom (.block bt h)
  | loop bt h => exact .atom (.loop bt h)
  | if_ bt h₁ h₂ => exact .atom (.if_ bt h₁ h₂)
  | label n hc hb _ => exact .atom (.label n hc hb)
  | trap rest => exact .atom (.trap rest)
  | throwRef a rest => exact .atom (.throwRef a rest)

/-! ## Exits -/

set_option linter.unusedTactic false in
/-- What an exit instruction is not. -/
theorem Erase.ExitOne.facts {a : Admin} (ha : Erase.ExitOne a) :
    a.val? = none ∧ adminPureArity? a = none ∧ a ≠ .trap ∧ a ≠ .plain .throwRef ∧
    a ≠ .plain .drop ∧ (∀ bt b, a ≠ .plain (.block bt b)) ∧ (∀ bt b, a ≠ .plain (.loop bt b)) ∧
    (∀ bt b₁ b₂, a ≠ .plain (.if_ bt b₁ b₂)) ∧ (∀ n cont body, a ≠ .label n cont body) := by
  rcases ha with ⟨l, rfl⟩ | rfl | ha
  · simp [Admin.val?, adminPureArity?, pureArity?]
  · simp [Admin.val?, adminPureArity?, pureArity?]
  · cases a <;> simp only [Admin.IsReturnCallRef] at ha
    case plain i => cases i <;> simp_all [Admin.val?, adminPureArity?, pureArity?]
    all_goals simp [Admin.val?, adminPureArity?]

/-- The first active rewrite at an exit instruction keeps it, with the values before it. -/
theorem Erase.Atom.exit_eq {vs ws : List Val} {a : Admin} {rest x y r : List Admin}
    (hxy : Erase.Atom x y) (hk : Erase.ExitOne a) (h : vals vs ++ a :: rest = vals ws ++ x ++ r) :
    vs = ws ∧ y = [a] := by
  obtain ⟨ha, hp, ht, hh, hd, hblock, hloop, hif, hlabel⟩ := Erase.ExitOne.facts hk
  cases hxy with
  | keep b hb =>
    obtain ⟨hvs, hab, -⟩ := Sim.vals_append_cons_inj ha hb (by simpa using h)
    exact ⟨hvs, by rw [hab]⟩
  | @pure b n hb =>
    show vs = ws ∧ List.replicate n (.plain .drop) = [a]
    cases hv : b.val? with
    | none =>
      have hab : a = b := (Sim.vals_append_cons_inj ha hv (by simpa using h)).2.1
      exact absurd (hab ▸ hb) (by simp [hp])
    | some v =>
      have h' : vals vs ++ a :: rest = vals (ws ++ [v]) ++ .plain .drop :: r := by
        simpa [Admin.eq_of_val? hv, vals] using h
      exact absurd (Sim.vals_append_cons_inj ha rfl h').2.1 hd
  | block bt hb =>
    exact absurd (Sim.vals_append_cons_inj ha rfl (by simpa using h)).2.1 (hblock _ _)
  | loop bt hb => exact absurd (Sim.vals_append_cons_inj ha rfl (by simpa using h)).2.1 (hloop _ _)
  | if_ bt hb₁ hb₂ =>
    exact absurd (Sim.vals_append_cons_inj ha rfl (by simpa using h)).2.1 (hif _ _ _)
  | label n hc hb =>
    exact absurd (Sim.vals_append_cons_inj ha rfl (by simpa using h)).2.1 (hlabel _ _ _)
  | trap junk => exact absurd (Sim.vals_append_cons_inj ha rfl (by simpa using h)).2.1 ht
  | throwRef x junk =>
    have h' : vals vs ++ a :: rest =
        vals (ws ++ [.ref (.exn x)]) ++ .plain .throwRef :: (junk ++ r) := by
      simpa [vals, throwing, Val.toAdmin] using h
    exact absurd (Sim.vals_append_cons_inj ha rfl h').2.1 hh

/-- Erasure preserves every value before a branch, return or tail-call exit, and the exit
instruction itself. Only its unreachable suffix can change. -/
theorem Erase.exit_prefix {vs : List Val} {a : Admin} {rest d : List Admin}
    (h : Erase (vals vs ++ a :: rest) d) (hk : Erase.ExitOne a) :
    ∃ rest', d = vals vs ++ a :: rest' := by
  rcases h.split with ⟨us, hc, _⟩ | ⟨ws, x, y, r, r', hc, rfl, hxy, _⟩
  · have hm : a ∈ vals us := by rw [← hc]; simp
    exact (SingleThreaded.Det.mem_vals hm (Erase.ExitOne.facts hk).1).elim
  · obtain ⟨rfl, rfl⟩ := hxy.exit_eq hk hc
    exact ⟨r', by simp⟩

theorem Erase.exit_prefix_append {vs : List Val} {a : Admin} {rest d : List Admin}
    (h : Erase (vals vs ++ [a] ++ rest) d) (hk : Erase.ExitOne a) :
    ∃ rest', d = vals vs ++ [a] ++ rest' := by
  obtain ⟨rest', he⟩ := Erase.exit_prefix (by simpa using h) hk
  exact ⟨rest', by simpa using he⟩

end Silmaril.Wasm.Dataflow
