module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.DCECutTyping
public import Silmaril.Wasm.Binaryen.CtxTyping

@[expose] public section

/-! # The sketch bridge for DCE (operational simulation development, item 1)

`DceCut` (`DCECutTyping.lean`) is the code relation that safe DCE produces on
lowered code (`dceL_cut`). Its generators are primitive cuts after a stack-polymorphic
instruction and congruence; every one is an instance of the tooling's closure
`Sim.InstrsRel Sim.dceBI` (`DceCut.instrsRel`): a cut `a ++ b ↝ a` with `a` ending in a
bottom instruction is a `dceBI` base pair, and `trans` composes because `dceBI`
deletions nest (both sides agree up to the first bottom at every nesting level).

Plugging related sequences into a one-hole context and a module body keeps the
bodies related (`BCtx.dceCut_plug`, `withBody_bodiesRel`), so `exportEquiv_dce`
(`CodeSimModule.lean`) applies to every `SeqRefines` instance.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- The sketch's Boolean bottom test is the tooling's `BotInstr`. -/
theorem botInstr_bot {i : Instr} (h : botInstr i = true) : Sim.BotInstr i := by
  unfold botInstr at h
  split at h <;> first | exact trivial | simp at h

/-- A primitive cut is a `dceBI` base pair. -/
theorem EndsInBot.dceBI {a : List Instr} (h : EndsInBot a) (b : List Instr) :
    Sim.dceBI (a ++ b) a := by
  obtain ⟨pre, i, rfl, hi⟩ := h
  exact ⟨pre, i, b, [], botInstr_bot hi, by simp, by simp⟩

/-! ## Canonical truncation

`truncL` deletes everything after the first bottom instruction of a sequence, at
every nesting level. Sequences with equal truncations are `InstrsRel dceBI`-related
(`instrsRel_of_truncL`), and `DceCut` preserves truncations (`DceCut.truncL_eq`);
this handles `DceCut.trans`, which is not a closure generator.
-/

mutual
/-- Truncate the bodies of a structured instruction. -/
def truncI : Instr → Instr
  | .block bt b => .block bt (truncL b)
  | .loop bt b => .loop bt (truncL b)
  | .if_ bt b₁ b₂ => .if_ bt (truncL b₁) (truncL b₂)
  | .tryTable bt cs b => .tryTable bt cs (truncL b)
  | i => i
/-- Truncate a sequence after its first bottom instruction, at every level. -/
def truncL : List Instr → List Instr
  | [] => []
  | i :: is => if botInstr i then [i] else truncI i :: truncL is
end

theorem botInstr_truncI (i : Instr) : botInstr (truncI i) = botInstr i := by
  cases i <;> rfl

theorem truncL_append (a b : List Instr) :
    truncL (a ++ b) = truncL a ++ (if a.any botInstr then [] else truncL b) := by
  induction a with
  | nil => simp [truncL]
  | cons i is ih =>
    by_cases hi : botInstr i = true
    · simp [truncL, hi]
    · simp [truncL, hi, ih]

theorem any_truncL (a : List Instr) : (truncL a).any botInstr = a.any botInstr := by
  induction a with
  | nil => rfl
  | cons i is ih =>
    by_cases hi : botInstr i = true
    · simp [truncL, hi]
    · simp [truncL, hi, ih, botInstr_truncI]

/-- Every instruction is flat or one of the four structured forms. -/
theorem instr_cases (i : Instr) : structuredInstr i = false ∨ (∃ bt b, i = .block bt b) ∨
    (∃ bt b, i = .loop bt b) ∨ (∃ bt b₁ b₂, i = .if_ bt b₁ b₂) ∨
    (∃ bt cs b, i = .tryTable bt cs b) := by
  cases i <;> simp [structuredInstr]

theorem truncI_flat {i : Instr} (hf : structuredInstr i = false) : truncI i = i := by
  cases i <;> first | rfl | simp [structuredInstr] at hf

theorem truncI_block_inv {j : Instr} {bt : BlockType} {c : List Instr}
    (h : truncI j = .block bt c) : ∃ b, j = .block bt b ∧ truncL b = c := by
  rcases instr_cases j with hf | ⟨bt', b, rfl⟩ | ⟨bt', b, rfl⟩ | ⟨bt', b₁, b₂, rfl⟩ |
      ⟨bt', cs, b, rfl⟩
  · rw [truncI_flat hf] at h; subst h; simp [structuredInstr] at hf
  · simp only [truncI, Instr.block.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, rfl, rfl⟩
  all_goals simp [truncI] at h

theorem truncI_loop_inv {j : Instr} {bt : BlockType} {c : List Instr}
    (h : truncI j = .loop bt c) : ∃ b, j = .loop bt b ∧ truncL b = c := by
  rcases instr_cases j with hf | ⟨bt', b, rfl⟩ | ⟨bt', b, rfl⟩ | ⟨bt', b₁, b₂, rfl⟩ |
      ⟨bt', cs, b, rfl⟩
  · rw [truncI_flat hf] at h; subst h; simp [structuredInstr] at hf
  · simp [truncI] at h
  · simp only [truncI, Instr.loop.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, rfl, rfl⟩
  all_goals simp [truncI] at h

theorem truncI_if_inv {j : Instr} {bt : BlockType} {c₁ c₂ : List Instr}
    (h : truncI j = .if_ bt c₁ c₂) :
    ∃ b₁ b₂, j = .if_ bt b₁ b₂ ∧ truncL b₁ = c₁ ∧ truncL b₂ = c₂ := by
  rcases instr_cases j with hf | ⟨bt', b, rfl⟩ | ⟨bt', b, rfl⟩ | ⟨bt', b₁, b₂, rfl⟩ |
      ⟨bt', cs, b, rfl⟩
  · rw [truncI_flat hf] at h; subst h; simp [structuredInstr] at hf
  · simp [truncI] at h
  · simp [truncI] at h
  · simp only [truncI, Instr.if_.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨b₁, b₂, rfl, rfl, rfl⟩
  · simp [truncI] at h

theorem truncI_tryTable_inv {j : Instr} {bt : BlockType} {cs : List Catch} {c : List Instr}
    (h : truncI j = .tryTable bt cs c) : ∃ b, j = .tryTable bt cs b ∧ truncL b = c := by
  rcases instr_cases j with hf | ⟨bt', b, rfl⟩ | ⟨bt', b, rfl⟩ | ⟨bt', b₁, b₂, rfl⟩ |
      ⟨bt', cs', b, rfl⟩
  · rw [truncI_flat hf] at h; subst h; simp [structuredInstr] at hf
  · simp [truncI] at h
  · simp [truncI] at h
  · simp [truncI] at h
  · simp only [truncI, Instr.tryTable.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨b, rfl, rfl⟩

/-- A sequence is related to its truncation (by recursion on a size bound). -/
theorem truncL_rel_lt : ∀ (n : Nat) (a : List Instr), sizeOf a < n →
    Sim.InstrsRel Sim.dceBI a (truncL a)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _ => .nil
  | n + 1, i :: is, h => by
      have hsz : 1 + sizeOf i + sizeOf is < n + 1 := by simpa using h
      by_cases hi : botInstr i = true
      · simp only [truncL, hi, ite_true]
        exact .base ⟨[], i, is, [], botInstr_bot hi, rfl, rfl⟩
      · simp only [truncL, hi, Bool.false_eq_true, ite_false]
        refine .cons ?_ (truncL_rel_lt n is (by omega))
        rcases instr_cases i with hf | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
            ⟨bt, cs, b, rfl⟩
        · rw [truncI_flat hf]; exact .refl _
        · simp only [Instr.block.sizeOf_spec] at hsz
          exact .block bt (truncL_rel_lt n b (by omega))
        · simp only [Instr.loop.sizeOf_spec] at hsz
          exact .loop bt (truncL_rel_lt n b (by omega))
        · simp only [Instr.if_.sizeOf_spec] at hsz
          exact .if_ bt (truncL_rel_lt n b₁ (by omega)) (truncL_rel_lt n b₂ (by omega))
        · simp only [Instr.tryTable.sizeOf_spec] at hsz
          exact .tryTable bt cs (truncL_rel_lt n b (by omega))

theorem truncL_rel (a : List Instr) : Sim.InstrsRel Sim.dceBI a (truncL a) :=
  truncL_rel_lt _ a (Nat.lt_succ_self _)

/-- An instruction is related to its truncation. -/
theorem truncI_rel (i : Instr) : Sim.InstrRel Sim.dceBI i (truncI i) := by
  rcases instr_cases i with hf | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
      ⟨bt, cs, b, rfl⟩
  · rw [truncI_flat hf]; exact .refl _
  · exact .block bt (truncL_rel b)
  · exact .loop bt (truncL_rel b)
  · exact .if_ bt (truncL_rel b₁) (truncL_rel b₂)
  · exact .tryTable bt cs (truncL_rel b)

/-- Sequences with equal truncations are related (by recursion on a size bound). -/
theorem instrsRel_of_truncL_lt : ∀ (n : Nat) (a b : List Instr), sizeOf a < n →
    truncL a = truncL b → Sim.InstrsRel Sim.dceBI a b
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], [], _, _ => .nil
  | _ + 1, [], j :: js, _, h => by
      by_cases hj : botInstr j = true <;> simp [truncL, hj] at h
  | _ + 1, i :: is, [], _, h => by
      by_cases hi : botInstr i = true <;> simp [truncL, hi] at h
  | n + 1, i :: is, j :: js, hn, h => by
      have hsz : 1 + sizeOf i + sizeOf is < n + 1 := by simpa using hn
      by_cases hi : botInstr i = true <;> by_cases hj : botInstr j = true
      · simp only [truncL, hi, hj, ite_true, List.cons.injEq, and_true] at h
        subst h
        exact .base ⟨[], i, is, js, botInstr_bot hi, rfl, rfl⟩
      · simp only [truncL, hi, hj, ite_true, Bool.false_eq_true, ite_false,
          List.cons.injEq] at h
        have := botInstr_truncI j
        rw [← h.1] at this
        simp_all
      · simp only [truncL, hi, hj, ite_true, Bool.false_eq_true, ite_false,
          List.cons.injEq] at h
        have := botInstr_truncI i
        rw [h.1] at this
        simp_all
      · simp only [truncL, hi, hj, Bool.false_eq_true, ite_false, List.cons.injEq] at h
        obtain ⟨h₁, h₂⟩ := h
        refine .cons ?_ (instrsRel_of_truncL_lt n is js (by omega) h₂)
        rcases instr_cases i with hf | ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
            ⟨bt, cs, b, rfl⟩
        · rw [truncI_flat hf] at h₁
          rw [h₁]
          have := (truncI_rel j).flip
          rwa [Sim.dceBI_flip] at this
        · simp only [Instr.block.sizeOf_spec] at hsz
          obtain ⟨b', rfl, hb⟩ := truncI_block_inv h₁.symm
          exact .block bt (instrsRel_of_truncL_lt n b b' (by omega) hb.symm)
        · simp only [Instr.loop.sizeOf_spec] at hsz
          obtain ⟨b', rfl, hb⟩ := truncI_loop_inv h₁.symm
          exact .loop bt (instrsRel_of_truncL_lt n b b' (by omega) hb.symm)
        · simp only [Instr.if_.sizeOf_spec] at hsz
          obtain ⟨b₁', b₂', rfl, hb₁, hb₂⟩ := truncI_if_inv h₁.symm
          exact .if_ bt (instrsRel_of_truncL_lt n b₁ b₁' (by omega) hb₁.symm)
            (instrsRel_of_truncL_lt n b₂ b₂' (by omega) hb₂.symm)
        · simp only [Instr.tryTable.sizeOf_spec] at hsz
          obtain ⟨b', rfl, hb⟩ := truncI_tryTable_inv h₁.symm
          exact .tryTable bt cs (instrsRel_of_truncL_lt n b b' (by omega) hb.symm)

/-- **Sequences with equal truncations are related.** -/
theorem instrsRel_of_truncL (a b : List Instr) (h : truncL a = truncL b) :
    Sim.InstrsRel Sim.dceBI a b :=
  instrsRel_of_truncL_lt _ a b (Nat.lt_succ_self _) h

/-- `DceCut` preserves truncations. -/
theorem DceCut.truncL_eq {a b : List Instr} (h : DceCut a b) : truncL a = truncL b := by
  induction h with
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | append _ _ ih₁ ih₂ =>
    rw [truncL_append, truncL_append, ← any_truncL, ih₁, ih₂, any_truncL]
  | @cut a b hb =>
    obtain ⟨pre, i, rfl, hi⟩ := hb
    rw [truncL_append]
    simp [hi]
  | block bt _ ih => simp [truncL, truncI, botInstr, ih]
  | loop bt _ ih => simp [truncL, truncI, botInstr, ih]
  | if_ bt _ _ ih₁ ih₂ => simp [truncL, truncI, botInstr, ih₁, ih₂]
  | tryTable bt cs _ ih => simp [truncL, truncI, botInstr, ih]

/-- **`DceCut` is an instance of the tooling's closure.** -/
theorem DceCut.instrsRel {a b : List Instr} (h : DceCut a b) : Sim.InstrsRel Sim.dceBI a b :=
  instrsRel_of_truncL a b h.truncL_eq

/-- `DceCut` is a congruence for one-hole contexts. -/
theorem BCtx.dceCut_plug (K : BCtx) {a b : List BExpr}
    (h : DceCut (BExpr.lowerList a) (BExpr.lowerList b)) :
    DceCut (BExpr.lowerList (K.plug a)) (BExpr.lowerList (K.plug b)) := by
  have hs : ∀ (pre post : List BExpr) {a b : List BExpr},
      DceCut (BExpr.lowerList a) (BExpr.lowerList b) →
      DceCut (BExpr.lowerList (pre ++ a ++ post)) (BExpr.lowerList (pre ++ b ++ post)) := by
    intro pre post a b h
    simp only [BExpr.lowerList_append]
    exact DceCut.append (DceCut.append (.refl _) h) (.refl _)
  induction K with
  | hole => exact h
  | seq pre k post ih => exact hs pre post ih
  | op i pre k post ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_op]
    exact DceCut.append (hs pre post ih) (.refl _)
  | block bt pre k post ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.block bt (hs pre post ih)
  | loop bt pre k post ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.loop bt (hs pre post ih)
  | ifCond bt pre k post t e ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.append (hs pre post ih) (.refl _)
  | ifThen bt c pre k post e ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.append (.refl _) (DceCut.if_ bt (hs pre post ih) (.refl _))
  | ifElse bt c t pre k post ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.append (.refl _) (DceCut.if_ bt (.refl _) (hs pre post ih))
  | tryTable bt cs pre k post ih =>
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower]
    exact DceCut.tryTable bt cs (hs pre post ih)

/-- Replacing one body by a related one gives modules with related bodies. -/
theorem withBody_bodiesRel {BI : List Instr → List Instr → Prop} (m : BModule) (g : Nat)
    {a b : List BExpr} (h : Sim.InstrsRel BI (BExpr.lowerList a) (BExpr.lowerList b)) :
    ModuleBodiesRel BI (m.withBody g a).lower (m.withBody g b).lower := by
  have key : ∀ (fs : List BFunc) (g : Nat), List.Forall₂ (fun f g : Func =>
      f.type = g.type ∧ f.locals = g.locals ∧ Sim.InstrsRel BI f.body g.body)
      ((modifyAt (fun f => { f with body := a }) g fs).map
        (Declaration.Func.mapBody BExpr.lowerList))
      ((modifyAt (fun f => { f with body := b }) g fs).map
        (Declaration.Func.mapBody BExpr.lowerList)) := by
    intro fs
    induction fs with
    | nil => intro g; cases g <;> exact .nil
    | cons f fs ih =>
      intro g
      cases g with
      | zero =>
        refine .cons ⟨rfl, rfl, h⟩ ?_
        clear ih
        induction fs with
        | nil => exact .nil
        | cons f' fs ih' => exact .cons ⟨rfl, rfl, Sim.InstrsRel.refl _⟩ ih'
      | succ g => exact .cons ⟨rfl, rfl, Sim.InstrsRel.refl _⟩ (ih g)
  exact ⟨rfl, key m.funcs g⟩

/-- **The DCE bridge.** Sequences whose lowerings are `DceCut`-related, typed at
`C ⊢ it`, are contextually equivalent for every code-parametric host. -/
theorem dceCut_seqEquivH {P : Profile} {C : Context} {it : InstrType} {es es' : List BExpr}
    (hcut : DceCut (BExpr.lowerList es) (BExpr.lowerList es'))
    (h : SeqOk C es it) (h' : SeqOk C es' it) :
    SeqEquivH HostsP (· = ·) P C it es' es := by
  refine ⟨⟨h', h, fun host m g K hh h₁ h₂ => ?_⟩, ⟨h, h', fun host m g K hh h₁ h₂ => ?_⟩⟩
  · have hrel := withBody_bodiesRel m g (BCtx.dceCut_plug K hcut).instrsRel
    exact (exportEquiv_dce hh hrel.dce_symm h₁ h₂).1
  · have hrel := withBody_bodiesRel m g (BCtx.dceCut_plug K hcut).instrsRel
    exact (exportEquiv_dce hh hrel h₁ h₂).1.mono fun _ _ e => e.symm

end Silmaril.Wasm.Binaryen
