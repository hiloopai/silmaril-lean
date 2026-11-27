module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Read.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.GrammarStep

/-! # The reader of the grammar is exact at every size -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow emptyDispatchRep)
open Paper.TypeCategory (sumInl sumInr blockRoute blockStep iterate_blockStep iterate_fixpoint)
open Paper.TypeCategory (whiskerLeft_iterate iterate_naturality)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback (carryExit)
open Bridge.NamedFlat (tabulate)

/-! ## Reading every index -/

theorem tabulate_sound {A : Type} : ∀ (n : Nat) (f : Fin n → Option A) (g : Fin n → A),
    tabulate n f = some g → ∀ i, f i = some (g i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, g, h, i => by
    cases h0 : f 0 with
    | none => simp [tabulate, h0] at h
    | some head =>
      cases ht : tabulate n (fun i => f i.succ) with
      | none => simp [tabulate, h0, ht] at h
      | some tail =>
        simp [tabulate, h0, ht] at h
        subst h
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using h0
        · simpa using tabulate_sound n _ tail ht j

theorem tabulate_some {A : Type} : ∀ (n : Nat) (g : Fin n → A), tabulate n (fun i => some (g i)) = some g
  | 0, g => congrArg some (funext fun i => i.elim0)
  | n + 1, g => by
    have ih := tabulate_some n (fun i => g i.succ)
    simp only [tabulate, Option.bind_some, ih, Option.map_some]
    refine congrArg some (funext fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

section Reader

variable {K : Nat}

/-! ## The pieces of the reader -/

theorem fin_ofFin (i : Fin (K + 1 + 1)) : (NLeaf.ofFin i).fin = i := by
  unfold NLeaf.ofFin
  split
  · rfl
  · rename_i h
    exact Fin.ext (by
      have := i.isLt
      simp only [NLeaf.fin, Fin.val_last]
      omega)

theorem ofFin_fin : (b : NLeaf K) → NLeaf.ofFin b.fin = b
  | .exit => by simp [NLeaf.ofFin, NLeaf.fin]
  | .goto j => by simp [NLeaf.ofFin, NLeaf.fin]

theorem startOfFinN_eq {i : Fin (K + 1 + 1)} {s : Fin (K + 1)} (h : startOfFinN i = some s) :
    i = s.castSucc := by
  unfold startOfFinN at h
  split at h
  · cases h
    rfl
  · cases h

theorem startOfFinN_castSucc (s : Fin (K + 1)) : startOfFinN s.castSucc = some s := by
  simp [startOfFinN]

theorem readLeafN_sound {x : LambdaSSA.Flat signature.Instr (K + 1 + 1) 3} {b : NLeaf K}
    (h : readLeafN x = some b) : x = .br b.fin (.bv 0) := by
  cases x with
  | br i a =>
    by_cases ha : isBv0 a = true
    · simp [readLeafN, ha] at h
      rw [isBv0_eq ha, ← h, fin_ofFin]
    · simp [readLeafN, ha] at h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h
  | case _ _ _ => cases h

theorem readLeafN_leaf (b : NLeaf K) : readLeafN (.br b.fin (.bv 0)) = some b :=
  congrArg some (ofFin_fin b)

theorem readBlockN_sound {x : LambdaSSA.Flat signature.Instr (K + 1 + 1) 2} {r : Bool × NLeaf K × NLeaf K}
    (h : readBlockN x = some r) :
    x = .case (.op (.ask r.1) (.bv 0)) (.br r.2.1.fin (.bv 0)) (.br r.2.2.fin (.bv 0)) := by
  cases x with
  | case e l r' =>
    cases he : readOp e with
    | none => simp [readBlockN, he] at h
    | some lab =>
      cases hl : readLeafN l with
      | none => simp [readBlockN, he, hl] at h
      | some b₁ =>
        cases hr : readLeafN r' with
        | none => simp [readBlockN, he, hl, hr] at h
        | some b₂ =>
          simp [readBlockN, he, hl, hr] at h
          rw [← h, readOp_sound he, readLeafN_sound hl, readLeafN_sound hr]
  | br _ _ => cases h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h

theorem readBlockN_block (l : Bool) (b₁ b₂ : NLeaf K) :
    readBlockN (.case (.op (.ask l) (.bv 0)) (.br b₁.fin (.bv 0)) (.br b₂.fin (.bv 0))) = some (l, b₁, b₂) := by
  simp [readBlockN, readOp, isBv0, opLabel, readLeafN_leaf]

theorem readEntryN_sound {x : LambdaSSA.Flat signature.Instr (K + 1 + 1) 1} {s : Fin (K + 1)}
    (h : readEntryN x = some s) : x = .br s.castSucc (.bv 0) := by
  cases x with
  | br i a =>
    by_cases ha : isBv0 a = true
    · simp [readEntryN, ha] at h
      rw [isBv0_eq ha, startOfFinN_eq h]
    · simp [readEntryN, ha] at h
  | let₁ _ _ => cases h
  | let₂ _ _ => cases h
  | case _ _ _ => cases h

theorem readEntryN_entry (s : Fin (K + 1)) : readEntryN (.br s.castSucc (.bv 0)) = some s := by
  simp [readEntryN, isBv0, startOfFinN_castSucc]

/-! ## The reader is exact -/

/-- A graph that the reader accepts is the graph of the table it returns. -/
theorem nread_sound {g : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1} {d : NTable K}
    (h : NTable.read g = some d) : g = d.flat := by
  obtain ⟨entry, block⟩ := g
  cases hs : readEntryN entry with
  | none => simp [NTable.read, hs] at h
  | some s =>
    cases ht : tabulate (K + 1) (fun i => readBlockN (block i)) with
    | none => simp [NTable.read, hs, ht] at h
    | some rows =>
      simp [NTable.read, hs, ht] at h
      rw [← h]
      exact congrArg₂ LambdaSSA.FiniteCFG.mk (readEntryN_sound hs)
        (funext fun i => readBlockN_sound (tabulate_sound _ _ _ ht i))

theorem ofRows_rowsN (d : NTable K) :
    NTable.ofRows d.start (fun i => (d.label i, d.branch i false, d.branch i true)) = d := by
  obtain ⟨label, branch, start⟩ := d
  have eb : (fun i tag => match tag with
      | false => branch i false
      | true => branch i true) = branch := by
    funext i tag
    cases tag <;> rfl
  exact congrArg (fun b => (⟨label, b, start⟩ : NTable K)) eb

/-- The reader accepts the graph of every table and returns that table. -/
theorem nread_flat (d : NTable K) : NTable.read d.flat = some d := by
  have e₁ : readEntryN d.flat.entry = some d.start := readEntryN_entry d.start
  have e₂ : (fun i => readBlockN (d.flat.block i)) =
      fun i => some (d.label i, d.branch i false, d.branch i true) :=
    funext fun i => readBlockN_block _ _ _
  unfold NTable.read
  rw [e₁, e₂, tabulate_some]
  exact congrArg some (ofRows_rowsN d)

theorem nread_iff {g : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1} {d : NTable K} :
    NTable.read g = some d ↔ g = d.flat :=
  ⟨nread_sound, fun h => h ▸ nread_flat d⟩

/-! ## Typing of generated graphs -/

theorem append_bit (i : Fin (K + 1 + 1)) :
    SSA.FiniteSum.append (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit) i = Bit := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem jump_typed {n : Nat} {β : BoundCtx (Ty Empty) (n + 1)} (hβ : β.get 0 = Bit) (i : Fin (K + 1 + 1)) :
    LambdaSSA.Flat.HasType (SSA.FiniteSum.append (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit)) β
      (.br i (.bv 0) : LambdaSSA.Flat signature.Instr (K + 1 + 1) (n + 1)) :=
  .br (by
    rw [append_bit, ← hβ]
    exact .bv)

/-- The graph of every table is typed in the flat judgment. -/
theorem nflat_typed (d : NTable K) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit) d.flat where
  entry := jump_typed rfl _
  block := fun _ => .case (A := Bit) (B := Bit) (.op .bv) (jump_typed rfl _) (jump_typed rfl _)

end Reader

/-! ## Sources given as flat syntax, at any two sizes -/

section Accepted

variable {K K' : Nat} {g : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1}
  {g' : LambdaSSA.FiniteCFG signature.Instr (K' + 1) 1 1} {d : NTable K} {d' : NTable K'}

theorem nread_erase (h : NTable.read g = some d) : g.erase = d.source := by
  rw [nread_sound h]
  rfl

theorem nread_typed (h : NTable.read g = some d) : ValueBranches [Bit] g.erase [Bit] :=
  nread_erase h ▸ d.source_typed

theorem nread_flat_typed (h : NTable.read g = some d) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit) g :=
  nread_sound h ▸ nflat_typed d

theorem nread_bitPointed (h : NTable.read g = some d) :
    BitPointed g.erase (fun i => some (d.label i)) d.act (fun _ => d.start) := by
  rw [nread_erase h]
  exact nbitPointed d

theorem nread_entered (h : NTable.read g = some d) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] g.erase
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered d.start)) [Bit] := by
  rw [nread_erase h]
  exact cert_source (ntableCert d)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem nread_complete (h : NTable.read g = some d) (h' : NTable.read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔ Valid (nread_typed h).hasType (nread_typed h').hasType := by
  obtain rfl := nread_sound h
  obtain rfl := nread_sound h'
  exact ncomplete d d'

theorem nread_bisim (h : NTable.read g = some d) (h' : NTable.read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔
      ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → d.label x = d'.label y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧ R d.start d'.start := by
  obtain rfl := nread_sound h
  obtain rfl := nread_sound h'
  exact nbisim d d'

end Accepted

/-! ## The two-block reader inside the reader of the grammar -/

theorem pollLeaf_fin : (b : PollLeaf) → b.toN.fin = b.fin
  | .exit => rfl
  | .goto false => rfl
  | .goto true => rfl

/-- The graph of a two-block table is the graph of its table of the grammar. -/
theorem toN_flat (d : PollTable) : d.toN.flat = d.flat := by
  obtain ⟨label, branch, start⟩ := d
  refine congrArg₂ LambdaSSA.FiniteCFG.mk ?_ (funext fun i => ?_)
  · cases start <;> rfl
  · exact congrArg₂ (fun x y : Fin 3 => (LambdaSSA.Flat.case (.op (.ask (label (pairBit i))) (.bv 0))
      (.br x (.bv 0)) (.br y (.bv 0)) : LambdaSSA.Flat signature.Instr 3 2))
      (pollLeaf_fin _) (pollLeaf_fin _)

/-- A graph accepted by the two-block reader is accepted by the reader of
the grammar, with the corresponding table. -/
theorem poll_read_toN {g : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d : PollTable}
    (h : PollTable.read g = some d) : NTable.read (K := 1) g = some d.toN :=
  nread_iff.2 ((read_sound h).trans (toN_flat d).symm)

/-- And conversely: the two readers accept the same graphs with two blocks. -/
theorem poll_read_iff {g : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d : PollTable} :
    PollTable.read g = some d ↔ NTable.read (K := 1) g = some d.toN :=
  ⟨poll_read_toN, fun h => read_iff.2 ((nread_sound h).trans (toN_flat d))⟩

/-! ## Regression across sizes -/

theorem cycleFlat_eq (l : Bool) : cycleFlat l = (cycleN l).flat :=
  congrArg (LambdaSSA.FiniteCFG.mk _) (funext fun i => by
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl)

theorem nread_cycle (l : Bool) : NTable.read (K := 2) (cycleFlat l) = some (cycleN l) :=
  nread_iff.2 (cycleFlat_eq l)

theorem nread_selfLit (l : Bool) : NTable.read (K := 1) (selfLit l) = some (selfTable l).toN :=
  poll_read_toN (read_selfLit l)

/-- The cycle of three blocks and the two-block literal have equal
sources, as accepted scoped inputs of two sizes. -/
theorem cycle_selfLit (l : Bool) : Eqv false [Bit] (cycleFlat l).erase (selfLit l).erase [Bit] :=
  (nread_bisim (nread_cycle l) (nread_selfLit l)).2
    ⟨fun _ _ => True, fun _ _ _ => rfl, fun _ _ _ tag _ => by
      cases tag
      · exact rfl
      · exact ⟨rfl, trivial⟩, trivial⟩

theorem cycle_selfLit_iff (l l' : Bool) :
    Eqv false [Bit] (cycleFlat l).erase (selfLit l').erase [Bit] ↔ l = l' :=
  ⟨fun e => by
      obtain ⟨R, hl, -, r⟩ := (nread_bisim (nread_cycle l) (nread_selfLit l')).1 e
      exact hl _ _ r,
    fun h => h ▸ cycle_selfLit l⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
