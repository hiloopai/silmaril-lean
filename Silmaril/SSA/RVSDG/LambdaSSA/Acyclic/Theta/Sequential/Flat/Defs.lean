module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Defs

/-! # Link two flat LambdaSSA fragments at a typed payload interface -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LambdaSSA (Region)
open LinearChain (Site localSite externalSite)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M E D X P Q : τ} {L R : List τ}

/-- A local block reads its own payload. Case arms receive only the selected
payload as their current value. A classifier can also route a separately bound
value while reading the original input. -/
inductive Block (Φ : Type u) [HasTy Φ τ] (L : List τ) : τ → Type u where
  | jump {A : τ} : Site L A → Block Φ L A
  | call {A B : τ} : TwoBlock.Instruction Φ A B → Site L B → Block Φ L A
  | split {A B : τ} : Block Φ L A → Block Φ L B → Block Φ L (Silmaril.coprod A B)
  | choose {A B C : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod B C) →
      Block Φ L B → Block Φ L C → Block Φ L A
  | bindChoose {A V B C : τ} : TwoBlock.Instruction Φ A V →
      TwoBlock.Instruction Φ A (Silmaril.coprod B C) → Site L V → Site L V → Block Φ L A

def Block.ofAcyclic : Acyclic.Block Φ L A → Block Φ L A
  | .jump op site => .call op site
  | .branch op left right => .choose op (.jump left) (.jump right)

def Block.rename (f : ∀ {X}, Site L X → Site R X) : {A : τ} → Block Φ L A → Block Φ R A
  | _, .jump site => .jump (f site)
  | _, .call op site => .call op (f site)
  | _, .split left right => .split (left.rename f) (right.rename f)
  | _, .choose op left right => .choose op (left.rename f) (right.rename f)
  | _, .bindChoose value test l r => .bindChoose value test (f l) (f r)

def Block.region : {A : τ} → Block Φ L A → Region Φ
  | _, .jump site => .br site.index (.var 0)
  | _, .call op site => .br site.index (.op op.op (.var 0))
  | _, .split left right => .case (.var 0) left.region right.region
  | _, .choose op left right => .case (.op op.op (.var 0)) left.region right.region
  | _, .bindChoose value test l r =>
    .let₁ (.op value.op (.var 0))
      (.case (.op test.op (.var 1)) (.br l.index (.var 1)) (.br r.index (.var 1)))

theorem Block.typing : {A : τ} → (block : Block Φ L A) → (Γ : List τ) →
    Region.HasType (A :: Γ) block.region L
  | _, .jump site, _ => .br site.typing (.var rfl)
  | _, .call op site, Γ => .br site.typing (op.typing Γ)
  | _, .split left right, Γ => .case (.var rfl) (left.typing (_ :: Γ)) (right.typing (_ :: Γ))
  | _, .choose op left right, Γ => .case (op.typing Γ) (left.typing (_ :: Γ)) (right.typing (_ :: Γ))
  | _, .bindChoose value test l r, Γ =>
    .let₁ (value.typing Γ)
      (.case (test.typingAt rfl) (.br l.typing (.var rfl)) (.br r.typing (.var rfl)))

/-- The block table may contain cycles. Each block is typed independently of
the entry environment. Locals and external labels occupy disjoint ranges. -/
structure Fragment (Φ : Type u) [HasTy Φ τ] (A E D : τ) where
  extra : Nat
  localTypes : Fin (extra + 1) → τ
  entry : Block Φ (List.ofFn localTypes ++ [E,D]) A
  blocks : ∀ i, Block Φ (List.ofFn localTypes ++ [E,D]) (localTypes i)

abbrev Fragment.count (p : Fragment Φ A E D) := p.extra + 1

abbrev Fragment.Labels (p : Fragment Φ A E D) := List.ofFn p.localTypes ++ [E,D]

def Fragment.region (p : Fragment Φ A E D) : Region Φ :=
  .cfg p.entry.region p.count (fun i => (p.blocks i).region)

theorem Fragment.typing (p : Fragment Φ A E D) :
    Region.HasType [A] p.region [E,D] :=
  .cfg p.localTypes (p.entry.typing []) (fun i => (p.blocks i).typing [A])

/-- Dispatch on the typed result of one instruction. The block table is
unreachable because the entry branches directly to an external label. -/
def Fragment.classify (op : TwoBlock.Instruction Φ A (Silmaril.coprod E D)) :
    Fragment Φ A E D where
  extra := 0
  localTypes := fun _ => A
  entry := .choose op (.jump (externalSite _ _ 0)) (.jump (externalSite _ _ 1))
  blocks i := .jump (localSite _ _ i)

def Fragment.feedbackTypes (p : Fragment Φ A E A) : Fin (p.count + 1) → τ :=
  Fin.cons A p.localTypes

def Fragment.feedbackSite (p : Fragment Φ A E A) (site : Site p.Labels X) :
    Site (List.ofFn p.feedbackTypes ++ [E,D]) X :=
  redirect (R := p.localTypes) (L := [E,A]) (fun i => localSite p.feedbackTypes [E,D] i.succ)
    (Fin.cases (motive := fun i => Site _ ([E,A].get i))
      (externalSite p.feedbackTypes [E,D] 0)
      (Fin.cases (localSite p.feedbackTypes [E,D] 0) (fun i => i.elim0))) site

/-- Add an outer header while preserving the body's local blocks. The body's
first exit returns; its second exit re-enters the header with its payload.
The second external label of the resulting fragment is unreachable. -/
def Fragment.feedback (p : Fragment Φ A E A) : Fragment Φ A E D where
  extra := p.count
  localTypes := p.feedbackTypes
  entry := .jump (localSite p.feedbackTypes [E,D] 0)
  blocks := Fin.cases (p.entry.rename p.feedbackSite) (fun i => (p.blocks i).rename p.feedbackSite)

/-- A single-header loop with an independently bound payload. The classifier's
left arm returns the binding and its right arm feeds it back. -/
def Fragment.bindChooseLoop {B C : τ} (value : TwoBlock.Instruction Φ A A)
    (test : TwoBlock.Instruction Φ A (Silmaril.coprod B C)) : Fragment Φ A A D where
  extra := 0
  localTypes := fun _ => A
  entry := .jump (localSite _ _ 0)
  blocks _ := .bindChoose value test (externalSite _ _ 0) (localSite _ _ 0)

/-- On an already selected sum, run the left fragment or return the right
payload immediately at the first external label. -/
def Fragment.splitReturn (p : Fragment Φ A E D) : Fragment Φ (Silmaril.coprod A E) E D :=
  { p with entry := .split p.entry (.jump (externalSite p.localTypes [E,D] 0)) }

/-- A bridge can enter the fragment or supply a completed exit. In the
completed case the fragment's entry and local blocks are skipped. -/
def Fragment.gateCarrier (p : Fragment Φ M E D)
    (gate : TwoBlock.Instruction Φ A (TwoBlock.TwoExit.Carrier M E D)) : Fragment Φ A E D where
  extra := p.extra
  localTypes := p.localTypes
  entry := .choose gate
    (.split (.jump (externalSite p.localTypes [E,D] 0)) (.jump (externalSite p.localTypes [E,D] 1)))
    p.entry
  blocks := p.blocks

def Fragment.loop {B K : τ} (s : Loop Φ A B K E D) : Fragment Φ A E D where
  extra := bodyCount s + 1
  localTypes := Theta.localTypes s
  entry := .jump (localSite _ _ 0)
  blocks i := .ofAcyclic (Theta.blockAt s i)

/-- Use the admitted conditional loop without changing its actual entry or
its existing loop block table. -/
def Fragment.guarded {I B K : τ} (s : Conditional.Guarded Φ A I B K E D) : Fragment Φ A E D where
  extra := bodyCount s.loop + 1
  localTypes := Theta.localTypes s.loop
  entry := .choose s.gate
    (.split (.jump (Conditional.firstExit s)) (.jump (Conditional.secondExit s)))
    (.jump (Conditional.enterLoop s))
  blocks i := .ofAcyclic (Theta.blockAt s.loop i)

theorem Block.ofAcyclic_region (block : Acyclic.Block Φ L A) : (ofAcyclic block).region = block.region := by
  cases block <;> rfl

theorem Fragment.loop_region {B K : τ} (s : Loop Φ A B K E D) :
    (Fragment.loop s).region = Theta.region s :=
  congrArg (fun blocks => Region.cfg (.br 0 (.var 0)) (bodyCount s + 2) blocks)
    (funext fun i => Block.ofAcyclic_region (Theta.blockAt s i))

theorem Fragment.guarded_region {I B K : τ} (s : Conditional.Guarded Φ A I B K E D) :
    (Fragment.guarded s).region = Conditional.region s :=
  congrArg (fun blocks => Region.cfg (Conditional.entry s) (bodyCount s.loop + 2) blocks)
    (funext fun i => Block.ofAcyclic_region (Theta.blockAt s.loop i))

/-- A producer exit can enter the consumer or return to either external
label. The chosen destination determines the payload type. -/
inductive ExitTarget (M E D : τ) : τ → Type u where
  | consumer : ExitTarget M E D M
  | first : ExitTarget M E D E
  | second : ExitTarget M E D D

structure ExitRouting (P Q M E D : τ) where
  first : ExitTarget M E D P
  second : ExitTarget M E D Q

def ExitRouting.target (routing : ExitRouting P Q M E D) :
    (i : Fin [P,Q].length) → ExitTarget M E D ([P,Q].get i) :=
  Fin.cases (motive := fun i => ExitTarget M E D ([P,Q].get i)) routing.first
    (Fin.cases routing.second (fun i => i.elim0))

variable (p : Fragment Φ A P Q) (q : Fragment Φ M E D)

/-- Keep all original block positions within each phase and allocate a fresh
block for the consumer entry. -/
def rightTypes : Fin (q.count + 1) → τ := Fin.cons M q.localTypes

def linkedTypes : Fin (p.count + (q.count + 1)) → τ :=
  Fin.addCases p.localTypes (rightTypes q)

abbrev LinkedLabels := List.ofFn (linkedTypes p q) ++ [E,D]

@[simp] theorem left_type (i : Fin p.count) :
    linkedTypes p q (i.castAdd (q.count + 1)) = p.localTypes i :=
  Fin.addCases_left i

@[simp] theorem right_type (i : Fin (q.count + 1)) :
    linkedTypes p q (i.natAdd p.count) = rightTypes q i :=
  Fin.addCases_right i

def leftLocal (i : Fin p.count) : Site (LinkedLabels p q) (p.localTypes i) :=
  left_type p q i ▸ localSite (linkedTypes p q) [E,D] (i.castAdd (q.count + 1))

def rightLocal (i : Fin (q.count + 1)) : Site (LinkedLabels p q) (rightTypes q i) :=
  right_type p q i ▸ localSite (linkedTypes p q) [E,D] (i.natAdd p.count)

def handoff : Site (LinkedLabels p q) M := rightLocal p q 0

def targetSite : {X : τ} → ExitTarget M E D X → Site (LinkedLabels p q) X
  | _, .consumer => handoff p q
  | _, .first => externalSite (linkedTypes p q) [E,D] 0
  | _, .second => externalSite (linkedTypes p q) [E,D] 1

def leftSiteBy (routing : ExitRouting P Q M E D)
    (site : Site p.Labels X) : Site (LinkedLabels p q) X :=
  redirect (L := [P,Q]) (leftLocal p q) (fun i => targetSite p q (routing.target i)) site

def rightSite (site : Site q.Labels X) : Site (LinkedLabels p q) X :=
  redirect (R := q.localTypes) (fun i => rightLocal p q i.succ) (externalSite (linkedTypes p q) [E,D]) site

def rightBlock (i : Fin (q.count + 1)) : Block Φ (LinkedLabels p q) (rightTypes q i) :=
  Fin.cases (motive := fun j => Block Φ (LinkedLabels p q) (rightTypes q j))
    (q.entry.rename (rightSite p q)) (fun j => (q.blocks j).rename (rightSite p q)) i

/-- Relocate both block tables into a single flat CFG. Each producer exit
routes according to its own typed destination. -/
def linkBy (routing : ExitRouting P Q M E D) : Fragment Φ A E D where
  extra := p.count + q.count
  localTypes := linkedTypes p q
  entry := p.entry.rename (leftSiteBy p q routing)
  blocks i := Fin.addCases (motive := fun j => Block Φ (LinkedLabels p q) (linkedTypes p q j))
    (fun j => (left_type p q j).symm ▸ (p.blocks j).rename (leftSiteBy p q routing))
    (fun j => (right_type p q j).symm ▸ rightBlock p q j) i

/-- The ordinary serial link sends both same-sort producer exits to the
consumer entry. -/
def link (p : Fragment Φ A M M) (q : Fragment Φ M E D) : Fragment Φ A E D :=
  linkBy p q ⟨.consumer, .consumer⟩

def leftSite (p : Fragment Φ A M M) (q : Fragment Φ M E D)
    (site : Site p.Labels X) : Site (LinkedLabels p q) X :=
  leftSiteBy p q ⟨.consumer, .consumer⟩ site

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
