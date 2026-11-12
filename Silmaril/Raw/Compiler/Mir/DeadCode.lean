module

public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! # Dead-code elimination on Mir

`DeadCode.pass` deletes the operations whose result is never read: a `const`, `move`,
`unary`, `slotGet` or `binary` (except division and remainder, which may fault) whose
destination register is dead after it. Loads, stores, slot writes, calls, `addr` and
floating-point instructions are kept.

**Liveness, checked.** The live registers at the start of each block are computed by an
unverified backward fixpoint iteration (`iterate`) and then **checked** (`check`): for
every block, the registers live at its start, computed backward from the union of the
claimed sets of its successors and the registers its terminator reads, must be in its
own claimed set. A function whose certificate fails the check is left unchanged, so the
pass is a validator with fallback. Register sets are bit masks (`Nat`), so the pass is
fast on functions with many registers.

**Simulation.** The output of a block is the subsequence of its kept instructions. An
input point `(l, i)` is related to the output point `(l, i')` at which the output's
remaining instructions are the kept part of the input's remaining ones, with frames that
have the same slots and agree on the registers live at `(l, i)` (`DRel`). A deleted
operation is a stuttering step (`FuncPass.InstrSim`); `DeadCode.correct` proves
`Contract.mirPass` through `FuncPass.mirPass`. -/

@[expose] public section

namespace Silmaril.Compile.Mir.DeadCode

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass

/-! ## Register sets -/

/-- A set of registers, as a bit mask. -/
abbrev RSet := Nat

def RSet.insert (s : RSet) (r : Nat) : RSet := s ||| 2 ^ r

def RSet.erase (s : RSet) (r : Nat) : RSet := if s.testBit r then s ^^^ 2 ^ r else s

def RSet.addAll (s : RSet) (rs : List Nat) : RSet := rs.foldl RSet.insert s

def RSet.eraseAll (s : RSet) (rs : List Nat) : RSet := rs.foldl RSet.erase s

def RSet.subset (a b : RSet) : Bool := a ||| b == b

theorem RSet.mem_insert (s : RSet) (r x : Nat) : (s.insert r).testBit x = (s.testBit x || decide (r = x)) := by
  simp [RSet.insert, Nat.testBit_or, Nat.testBit_two_pow]

theorem RSet.mem_erase (s : RSet) (r x : Nat) : (s.erase r).testBit x = (s.testBit x && decide (x ≠ r)) := by
  unfold RSet.erase
  split
  · rename_i h
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hx : x = r
    · subst hx; simp [h]
    · simp [hx, Ne.symm hx]
  · rename_i h
    by_cases hx : x = r
    · subst hx; simp at h; simp [h]
    · simp [hx]

theorem RSet.mem_addAll (s : RSet) (rs : List Nat) (x : Nat) :
    (s.addAll rs).testBit x = (s.testBit x || decide (x ∈ rs)) := by
  induction rs generalizing s with
  | nil => simp [RSet.addAll]
  | cons r rs ih =>
    simp only [RSet.addAll, List.foldl_cons] at ih ⊢
    rw [ih, RSet.mem_insert]
    by_cases h : x = r <;> simp [h, eq_comm]

theorem RSet.mem_eraseAll (s : RSet) (rs : List Nat) (x : Nat) :
    (s.eraseAll rs).testBit x = (s.testBit x && decide (x ∉ rs)) := by
  induction rs generalizing s with
  | nil => simp [RSet.eraseAll]
  | cons r rs ih =>
    simp only [RSet.eraseAll, List.foldl_cons] at ih ⊢
    rw [ih, RSet.mem_erase]
    by_cases h : x = r <;> simp [h]

theorem RSet.mem_of_subset {a b : RSet} (h : RSet.subset a b = true) {x : Nat} (hx : a.testBit x = true) :
    b.testBit x = true := by
  simp only [RSet.subset, beq_iff_eq] at h
  rw [← h, Nat.testBit_or, hx, Bool.true_or]

/-! ## Liveness -/

/-- The registers an operation reads. -/
def opUses : Lir.Op Nat → List Nat
  | .const _ _ => []
  | .move _ s => [s]
  | .unary _ _ s => [s]
  | .binary _ _ a b => [a, b]
  | .load _ _ _ base _ => [base]
  | .store _ base _ src => [base, src]
  | .slotGet _ _ => []
  | .slotSet _ s => [s]

/-- The register an operation writes. -/
def opDef : Lir.Op Nat → Option Nat
  | .const d _ => some d
  | .move d _ => some d
  | .unary _ d _ => some d
  | .binary _ d _ _ => some d
  | .load _ _ d _ _ => some d
  | .slotGet d _ => some d
  | _ => none

/-- Division and remainder: `Binop.eval` fails on a zero divisor. -/
def faults : Lir.Binop → Bool
  | .divs | .divu | .rems | .remu | .divs32 | .divu32 | .rems32 | .remu32 => true
  | _ => false

/-- The register of an operation that can be deleted when it is dead: one that writes a
register, changes nothing else, and cannot fault. -/
def removable : Lir.Op Nat → Option Nat
  | .const d _ => some d
  | .move d _ => some d
  | .unary _ d _ => some d
  | .binary op d _ _ => if faults op then none else some d
  | .slotGet d _ => some d
  | _ => none

/-- Whether an instruction is dead after `L`. -/
def dead (L : RSet) : Instr → Bool
  | .op o =>
    match removable o with
    | some d => !L.testBit d
    | none => false
  | _ => false

/-- The registers live before a kept instruction, from those live after it. -/
def instrLive (L : RSet) : Instr → RSet
  | .op o =>
    (match opDef o with
      | some d => L.erase d
      | none => L).addAll (opUses o)
  | .fop _ d a b => ((L.erase d).insert a).insert b
  | .addr d _ _ => L.erase d
  | .call _ args res => (L.eraseAll res).addAll args
  | .callIndirect t args res => ((L.eraseAll res).addAll args).insert t

/-- Delete the dead instructions of a list, backward from the registers `L` live after it;
the kept instructions and the registers live before the list. -/
def dceList (L : RSet) : List Instr → List Instr × RSet
  | [] => ([], L)
  | x :: xs =>
    let p := dceList L xs
    if dead p.2 x then p else (x :: p.1, instrLive p.2 x)

/-- The registers a terminator reads. -/
def termUses : Lir.Term Nat → List Nat
  | .branch c _ _ => [c]
  | .ret locs => locs.filterMap fun | .reg r => some r | .slot _ => none
  | _ => []

/-- The registers live after a block, from the claimed sets of its successors. -/
def liveOut (cert : Array RSet) : Lir.Term Nat → RSet
  | .jump l => cert.getD l 0
  | .branch _ l₁ l₂ => cert.getD l₁ 0 ||| cert.getD l₂ 0
  | _ => 0

/-- The registers live before the terminator of a block. -/
def liveEnd (cert : Array RSet) (b : Block) : RSet := (liveOut cert b.term).addAll (termUses b.term)

/-- The kept instructions of a block and the registers live at its start. -/
def blockLive (cert : Array RSet) (b : Block) : List Instr × RSet :=
  dceList (liveEnd cert b) b.instrs.toList

/-- One backward sweep over the blocks, last first. -/
def sweep (f : Func) (cert : Array RSet) : Array RSet :=
  (List.range f.blocks.size).foldr (fun l c =>
    match f.blocks[l]? with
    | some b => c.set! l ((blockLive c b).2 ||| c.getD l 0)
    | none => c) cert

/-- The fixpoint iteration (unverified; `check` validates its result). -/
def iterate (f : Func) : Nat → Array RSet → Array RSet
  | 0, cert => cert
  | fuel + 1, cert =>
    let cert' := sweep f cert
    if cert' == cert then cert else iterate f fuel cert'

/-- The claimed live registers at the start of each block. -/
def certOf (f : Func) : Array RSet := iterate f 64 (Array.replicate f.blocks.size 0)

/-- The certificate covers every block: the registers live at its start, from the claims of
its successors, are claimed. -/
def check (cert : Array RSet) (f : Func) : Bool :=
  (List.range f.blocks.size).all fun l =>
    match f.blocks[l]? with
    | some b => RSet.subset (blockLive cert b).2 (cert.getD l 0)
    | none => true

def dceBlock (cert : Array RSet) (b : Block) : Block := ⟨(blockLive cert b).1.toArray, b.term⟩

/-- The pass on one function: the dead operations deleted when the certificate checks,
otherwise the function unchanged. -/
def dceFunc (f : Func) : Func :=
  let cert := certOf f
  if check cert f then { f with blocks := f.blocks.map (dceBlock cert) } else f

/-- The pass on units. -/
def run : Array Mir.Unit → Array Mir.Unit := mapFuncs dceFunc

/-! ## Correctness -/

theorem check_spec {cert : Array RSet} {f : Func} (h : check cert f = true) {l : Nat} {b : Block}
    (hb : f.blocks[l]? = some b) : RSet.subset (blockLive cert b).2 (cert.getD l 0) = true := by
  simp only [check, List.all_eq_true, List.mem_range] at h
  have := h l (Array.getElem?_eq_some_iff.mp hb).1
  simpa [hb] using this

theorem dceList_refs (L : RSet) (xs : List Instr) :
    (dceList L xs).1.filterMap refKey = xs.filterMap refKey := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [dceList]
    split
    · rename_i h
      rw [ih]
      cases x with
      | op o => simp only [List.filterMap_cons, refKey]
      | _ => simp [dead] at h
    · simp only [List.filterMap_cons, ih]

theorem shape : Shape dceFunc where
  name f := by simp only [dceFunc]; split <;> rfl
  params f := by simp only [dceFunc]; split <;> rfl
  results f := by simp only [dceFunc]; split <;> rfl
  weak f := by simp only [dceFunc]; split <;> rfl
  size f := by simp only [dceFunc]; split <;> simp
  refs f := by
    simp only [dceFunc]; split
    · simp only [funcRefs, Array.toList_map, List.flatMap_map, dceBlock, blockLive,
        List.toList_toArray, dceList_refs]
    · rfl

/-- Frames with the same slots that agree on the registers of `L`. -/
def Agree (L : RSet) (fr fr' : Lir.Frame Nat) : Prop :=
  fr'.slots = fr.slots ∧ ∀ r, L.testBit r = true → fr'.get r = fr.get r

theorem Agree.mono {L L' : RSet} {fr fr' : Lir.Frame Nat} (h : Agree L fr fr')
    (hs : ∀ r, L'.testBit r = true → L.testBit r = true) : Agree L' fr fr' :=
  ⟨h.1, fun r hr => h.2 r (hs r hr)⟩

theorem Agree.set {L : RSet} {fr fr' : Lir.Frame Nat} {d : Nat} (h : Agree (L.erase d) fr fr')
    (w : Lir.Word) : Agree L (fr.set d w) (fr'.set d w) := by
  refine ⟨h.1, fun r hr => ?_⟩
  by_cases hrd : r = d
  · simp [hrd]
  · simp only [Lir.Frame.get_set, hrd, ite_false]
    exact h.2 r (by rw [RSet.mem_erase]; simp [hr, hrd])

theorem Agree.get {L : RSet} {fr fr' : Lir.Frame Nat} {rs : List Nat} (h : Agree (L.addAll rs) fr fr')
    {r : Nat} (hr : r ∈ rs) : fr'.get r = fr.get r :=
  h.2 r (by rw [RSet.mem_addAll]; simp [hr])

theorem Agree.base {L : RSet} {fr fr' : Lir.Frame Nat} {rs : List Nat} (h : Agree (L.addAll rs) fr fr') :
    Agree L fr fr' :=
  h.mono fun r hr => by rw [RSet.mem_addAll, hr, Bool.true_or]

theorem readAll_agree {fr fr' : Lir.Frame Nat} (hs : fr'.slots = fr.slots) {locs : List (Lir.Loc Nat)}
    (h : ∀ r, Lir.Loc.reg r ∈ locs → fr'.get r = fr.get r) : fr'.readAll locs = fr.readAll locs := by
  induction locs with
  | nil => rfl
  | cons l ls ih =>
    simp only [Lir.Frame.readAll, List.mapM_cons] at ih ⊢
    rw [ih fun r hr => h r (List.mem_cons_of_mem _ hr)]
    cases l with
    | reg r => simp only [Lir.Frame.read]; rw [show fr'.regs r = fr.regs r from h r (by simp)]
    | slot n => simp only [Lir.Frame.read, hs]

theorem readAll_regs_agree {fr fr' : Lir.Frame Nat} {L : RSet} {rs : List Nat}
    (h : Agree (L.addAll rs) fr fr') : fr'.readAll (rs.map .reg) = fr.readAll (rs.map .reg) :=
  readAll_agree h.1 fun r hr => h.get (by simpa using hr)

theorem writeAll_agree {fr fr' fr₁ fr₁' : Lir.Frame Nat} {rs : List Nat} {vals : List Lir.Word}
    (hw : fr.writeAll (rs.map .reg) vals = some fr₁) (hw' : fr'.writeAll (rs.map .reg) vals = some fr₁')
    (r : Nat) : fr₁'.regs r = fr₁.regs r ∨ (r ∉ rs ∧ fr₁'.regs r = fr'.regs r ∧ fr₁.regs r = fr.regs r) := by
  induction rs generalizing fr fr' vals with
  | nil =>
    cases vals <;> simp [Lir.Frame.writeAll] at hw hw'
    subst hw hw'; exact .inr ⟨by simp, rfl, rfl⟩
  | cons x xs ih =>
    cases vals with
    | nil => simp [Lir.Frame.writeAll] at hw
    | cons v vs =>
      simp only [List.map_cons, Lir.Frame.writeAll, Lir.Frame.write] at hw hw'
      rcases ih hw hw' with h | ⟨hr, h₁, h₂⟩
      · exact .inl h
      · by_cases hrx : r = x
        · left; rw [h₁, h₂]; simp [hrx]
        · right; refine ⟨by simp [hrx, hr], ?_, ?_⟩ <;> simp [h₁, h₂, hrx]

theorem writeAll_slots {fr fr₁ : Lir.Frame Nat} {rs : List Nat} {vals : List Lir.Word}
    (hw : fr.writeAll (rs.map .reg) vals = some fr₁) : fr₁.slots = fr.slots := by
  induction rs generalizing fr vals with
  | nil => cases vals <;> simp [Lir.Frame.writeAll] at hw; subst hw; rfl
  | cons x xs ih =>
    cases vals with
    | nil => simp [Lir.Frame.writeAll] at hw
    | cons v vs =>
      simp only [List.map_cons, Lir.Frame.writeAll, Lir.Frame.write] at hw
      rw [ih hw]; rfl

theorem Agree.writeAll {L : RSet} {fr fr' fr₁ fr₁' : Lir.Frame Nat} {rs : List Nat} {vals : List Lir.Word}
    (h : Agree (L.eraseAll rs) fr fr') (hw : fr.writeAll (rs.map .reg) vals = some fr₁)
    (hw' : fr'.writeAll (rs.map .reg) vals = some fr₁') : Agree L fr₁ fr₁' := by
  refine ⟨by rw [writeAll_slots hw, writeAll_slots hw', h.1], fun r hr => ?_⟩
  rcases writeAll_agree hw hw' r with e | ⟨hn, e₁, e₂⟩
  · exact e
  · show fr₁'.regs r = fr₁.regs r
    rw [e₁, e₂]
    exact h.2 r (by rw [RSet.mem_eraseAll]; simp [hr, hn])

/-- A kept operation runs the same from agreeing frames. -/
theorem op_agree {L : RSet} {fr fr' : Lir.Frame Nat} {o : Lir.Op Nat}
    (h : Agree (instrLive L (.op o)) fr fr') {m : Lir.Memory} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory}
    (he : o.exec fr m = some (fr₁, m₁)) : ∃ fr₁', o.exec fr' m = some (fr₁', m₁) ∧ Agree L fr₁ fr₁' := by
  simp only [instrLive] at h
  have hb := h.base
  cases o with
  | const d w =>
    simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, rfl, hb.set w⟩
  | move d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.get (r := s) (by simp [opUses]), hv], hb.set v⟩
  | unary op d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.get (r := s) (by simp [opUses]), hv], hb.set _⟩
  | binary op d a c =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.get (r := a) (by simp [opUses]), h.get (r := c) (by simp [opUses]),
      hx, hy, hz], hb.set z⟩
  | load w e d base off =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, z, hz, rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.get (r := base) (by simp [opUses]), ha, hz], hb.set z⟩
  | store w base off src =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, x, hx, m', hm', rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.get (r := base) (by simp [opUses]),
      h.get (r := src) (by simp [opUses]), ha, hx, hm'], hb⟩
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨_, by simp [Lir.Op.exec, h.1, hv], hb.set v⟩
  | slotSet n s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    refine ⟨fr'.setSlot n v, by simp [Lir.Op.exec, h.get (r := s) (by simp [opUses]), hv], ?_⟩
    refine ⟨?_, fun r hr => hb.2 r hr⟩
    funext k
    simp only [Lir.Frame.slots_setSlot, hb.1]

/-- A deleted operation changes only its dead register. -/
theorem dead_exec {L : RSet} {o : Lir.Op Nat} (hd : dead L (.op o) = true) {fr fr' : Lir.Frame Nat}
    (h : Agree L fr fr') {m : Lir.Memory} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory}
    (he : o.exec fr m = some (fr₁, m₁)) : m₁ = m ∧ Agree L fr₁ fr' := by
  simp only [dead] at hd
  split at hd
  · rename_i d hrem
    simp only [Bool.not_eq_true'] at hd
    have key : ∀ w, Agree L (fr.set d w) fr' := fun w => by
      refine ⟨h.1, fun r hr => ?_⟩
      have : r ≠ d := by rintro rfl; rw [hd] at hr; cases hr
      simp [this, h.2 r hr]
    cases o with
    | const d' w =>
      simp only [removable, Option.some.injEq] at hrem; subst hrem
      simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, key _⟩
    | move d' s =>
      simp only [removable, Option.some.injEq] at hrem; subst hrem
      simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨v, -, rfl, rfl⟩ := he; exact ⟨rfl, key _⟩
    | unary op d' s =>
      simp only [removable, Option.some.injEq] at hrem; subst hrem
      simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨v, -, rfl, rfl⟩ := he; exact ⟨rfl, key _⟩
    | binary op d' a c =>
      simp only [removable] at hrem
      split at hrem
      · cases hrem
      · simp only [Option.some.injEq] at hrem; subst hrem
        simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
        obtain ⟨_, _, _, _, z, _, rfl, rfl⟩ := he; exact ⟨rfl, key _⟩
    | slotGet d' n =>
      simp only [removable, Option.some.injEq] at hrem; subst hrem
      simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨v, -, rfl, rfl⟩ := he; exact ⟨rfl, key _⟩
    | load => simp [removable] at hrem
    | store => simp [removable] at hrem
    | slotSet => simp [removable] at hrem
  · cases hd

/-- The relation on a checked function: the output's remaining instructions are the kept
part of the input's, and the frames agree on the live registers. -/
def DRel (cert : Array RSet) (f : Func) (l i : Nat) (fr : Lir.Frame Nat) (i' : Nat) (fr' : Lir.Frame Nat) :
    Prop :=
  match f.blocks[l]? with
  | some b =>
    let p := dceList (liveEnd cert b) (b.instrs.toList.drop i)
    i' ≤ (blockLive cert b).1.length ∧ (blockLive cert b).1.drop i' = p.1 ∧ Agree p.2 fr fr'
  | none => fr'.slots = fr.slots

/-- The point relation: `DRel` when the certificate checks, otherwise the identity. -/
def PR : PointRel := fun f =>
  if check (certOf f) f then DRel (certOf f) f else idRel

theorem dceFunc_block {cert : Array RSet} {f : Func} {l : Nat} {b b' : Block} (hb : f.blocks[l]? = some b)
    (hb' : ({ f with blocks := f.blocks.map (dceBlock cert) } : Func).blocks[l]? = some b') :
    b' = dceBlock cert b := by
  simp only [Array.getElem?_map, hb, Option.map_some, Option.some.injEq] at hb'
  exact hb'.symm

theorem agree_entry {cert : Array RSet} {f : Func} (hc : check cert f = true) {l : Nat}
    {fr fr' : Lir.Frame Nat} (h : Agree (cert.getD l 0) fr fr') : DRel cert f l 0 fr 0 fr' := by
  unfold DRel
  split
  · rename_i b hb
    refine ⟨Nat.zero_le _, by simp [blockLive], h.mono fun r hr => RSet.mem_of_subset (check_spec hc hb) ?_⟩
    simpa [blockLive] using hr
  · exact h.1

theorem dfsim (f : Func) (hc : check (certOf f) f = true) :
    FSim f { f with blocks := f.blocks.map (dceBlock (certOf f)) } (DRel (certOf f) f) where
  entry fr := by
    unfold DRel
    split
    · exact ⟨Nat.zero_le _, by simp [blockLive], ⟨rfl, fun _ _ => rfl⟩⟩
    · rfl
  instr l b b' i fr i' fr' x hb hb' hp hx := by
    obtain rfl := dceFunc_block hb hb'
    simp only [DRel, hb] at hp
    obtain ⟨hle, hdrop, hag⟩ := hp
    have hxs : b.instrs.toList.drop i = x :: b.instrs.toList.drop (i + 1) := by
      have hx' : b.instrs.toList[i]? = some x := by simpa using hx
      obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hx'
      rw [List.drop_eq_getElem_cons hi, hget]
    have hnext : ∀ i₂ fr₂ fr₂', i₂ ≤ (blockLive (certOf f) b).1.length →
        (blockLive (certOf f) b).1.drop i₂ = (dceList (liveEnd (certOf f) b) (b.instrs.toList.drop (i + 1))).1 →
        Agree (dceList (liveEnd (certOf f) b) (b.instrs.toList.drop (i + 1))).2 fr₂ fr₂' →
        DRel (certOf f) f l (i + 1) fr₂ i₂ fr₂' := fun i₂ fr₂ fr₂' h₁ h₂ h₃ => by
      simp only [DRel, hb]; exact ⟨h₁, h₂, h₃⟩
    rw [hxs] at hdrop hag
    simp only [dceList] at hdrop hag
    split at hdrop
    · -- deleted
      rename_i hd
      simp only [hd, ↓reduceIte] at hag
      cases x with
      | op o =>
        intro m fr₁ m₁ he
        obtain ⟨rfl, hag'⟩ := dead_exec hd hag he
        exact .inl ⟨rfl, hnext i' fr₁ fr' hle hdrop hag'⟩
      | _ => simp [dead] at hd
    · -- kept
      rename_i hd
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hag
      have hlt : i' < (blockLive (certOf f) b).1.length := by
        by_contra hge
        rw [List.drop_eq_nil_of_le (by omega)] at hdrop
        cases hdrop
      have hy : (dceBlock (certOf f) b).instrs[i']? = some x := by
        have h0 := congrArg (·[0]?) hdrop
        simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
        simpa [dceBlock] using h0
      have hdrop' : (blockLive (certOf f) b).1.drop (i' + 1) =
          (dceList (liveEnd (certOf f) b) (b.instrs.toList.drop (i + 1))).1 := by
        rw [← List.tail_drop, hdrop]; rfl
      rw [hy]
      cases x with
      | op o =>
        intro m fr₁ m₁ he
        obtain ⟨fr₁', he', hag'⟩ := op_agree hag he
        exact .inr ⟨o, rfl, fr₁', he', hnext _ _ _ hlt hdrop' hag'⟩
      | fop op d a c =>
        intro fr₁ he
        simp only [instrLive] at hag
        refine ⟨op, d, a, c, rfl, ?_⟩
        simp only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
        obtain ⟨x, hx, y, hy, rfl⟩ := he
        have hc : fr'.get c = fr.get c := hag.2 c (by simp [RSet.mem_insert])
        have ha : fr'.get a = fr.get a := hag.2 a (by simp [RSet.mem_insert])
        refine ⟨fr'.set d (op.eval x y), by simp [Lir.FOp.exec, ha, hc, hx, hy], hnext _ _ _ hlt hdrop' ?_⟩
        refine Agree.set (hag.mono fun r hr => ?_) _
        simp [RSet.mem_insert, hr]
      | addr d s off =>
        simp only [instrLive] at hag
        exact ⟨rfl, fun w => hnext _ _ _ hlt hdrop' (hag.set w)⟩
      | call c args res =>
        simp only [instrLive] at hag
        intro vals hv
        refine ⟨args, rfl, by rw [readAll_regs_agree hag, hv], fun vals' fr₁ fr₁' hw hw' =>
          hnext _ _ _ hlt hdrop' (hag.base.writeAll hw hw')⟩
      | callIndirect t args res =>
        simp only [instrLive] at hag
        intro v vals ht hv
        have ht' : fr'.get t = fr.get t := hag.2 t (by simp [RSet.mem_insert])
        have hag₂ : Agree ((((dceList (liveEnd (certOf f) b) (b.instrs.toList.drop (i + 1))).2).eraseAll
            res).addAll args) fr fr' :=
          hag.mono fun r hr => by simp [RSet.mem_insert, hr]
        refine ⟨t, args, rfl, by rw [ht', ht], by rw [readAll_regs_agree hag₂, hv],
          fun vals' fr₁ fr₁' hw hw' => hnext _ _ _ hlt hdrop' (hag₂.base.writeAll hw hw')⟩
  term l b b' i fr i' fr' hb hb' hp hi := by
    obtain rfl := dceFunc_block hb hb'
    simp only [DRel, hb] at hp
    obtain ⟨hle, hdrop, hag⟩ := hp
    rw [hi, List.drop_eq_nil_of_le (as := b.instrs.toList) (by simp)] at hdrop hag
    simp only [dceList] at hdrop hag
    have hi' : i' = (dceBlock (certOf f) b).instrs.size := by
      have := List.drop_eq_nil_iff.mp hdrop
      simp only [dceBlock, List.size_toArray]; omega
    refine ⟨hi', fun hns => ?_⟩
    simp only [dceBlock]
    have huse : ∀ r ∈ termUses b.term, fr'.get r = fr.get r := fun r hr => hag.get hr
    have hout : termOut fr' b.term = termOut fr b.term := by
      cases ht : b.term with
      | jump l => rfl
      | trap => rfl
      | branch c l₁ l₂ =>
        simp only [termOut]; rw [huse c (by simp [ht, termUses])]
      | ret locs =>
        simp only [termOut]
        rw [readAll_agree hag.1 fun r hr => huse r (by simp [ht, termUses]; exact ⟨_, hr, rfl⟩)]
    refine ⟨hout, fun l' hl' => agree_entry hc (hag.base.mono fun r hr => ?_)⟩
    cases ht : b.term with
    | jump l => simp [ht, termOut] at hl'; subst hl'; simpa [liveOut, ht] using hr
    | trap => simp [ht, termOut] at hl'
    | ret locs => simp only [ht, termOut] at hl'; split at hl' <;> cases hl'
    | branch c l₁ l₂ =>
      simp only [ht, termOut] at hl'
      split at hl'
      · simp only [TermOut.goto.injEq] at hl'
        simp only [liveOut, Nat.testBit_or, Bool.or_eq_true]
        split at hl' <;> subst hl'
        · exact .inr hr
        · exact .inl hr
      · cases hl'

theorem sim : Sim dceFunc PR := fun f => by
  by_cases hc : check (certOf f) f = true
  · have e₁ : dceFunc f = { f with blocks := f.blocks.map (dceBlock (certOf f)) } := by
      simp [dceFunc, hc]
    have e₂ : PR f = DRel (certOf f) f := by simp [PR, hc]
    rw [e₁, e₂]; exact dfsim f hc
  · have e₁ : dceFunc f = f := by simp [dceFunc, hc]
    have e₂ : PR f = idRel := by simp [PR, hc]
    rw [e₁, e₂]; exact FSim.id f

/-- **Dead-code elimination refines its input** (`Contract.mirPass`). -/
theorem correct : Contract.mirPass run := FuncPass.mirPass shape sim

end Silmaril.Compile.Mir.DeadCode
