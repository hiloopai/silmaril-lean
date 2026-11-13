module

public import Silmaril.Machine.CBackend.Lir.Simulation.Defs

/-!
# Spilling: from virtual to physical registers

The input is a Lir program over any register type `V` (typically `Nat`, an
unbounded supply of virtual registers). An `Allocation V P` gives every virtual
register a *home*: a physical register of type `P` or a spill slot. It also
names two distinct *scratch* registers, which are never homes.

`spill` rewrites the program:

* a spilled operand is loaded into a scratch register (`slotGet`) before the
  operation, the first operand into `scratch₀`, the second into `scratch₁`;
* a spilled destination is computed into `scratch₀` and stored (`slotSet`)
  afterwards;
* a floating-point instruction (`fop`) is treated like a binary operation;
* a spilled branch condition is loaded into `scratch₀` at the end of the block;
* call arguments, call results, parameters and returned values are Lir
  locations already, so they are renamed without extra code.

Source stack slot `n` becomes target slot `2n` and spill slot `m` becomes
target slot `2m + 1`, so the two never collide and no condition on the source
program's slot usage is needed.

`Allocation.Valid` is the complete list of conditions: the scratch registers
are distinct, no home is a scratch register, and `home` is injective. Under
these conditions `spill_behaves` shows that every non-stuck behaviour of the
source (returned values and memory, trap and memory, divergence) is a behaviour
of the spilled program. No liveness analysis is performed, so the number of
spill slots equals the number of spilled virtual registers.

`firstK k` is a simple valid allocation: virtual registers `0 … k - 1` live in
physical registers `2 … k + 1` of `Fin (k + 2)`, the rest are spilled, and
physical registers `0` and `1` are the scratch registers.
-/

@[expose] public section

namespace Silmaril.Machine.Lir.Alloc

open Relation

/-- Where a virtual register lives. -/
inductive Home (P : Type) where
  | reg (p : P)
  | spill (slot : Nat)
  deriving DecidableEq, Repr

structure Allocation (V P : Type) where
  home : V → Home P
  scratch₀ : P
  scratch₁ : P

structure Allocation.Valid {V P : Type} (a : Allocation V P) : Prop where
  scratch_ne : a.scratch₀ ≠ a.scratch₁
  home_ne₀ : ∀ v, a.home v ≠ .reg a.scratch₀
  home_ne₁ : ∀ v, a.home v ≠ .reg a.scratch₁
  injective : Function.Injective a.home

variable {V P : Type}

def Home.loc : Home P → Loc P
  | .reg p => .reg p
  | .spill m => .slot (2 * m + 1)

namespace Allocation

variable (a : Allocation V P)

/-- The target location of a source location. -/
def loc : Loc V → Loc P
  | .reg v => (a.home v).loc
  | .slot n => .slot (2 * n)

/-- Code placing operand `v` in a register, using `sc` if it is spilled, and
that register. -/
def use (v : V) (sc : P) : List (Op P) × P :=
  match a.home v with
  | .reg p => ([], p)
  | .spill m => ([.slotGet sc (2 * m + 1)], sc)

/-- The register computing destination `v`, and the code storing it to its
home afterwards. -/
def dest (v : V) : P × List (Op P) :=
  match a.home v with
  | .reg p => (p, [])
  | .spill m => (a.scratch₀, [.slotSet (2 * m + 1) a.scratch₀])

def trOp : Op V → List (Op P)
  | .const d v => .const (a.dest d).1 v :: (a.dest d).2
  | .move d s => (a.use s a.scratch₀).1 ++ .move (a.dest d).1 (a.use s a.scratch₀).2 :: (a.dest d).2
  | .unary op d s =>
    (a.use s a.scratch₀).1 ++ .unary op (a.dest d).1 (a.use s a.scratch₀).2 :: (a.dest d).2
  | .binary op d x y =>
    (a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1 ++
      .binary op (a.dest d).1 (a.use x a.scratch₀).2 (a.use y a.scratch₁).2 :: (a.dest d).2
  | .load w e d b off =>
    (a.use b a.scratch₀).1 ++ .load w e (a.dest d).1 (a.use b a.scratch₀).2 off :: (a.dest d).2
  | .store w b off src =>
    (a.use b a.scratch₀).1 ++ (a.use src a.scratch₁).1 ++
      [.store w (a.use b a.scratch₀).2 off (a.use src a.scratch₁).2]
  | .slotGet d n => .slotGet (a.dest d).1 (2 * n) :: (a.dest d).2
  | .slotSet n s => (a.use s a.scratch₀).1 ++ [.slotSet (2 * n) (a.use s a.scratch₀).2]

def trInstr : Instr V → List (Instr P)
  | .op o => (a.trOp o).map .op
  | .call f args results => [.call f (args.map a.loc) (results.map a.loc)]
  | .fop op d x y =>
    ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1).map .op ++
      .fop op (a.dest d).1 (a.use x a.scratch₀).2 (a.use y a.scratch₁).2 :: (a.dest d).2.map .op

/-- Code placed before the terminator, and the terminator. -/
def trTerm : Term V → List (Op P) × Term P
  | .jump l => ([], .jump l)
  | .branch c l₁ l₂ => ((a.use c a.scratch₀).1, .branch (a.use c a.scratch₀).2 l₁ l₂)
  | .ret locs => ([], .ret (locs.map a.loc))
  | .trap => ([], .trap)

def trBlock (b : Block V) : Block P where
  instrs := (b.instrs.map a.trInstr).flatten ++ (a.trTerm b.term).1.map .op
  term := (a.trTerm b.term).2

def trFunc (fn : Func V) : Func P where
  params := fn.params.map a.loc
  entry := fn.entry
  blocks := fn.blocks.map a.trBlock

end Allocation

/-- The spilled program. -/
def spill (a : Allocation V P) (p : Prog V) : Prog P := ⟨p.funcs.map a.trFunc⟩

/-! ## The simple allocation -/

/-- Virtual registers below `k` in physical registers `2 … k + 1`; the others
spilled; physical registers `0` and `1` are scratch. -/
def firstK (k : Nat) : Allocation Nat (Fin (k + 2)) where
  home v := if h : v < k then .reg ⟨v + 2, by omega⟩ else .spill (v - k)
  scratch₀ := 0
  scratch₁ := 1

theorem firstK_valid (k : Nat) : (firstK k).Valid where
  scratch_ne := by simp [firstK]
  home_ne₀ := by
    intro v
    simp only [firstK]
    split
    · intro h; cases h
    · intro h; cases h
  home_ne₁ := by
    intro v
    simp only [firstK]
    split
    · intro h; cases h
    · intro h; cases h
  injective := by
    intro v w h
    simp only [firstK] at h
    split at h <;> split at h
    · simpa [Fin.ext_iff] using h
    · cases h
    · cases h
    · simp only [Home.spill.injEq] at h; omega

/-! ## Correctness -/

variable [DecidableEq V] [DecidableEq P] {a : Allocation V P}

omit [DecidableEq P] in
theorem Home.loc_injective : Function.Injective (Home.loc (P := P)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [Home.loc]

omit [DecidableEq P] in
theorem Allocation.loc_injective (hv : a.Valid) : Function.Injective a.loc := by
  intro x y h
  cases x with
  | reg v =>
    cases y with
    | reg w => exact congrArg Loc.reg (hv.injective (Home.loc_injective h))
    | slot n =>
      simp only [Allocation.loc] at h
      cases hh : a.home v <;> simp [hh, Home.loc] at h; omega
  | slot n =>
    cases y with
    | reg w =>
      simp only [Allocation.loc] at h
      cases hh : a.home w <;> simp [hh, Home.loc] at h; omega
    | slot m => simp only [Allocation.loc, Loc.slot.injEq] at h; congr 1; omega

omit [DecidableEq V] [DecidableEq P] in
theorem Allocation.loc_ne_scratch (hv : a.Valid) (l : Loc V) (sc : P)
    (hsc : sc = a.scratch₀ ∨ sc = a.scratch₁) : a.loc l ≠ .reg sc := by
  cases l with
  | reg v =>
    simp only [Allocation.loc]
    cases hh : a.home v with
    | reg p =>
      simp only [Home.loc, ne_eq, Loc.reg.injEq]
      rintro rfl
      rcases hsc with rfl | rfl
      · exact hv.home_ne₀ v hh
      · exact hv.home_ne₁ v hh
    | spill m => simp [Home.loc]
  | slot n => simp [Allocation.loc]

theorem Frame.read_write {R : Type} [DecidableEq R] (fr : Frame R) (l l' : Loc R) (x : Word) :
    (fr.write l x).read l' = if l' = l then some x else fr.read l' := by
  cases l <;> cases l' <;> simp [Frame.write, Frame.read, Frame.set, Frame.setSlot]

theorem Frame.read_set_other {R : Type} [DecidableEq R] (fr : Frame R) (r : R) (l : Loc R)
    (x : Word) (h : l ≠ .reg r) : (fr.set r x).read l = fr.read l := by
  cases l with
  | reg q =>
    have : q ≠ r := by rintro rfl; exact h rfl
    simp [Frame.read, this]
  | slot n => rfl

/-- Every defined source location is represented at its target location. -/
def FrameRel (a : Allocation V P) (fs : Frame V) (ft : Frame P) : Prop :=
  ∀ l x, fs.read l = some x → ft.read (a.loc l) = some x

omit [DecidableEq V] [DecidableEq P] in
theorem FrameRel.empty : FrameRel a (Frame.empty : Frame V) (Frame.empty : Frame P) := by
  intro l x h
  cases l <;> simp [Frame.read, Frame.empty] at h

theorem FrameRel.write (hv : a.Valid) {fs : Frame V} {ft : Frame P} (hr : FrameRel a fs ft)
    (l : Loc V) (x : Word) : FrameRel a (fs.write l x) (ft.write (a.loc l) x) := by
  intro l' y h
  rw [Frame.read_write] at h ⊢
  by_cases e : l' = l
  · subst e; simpa using h
  · have e' : a.loc l' ≠ a.loc l := fun h' => e (Allocation.loc_injective hv h')
    simp only [e, e', ite_false] at h ⊢
    exact hr l' y h

omit [DecidableEq V] in
theorem FrameRel.set_scratch (hv : a.Valid) {fs : Frame V} {ft : Frame P} (hr : FrameRel a fs ft)
    {sc : P} (hsc : sc = a.scratch₀ ∨ sc = a.scratch₁) (x : Word) : FrameRel a fs (ft.set sc x) := by
  intro l y h
  rw [Frame.read_set_other _ _ _ _ (Allocation.loc_ne_scratch hv l sc hsc)]
  exact hr l y h

omit [DecidableEq V] [DecidableEq P] in
theorem FrameRel.readAll {fs : Frame V} {ft : Frame P} (hr : FrameRel a fs ft) :
    ∀ {locs : List (Loc V)} {vals : List Word}, fs.readAll locs = some vals →
      ft.readAll (locs.map a.loc) = some vals
  | [], vals, h => by simpa [Frame.readAll] using h
  | l :: ls, vals, h => by
    simp only [Frame.readAll, List.mapM_cons] at h ⊢
    cases hl : fs.read l with
    | none => simp [hl] at h
    | some x =>
      cases hls : ls.mapM fs.read with
      | none => simp [hl, hls] at h
      | some xs =>
        have := FrameRel.readAll hr (locs := ls) hls
        simp only [Frame.readAll] at this
        simp [hl, hls] at h
        subst h
        simp [hr l x hl, this]

theorem FrameRel.writeAll (hv : a.Valid) :
    ∀ {locs : List (Loc V)} {vals : List Word} {fs fs' : Frame V} {ft : Frame P},
    FrameRel a fs ft → fs.writeAll locs vals = some fs' →
    ∃ ft', ft.writeAll (locs.map a.loc) vals = some ft' ∧ FrameRel a fs' ft'
  | [], [], _, _, ft, hr, h => by cases h; exact ⟨ft, rfl, hr⟩
  | [], _ :: _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, h => by cases h
  | l :: ls, x :: xs, fs, fs', ft, hr, h => by
    simp only [Frame.writeAll] at h
    obtain ⟨ft', h', r'⟩ := FrameRel.writeAll hv (hr.write hv l x) h
    exact ⟨ft', by simpa [Frame.writeAll] using h', r'⟩

/-! ### Operands and destinations -/

omit [DecidableEq V] in
theorem use_spec (hv : a.Valid) {fs : Frame V} {ft : Frame P} (hr : FrameRel a fs ft)
    {v : V} {x : Word} (hx : fs.get v = some x) {sc : P} (hsc : sc = a.scratch₀ ∨ sc = a.scratch₁)
    (m : Memory) :
    ∃ ft₁, execOps (a.use v sc).1 ft m = some (ft₁, m) ∧ ft₁.get (a.use v sc).2 = some x ∧
      FrameRel a fs ft₁ ∧ ∀ q, q ≠ sc → ft₁.regs q = ft.regs q := by
  have hl := hr (.reg v) x hx
  simp only [Allocation.loc] at hl
  unfold Allocation.use
  cases hh : a.home v with
  | reg p =>
    simp only [hh, Home.loc, Frame.read] at hl
    exact ⟨ft, rfl, hl, hr, fun _ _ => rfl⟩
  | spill n =>
    simp only [hh, Home.loc, Frame.read] at hl
    refine ⟨ft.set sc x, ?_, by simp [Frame.get], hr.set_scratch hv hsc x, ?_⟩
    · simp [execOps, Op.exec, hl]
    · intro q hq; simp [hq]

omit [DecidableEq V] [DecidableEq P] in
/-- The operand register is a home register or the chosen scratch register. -/
theorem use_reg (v : V) (sc : P) :
    (a.use v sc).2 = sc ∨ a.home v = .reg (a.use v sc).2 := by
  unfold Allocation.use
  cases a.home v <;> simp

omit [DecidableEq V] [DecidableEq P] in
theorem use_ne (hv : a.Valid) (v : V) : (a.use v a.scratch₀).2 ≠ a.scratch₁ := by
  rcases use_reg (a := a) v a.scratch₀ with h | h
  · rw [h]; exact hv.scratch_ne
  · intro e; rw [e] at h; exact hv.home_ne₁ v h

theorem dest_spec (hv : a.Valid) {fs : Frame V} {ft : Frame P} (hr : FrameRel a fs ft)
    (d : V) (z : Word) (m : Memory) :
    ∃ ft', execOps (a.dest d).2 (ft.set (a.dest d).1 z) m = some (ft', m) ∧
      FrameRel a (fs.set d z) ft' := by
  have hw := hr.write hv (.reg d) z
  unfold Allocation.dest
  cases hh : a.home d with
  | reg p =>
    simp only [Allocation.loc, hh, Home.loc, Frame.write] at hw
    exact ⟨_, rfl, hw⟩
  | spill n =>
    have hw' := (hr.set_scratch hv (Or.inl rfl) z).write hv (.reg d) z
    simp only [Allocation.loc, hh, Home.loc, Frame.write] at hw'
    refine ⟨_, ?_, hw'⟩
    simp [execOps, Op.exec, Frame.get]

theorem trOp_spec (hv : a.Valid) {o : Op V} {fs fs' : Frame V} {ft : Frame P} {m m' : Memory}
    (hr : FrameRel a fs ft) (hx : o.exec fs m = some (fs', m')) :
    ∃ ft', execOps (a.trOp o) ft m = some (ft', m') ∧ FrameRel a fs' ft' := by
  cases o with
  | const d v =>
    simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    obtain ⟨ft', h, r⟩ := dest_spec hv hr d v m
    exact ⟨ft', by simpa [Allocation.trOp, execOps_cons, Op.exec] using h, r⟩
  | move d s =>
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hs (Or.inl rfl) m
      obtain ⟨ft', h, r⟩ := dest_spec hv r₁ d x m
      refine ⟨ft', ?_, r⟩
      simp only [Allocation.trOp, execOps_append, e₁, Option.bind_some, execOps_cons, Op.exec]
      simpa [g₁] using h
  | unary op d s =>
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hs (Or.inl rfl) m
      obtain ⟨ft', h, r⟩ := dest_spec hv r₁ d (op.eval x) m
      refine ⟨ft', ?_, r⟩
      simp only [Allocation.trOp, execOps_append, e₁, Option.bind_some, execOps_cons, Op.exec]
      simpa [g₁] using h
  | binary op d x y =>
    simp only [Op.exec] at hx
    cases hx' : fs.get x with
    | none => simp [hx'] at hx
    | some vx =>
      cases hy' : fs.get y with
      | none => simp [hx', hy'] at hx
      | some vy =>
        cases hz : op.eval vx vy with
        | none => simp [hx', hy', hz] at hx
        | some z =>
          simp only [hx', hy', hz, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hx' (Or.inl rfl) m
          obtain ⟨ft₂, e₂, g₂, r₂, k₂⟩ := use_spec hv r₁ hy' (Or.inr rfl) m
          have g₁' : ft₂.get (a.use x a.scratch₀).2 = some vx := by
            simp only [Frame.get] at g₁ ⊢
            rw [k₂ _ (use_ne hv x)]; exact g₁
          obtain ⟨ft', h, r⟩ := dest_spec hv r₂ d z m
          refine ⟨ft', ?_, r⟩
          simp only [Allocation.trOp, execOps_append, e₁, e₂, Option.bind_some, execOps_cons,
            Op.exec]
          simpa [g₁', g₂, hz] using h
  | load w e d b off =>
    simp only [Op.exec] at hx
    cases hb : fs.get b with
    | none => simp [hb] at hx
    | some vb =>
      cases hl : m.load w e (vb.toNat + off) with
      | none => simp [hb, hl] at hx
      | some z =>
        simp only [hb, hl, Option.bind_some, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hb (Or.inl rfl) m
        obtain ⟨ft', h, r⟩ := dest_spec hv r₁ d z m
        refine ⟨ft', ?_, r⟩
        simp only [Allocation.trOp, execOps_append, e₁, Option.bind_some, execOps_cons, Op.exec]
        simpa [g₁, hl] using h
  | store w b off src =>
    simp only [Op.exec] at hx
    cases hb : fs.get b with
    | none => simp [hb] at hx
    | some vb =>
      cases hs : fs.get src with
      | none => simp [hb, hs] at hx
      | some vs =>
        cases hm : m.store w (vb.toNat + off) vs with
        | none => simp [hb, hs, hm] at hx
        | some mm =>
          simp only [hb, hs, hm, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hb (Or.inl rfl) m
          obtain ⟨ft₂, e₂, g₂, r₂, k₂⟩ := use_spec hv r₁ hs (Or.inr rfl) m
          have g₁' : ft₂.get (a.use b a.scratch₀).2 = some vb := by
            simp only [Frame.get] at g₁ ⊢
            rw [k₂ _ (use_ne hv b)]; exact g₁
          refine ⟨ft₂, ?_, r₂⟩
          simp only [Allocation.trOp, execOps_append, e₁, e₂, Option.bind_some, execOps_cons,
            Op.exec]
          simp [g₁', g₂, hm]
  | slotGet d n =>
    simp only [Op.exec] at hx
    cases hs : fs.slots n with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have ht : ft.slots (2 * n) = some x := hr (.slot n) x hs
      obtain ⟨ft', h, r⟩ := dest_spec hv hr d x m
      refine ⟨ft', ?_, r⟩
      simp only [Allocation.trOp, execOps_cons, Op.exec]
      simpa [ht] using h
  | slotSet n s =>
    simp only [Op.exec] at hx
    cases hs : fs.get s with
    | none => simp [hs] at hx
    | some x =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hr hs (Or.inl rfl) m
      have hw := r₁.write hv (.slot n) x
      simp only [Allocation.loc, Frame.write] at hw
      refine ⟨_, ?_, hw⟩
      simp only [Allocation.trOp, execOps_append, e₁, Option.bind_some, execOps_cons, Op.exec]
      simp [g₁]

/-! ### Program layout -/

omit [DecidableEq V] [DecidableEq P] in
theorem trOp_ne_nil (o : Op V) : a.trOp o ≠ [] := by
  cases o <;> simp [Allocation.trOp]

/-- The index in the spilled block of source instruction `i`. -/
def Allocation.offset (a : Allocation V P) (b : Block V) (i : Nat) : Nat :=
  ((b.instrs.take i).map a.trInstr).flatten.length

/-- Program points of the source mapped to the spilled program. -/
def mapPoint (a : Allocation V P) (p : Prog V) (pt : Point) : Point :=
  match p.block? pt.func pt.label with
  | some b => ⟨pt.func, pt.label, a.offset b pt.index⟩
  | none => pt

omit [DecidableEq V] [DecidableEq P] in
theorem spill_func? (p : Prog V) (f : FuncId) : (spill a p).func? f = (p.func? f).map a.trFunc := by
  simp [spill, Prog.func?]

omit [DecidableEq V] [DecidableEq P] in
theorem spill_block? (p : Prog V) (f : FuncId) (l : Label) :
    (spill a p).block? f l = (p.block? f l).map a.trBlock := by
  unfold Prog.block?
  rw [spill_func?]
  cases p.func? f <;> simp [Allocation.trFunc]

omit [DecidableEq V] [DecidableEq P] in
theorem mapPoint_zero (p : Prog V) (f : FuncId) (l : Label) : mapPoint a p ⟨f, l, 0⟩ = ⟨f, l, 0⟩ := by
  unfold mapPoint
  cases p.block? f l <;> simp [Allocation.offset]

theorem flatten_map_split {α β : Type} (f : α → List β) (L : List α) (i : Nat) (h : i < L.length) :
    (L.map f).flatten = ((L.take i).map f).flatten ++ (f L[i] ++ ((L.drop (i + 1)).map f).flatten) := by
  conv_lhs => rw [← List.take_append_drop i L, List.drop_eq_getElem_cons h]
  rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]

omit [DecidableEq V] [DecidableEq P] in
theorem trBlock_drop_instr (b : Block V) {i : Nat} (h : i < b.instrs.length) :
    (a.trBlock b).instrs.drop (a.offset b i) =
      a.trInstr b.instrs[i] ++
        (((b.instrs.drop (i + 1)).map a.trInstr).flatten ++ (a.trTerm b.term).1.map .op) := by
  simp only [Allocation.trBlock, Allocation.offset]
  rw [flatten_map_split _ _ i h, List.append_assoc, List.drop_left, List.append_assoc]

omit [DecidableEq V] [DecidableEq P] in
theorem offset_succ (b : Block V) {i : Nat} (h : i < b.instrs.length) :
    a.offset b (i + 1) = a.offset b i + (a.trInstr b.instrs[i]).length := by
  unfold Allocation.offset
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList, List.map_append, List.flatten_append, List.length_append, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

omit [DecidableEq V] [DecidableEq P] in
theorem trBlock_drop_term (b : Block V) :
    (a.trBlock b).instrs.drop (a.offset b b.instrs.length) = (a.trTerm b.term).1.map .op := by
  simp only [Allocation.trBlock, Allocation.offset, List.take_length]
  exact List.drop_left

omit [DecidableEq V] [DecidableEq P] in
theorem trBlock_length (b : Block V) :
    (a.trBlock b).instrs.length = a.offset b b.instrs.length + (a.trTerm b.term).1.length := by
  simp [Allocation.trBlock, Allocation.offset]

omit [DecidableEq V] [DecidableEq P] in
theorem fetch_instr_spill {p : Prog V} {pt : Point} {ins : Instr V}
    (h : p.fetch pt = some (.instr ins)) :
    ∃ b rest, (spill a p).block? pt.func pt.label = some (a.trBlock b) ∧
      mapPoint a p pt = ⟨pt.func, pt.label, a.offset b pt.index⟩ ∧
      mapPoint a p pt.next = ⟨pt.func, pt.label, a.offset b pt.index + (a.trInstr ins).length⟩ ∧
      (a.trBlock b).instrs.drop (a.offset b pt.index) = a.trInstr ins ++ rest := by
  obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some h
  rcases hc with ⟨i', hi, e⟩ | ⟨_, e⟩
  · cases e
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    refine ⟨b, _, by rw [spill_block?, hb]; rfl, by simp [mapPoint, hb], ?_,
      trBlock_drop_instr b hlt⟩
    simp [mapPoint, hb, offset_succ b hlt]
  · cases e

omit [DecidableEq V] [DecidableEq P] in
theorem fetch_term_spill {p : Prog V} {pt : Point} {t : Term V}
    (h : p.fetch pt = some (.term t)) :
    ∃ b, (spill a p).block? pt.func pt.label = some (a.trBlock b) ∧
      mapPoint a p pt = ⟨pt.func, pt.label, a.offset b pt.index⟩ ∧
      (a.trBlock b).instrs.drop (a.offset b pt.index) = (a.trTerm t).1.map .op ∧
      (a.trBlock b).instrs.length = a.offset b pt.index + (a.trTerm t).1.length ∧
      (a.trBlock b).term = (a.trTerm t).2 := by
  obtain ⟨b, hb, hc⟩ := Prog.fetch_eq_some h
  rcases hc with ⟨i', _, e⟩ | ⟨hi, e⟩
  · cases e
  · cases e
    refine ⟨b, by rw [spill_block?, hb]; rfl, by simp [mapPoint, hb], ?_, ?_, rfl⟩
    · rw [hi]; exact trBlock_drop_term b
    · rw [hi]; exact trBlock_length b

omit [DecidableEq V] [DecidableEq P] in
theorem fetch_of_drop {R : Type} {q : Prog R} {f : FuncId} {l : Label} {i : Nat} {b : Block R}
    (hb : q.block? f l = some b) {x : Instr R} {rest : List (Instr R)}
    (h : b.instrs.drop i = x :: rest) : q.fetch ⟨f, l, i⟩ = some (.instr x) := by
  have hi : b.instrs[i]? = some x := by
    have := congrArg (fun l => l[0]?) h
    simpa [List.getElem?_drop] using this
  exact Prog.fetch_eq_instr (pt := ⟨f, l, i⟩) hb hi

omit [DecidableEq V] [DecidableEq P] in
theorem fetch_at_length {R : Type} {q : Prog R} {f : FuncId} {l : Label} {b : Block R}
    (hb : q.block? f l = some b) : q.fetch ⟨f, l, b.instrs.length⟩ = some (.term b.term) :=
  Prog.fetch_eq_term (pt := ⟨f, l, b.instrs.length⟩) hb rfl

theorem spill_enter (hv : a.Valid) {p : Prog V} {f : FuncId} {vals : List Word} {pt : Point}
    {fr : Frame V} (h : p.enter f vals = some (pt, fr)) :
    ∃ ft, (spill a p).enter f vals = some (pt, ft) ∧ FrameRel a fr ft ∧ pt.index = 0 := by
  unfold Prog.enter at h ⊢
  rw [spill_func?]
  cases hf : p.func? f with
  | none => simp [hf] at h
  | some fn =>
    simp only [hf, Option.bind_some] at h
    cases hw : Frame.empty.writeAll fn.params vals with
    | none => simp [hw] at h
    | some fr' =>
      simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ft, hwt, hr⟩ := FrameRel.writeAll hv FrameRel.empty hw
      refine ⟨ft, ?_, hr, rfl⟩
      simp [Allocation.trFunc, hwt]

/-! ### The simulation -/

def StackRel (a : Allocation V P) (p : Prog V) : List (Activation V) → List (Activation P) → Prop
  | [], [] => True
  | x :: xs, y :: ys =>
    (y.point = mapPoint a p x.point ∧ FrameRel a x.frame y.frame) ∧ StackRel a p xs ys
  | _, _ => False

structure Rel (a : Allocation V P) (p : Prog V) (s : State V) (t : State P) : Prop where
  point : t.point = mapPoint a p s.point
  frame : FrameRel a s.frame t.frame
  stack : StackRel a p s.stack t.stack
  mem : t.mem = s.mem

/-- The spilling pass as a per-transition simulation into the spilled program. -/
def simulation (hv : a.Valid) (p : Prog V) : CaseSimulation p (LirTarget (spill a p)) where
  Match := Rel a p
  measure := fun _ => 0
  Returned := fun vs m t => step (spill a p) t = .returned vs m
  Trapped := fun m t => step (spill a p) t = .trapped m
  op := by
    intro s t o fr m hm hf he
    obtain ⟨b, rest, hb, hpt, hnext, hdrop⟩ := fetch_instr_spill (a := a) hf
    obtain ⟨ft', hx, hr⟩ := trOp_spec hv hm.frame he
    obtain ⟨o', os', hos⟩ : ∃ o' os', a.trOp o = o' :: os' := by
      cases h : a.trOp o with
      | nil => exact absurd h (trOp_ne_nil o)
      | cons o' os' => exact ⟨o', os', rfl⟩
    rw [hos] at hx
    have hcode : (a.trBlock b).instrs.drop t.point.index = (o' :: os').map Instr.op ++ rest := by
      rw [hm.point, hpt]; simpa [Allocation.trInstr, hos] using hdrop
    have hb' : (spill a p).block? t.point.func t.point.label = some (a.trBlock b) := by
      rw [hm.point, hpt]; exact hb
    have tg := transGen_execOps hb' hcode (by rw [hm.mem]; exact hx)
    refine ⟨⟨⟨t.point.func, t.point.label, t.point.index + (o' :: os').length⟩, ft', t.stack, m⟩,
      ⟨?_, hr, hm.stack, rfl⟩, .inl tg⟩
    simp only [hnext, hm.point, hpt, Allocation.trInstr, List.length_map, hos]
  call := by
    intro s t f args results vals pt fr hm hf ha he
    obtain ⟨b, rest, hb, hpt, _, hdrop⟩ := fetch_instr_spill (a := a) hf
    obtain ⟨ft, hen, hfr, hidx⟩ := spill_enter hv he
    have hft : (spill a p).fetch t.point =
        some (.instr (.call f (args.map a.loc) (results.map a.loc))) := by
      rw [hm.point, hpt]
      exact fetch_of_drop hb (by simpa [Allocation.trInstr] using hdrop)
    have st : Step (spill a p) t ⟨pt, ft, ⟨t.point, t.frame⟩ :: t.stack, t.mem⟩ :=
      (Transition.call hft (hm.frame.readAll ha) hen).step_eq
    refine ⟨⟨pt, ft, ⟨t.point, t.frame⟩ :: t.stack, t.mem⟩,
      ⟨?_, hfr, ⟨⟨hm.point, hm.frame⟩, hm.stack⟩, hm.mem⟩, .inl (.single st)⟩
    obtain ⟨pf, pl, pi⟩ := pt
    simp only at hidx
    subst hidx
    exact (mapPoint_zero p pf pl).symm
  fop := by
    intro s t op d x y fr hm hf he
    obtain ⟨b, rest, hb, hpt, hnext, hdrop⟩ := fetch_instr_spill (a := a) hf
    simp only [FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨vx, hx', vy, hy', rfl⟩ := he
    obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hm.frame hx' (Or.inl rfl) t.mem
    obtain ⟨ft₂, e₂, g₂, r₂, k₂⟩ := use_spec hv r₁ hy' (Or.inr rfl) t.mem
    have g₁' : ft₂.get (a.use x a.scratch₀).2 = some vx := by
      simp only [Frame.get] at g₁ ⊢
      rw [k₂ _ (use_ne hv x)]; exact g₁
    obtain ⟨ft', h, r⟩ := dest_spec hv r₂ d (op.eval vx vy) t.mem
    have hb' : (spill a p).block? t.point.func t.point.label = some (a.trBlock b) := by
      rw [hm.point, hpt]; exact hb
    have hcode : (a.trBlock b).instrs.drop t.point.index =
        ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1).map Instr.op ++
          (.fop op (a.dest d).1 (a.use x a.scratch₀).2 (a.use y a.scratch₁).2 ::
            ((a.dest d).2.map .op ++ rest)) := by
      rw [hm.point, hpt]; simpa [Allocation.trInstr] using hdrop
    have hus : execOps ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1) t.frame t.mem =
        some (ft₂, t.mem) := by
      simp [execOps_append, e₁, e₂]
    have s₁ := steps_execOps hb' hcode hus
    have hdrop₁ : (a.trBlock b).instrs.drop
        (t.point.index + ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1).length) =
        .fop op (a.dest d).1 (a.use x a.scratch₀).2 (a.use y a.scratch₁).2 ::
          ((a.dest d).2.map .op ++ rest) := by
      rw [← List.drop_drop, hcode, List.drop_left' (by simp)]
    have hft := fetch_of_drop hb' hdrop₁
    have hex : op.exec (a.dest d).1 (a.use x a.scratch₀).2 (a.use y a.scratch₁).2 ft₂ =
        some (ft₂.set (a.dest d).1 (op.eval vx vy)) := by
      simp [FOp.exec, g₁', g₂]
    have st := (Transition.fop (s := ⟨_, ft₂, t.stack, t.mem⟩) hft hex).step_eq
    have s₃ := steps_execOps (s := ⟨⟨t.point.func, t.point.label,
      t.point.index + ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1).length + 1⟩,
      ft₂.set (a.dest d).1 (op.eval vx vy), t.stack, t.mem⟩) hb'
      (drop_succ_of_cons hdrop₁) h
    refine ⟨⟨⟨t.point.func, t.point.label,
      t.point.index + ((a.use x a.scratch₀).1 ++ (a.use y a.scratch₁).1).length + 1 +
        (a.dest d).2.length⟩, ft', t.stack, t.mem⟩, ⟨?_, r, hm.stack, hm.mem⟩,
      .inl (Relation.TransGen.trans_right s₁ (Relation.TransGen.head' st s₃))⟩
    simp only [hnext, hm.point, hpt, Allocation.trInstr, List.length_append, List.length_map,
      List.length_cons]
    congr 1
    omega
  jump := by
    intro s t l hm hf
    obtain ⟨b, hb, hpt, _, hlen, hterm⟩ := fetch_term_spill (a := a) hf
    have hft : (spill a p).fetch t.point = some (.term (.jump l)) := by
      rw [hm.point, hpt]
      have := fetch_at_length hb
      simp only [hlen, Allocation.trTerm, List.length_nil, Nat.add_zero] at this
      rw [this, hterm]; rfl
    have st : Step (spill a p) t { t with point := ⟨t.point.func, l, 0⟩ } :=
      (Transition.jump hft).step_eq
    refine ⟨{ t with point := ⟨t.point.func, l, 0⟩ }, ⟨?_, hm.frame, hm.stack, hm.mem⟩,
      .inl (.single st)⟩
    simp only [hm.point, hpt]
    exact (mapPoint_zero p _ _).symm
  branch := by
    intro s t c l₁ l₂ x hm hf hc
    obtain ⟨b, hb, hpt, hdrop, hlen, hterm⟩ := fetch_term_spill (a := a) hf
    obtain ⟨ft₁, e₁, g₁, r₁, _⟩ := use_spec hv hm.frame hc (Or.inl rfl) t.mem
    have hb' : (spill a p).block? t.point.func t.point.label = some (a.trBlock b) := by
      rw [hm.point, hpt]; exact hb
    have hcode : (a.trBlock b).instrs.drop t.point.index =
        (a.use c a.scratch₀).1.map Instr.op ++ [] := by
      rw [hm.point, hpt, List.append_nil]; simpa [Allocation.trTerm] using hdrop
    have steps := steps_execOps hb' hcode e₁
    have hft : (spill a p).fetch
        ⟨t.point.func, t.point.label, t.point.index + (a.use c a.scratch₀).1.length⟩ =
        some (.term (.branch (a.use c a.scratch₀).2 l₁ l₂)) := by
      have := fetch_at_length hb'
      rw [hlen] at this
      simp only [hm.point, hpt, Allocation.trTerm] at this ⊢
      rw [this, hterm]; rfl
    have st : Step (spill a p) ⟨_, ft₁, t.stack, t.mem⟩
        ⟨⟨t.point.func, if x = 0 then l₂ else l₁, 0⟩, ft₁, t.stack, t.mem⟩ :=
      (Transition.branch (s := ⟨_, ft₁, t.stack, t.mem⟩) hft g₁).step_eq
    refine ⟨⟨⟨t.point.func, if x = 0 then l₂ else l₁, 0⟩, ft₁, t.stack, t.mem⟩,
      ⟨?_, r₁, hm.stack, hm.mem⟩, .inl (Relation.TransGen.tail' steps st)⟩
    simp only [hm.point, hpt]
    exact (mapPoint_zero p _ _).symm
  ret := by
    intro s t locs vals act rest f args results fr hm hf hv' hs ha hw
    obtain ⟨b, hb, hpt, _, hlen, hterm⟩ := fetch_term_spill (a := a) hf
    have hft : (spill a p).fetch t.point = some (.term (.ret (locs.map a.loc))) := by
      rw [hm.point, hpt]
      have := fetch_at_length hb
      simp only [hlen, Allocation.trTerm, List.length_nil, Nat.add_zero] at this
      rw [this, hterm]; rfl
    have hst := hm.stack
    rw [hs] at hst
    cases htst : t.stack with
    | nil => rw [htst] at hst; exact hst.elim
    | cons act' rest' =>
      rw [htst] at hst
      obtain ⟨⟨hap, haf⟩, hrest⟩ := hst
      obtain ⟨b₂, rest₂, hb₂, hpt₂, hnext₂, hdrop₂⟩ := fetch_instr_spill (a := a) ha
      have hfa : (spill a p).fetch act'.point =
          some (.instr (.call f (args.map a.loc) (results.map a.loc))) := by
        rw [hap, hpt₂]
        exact fetch_of_drop hb₂ (by simpa [Allocation.trInstr] using hdrop₂)
      obtain ⟨ft, hwt, hr⟩ := FrameRel.writeAll hv haf hw
      have st : Step (spill a p) t ⟨act'.point.next, ft, rest', t.mem⟩ :=
        (Transition.ret hft (hm.frame.readAll hv') htst hfa hwt).step_eq
      refine ⟨⟨act'.point.next, ft, rest', t.mem⟩, ⟨?_, hr, hrest, hm.mem⟩, .inl (.single st)⟩
      simp only [hnext₂, hap, hpt₂, Allocation.trInstr, List.length_singleton]
      rfl
  halt := by
    intro s t locs vals hm hf hv' hs
    obtain ⟨b, hb, hpt, _, hlen, hterm⟩ := fetch_term_spill (a := a) hf
    have hft : (spill a p).fetch t.point = some (.term (.ret (locs.map a.loc))) := by
      rw [hm.point, hpt]
      have := fetch_at_length hb
      simp only [hlen, Allocation.trTerm, List.length_nil, Nat.add_zero] at this
      rw [this, hterm]; rfl
    have hst := hm.stack
    rw [hs] at hst
    have htst : t.stack = [] := by
      cases h : t.stack with
      | nil => rfl
      | cons _ _ => rw [h] at hst; exact hst.elim
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.halt hft (hm.frame.readAll hv') htst).step_eq
  trap := by
    intro s t hm hf
    obtain ⟨b, hb, hpt, _, hlen, hterm⟩ := fetch_term_spill (a := a) hf
    have hft : (spill a p).fetch t.point = some (.term .trap) := by
      rw [hm.point, hpt]
      have := fetch_at_length hb
      simp only [hlen, Allocation.trTerm, List.length_nil, Nat.add_zero] at this
      rw [this, hterm]; rfl
    refine ⟨t, .refl, ?_⟩
    rw [← hm.mem]
    exact (Transition.trap hft).step_eq

theorem spill_start (hv : a.Valid) {p : Prog V} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State V} (h : p.start f args mem = some s) :
    ∃ t, (spill a p).start f args mem = some t ∧ Rel a p s t := by
  unfold Prog.start at h ⊢
  cases he : p.enter f args with
  | none => simp [he] at h
  | some r =>
    obtain ⟨pt, fr⟩ := r
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨ft, hen, hr, hidx⟩ := spill_enter hv he
    refine ⟨⟨pt, ft, [], mem⟩, by rw [hen]; rfl, ⟨?_, hr, trivial, rfl⟩⟩
    obtain ⟨pf, pl, pi⟩ := pt
    simp only at hidx
    subst hidx
    exact (mapPoint_zero p pf pl).symm

/-- **Semantic preservation of spilling.** For every valid allocation and every
program, each non-stuck behaviour of a whole-program run (returned values with
final memory, trap with memory, divergence) is a behaviour of the spilled
program started with the same function, arguments and memory. -/
theorem spill_behaves (hv : a.Valid) {p : Prog V} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State V} (h : p.start f args mem = some s) {b : Behavior} (hb : Behaves p s b)
    (hns : b ≠ .stuck) :
    ∃ t, (spill a p).start f args mem = some t ∧ Behaves (spill a p) t b := by
  obtain ⟨t, ht, hr⟩ := spill_start hv h
  exact ⟨t, ht, (simulation hv p).toForward.behaves ⟨fun _ _ _ h => h, fun _ _ h => h⟩ hr hb hns⟩

/-- Spilling with the simple `firstK` allocation. -/
theorem spill_firstK_behaves (k : Nat) {p : Prog Nat} {f : FuncId} {args : List Word}
    {mem : Memory} {s : State Nat} (h : p.start f args mem = some s) {b : Behavior}
    (hb : Behaves p s b) (hns : b ≠ .stuck) :
    ∃ t, (spill (firstK k) p).start f args mem = some t ∧ Behaves (spill (firstK k) p) t b :=
  spill_behaves (firstK_valid k) h hb hns

/-- Spilling composed with any backend simulation of the spilled program: the
backend's target, started in a state matched with the spilled program's start,
reproduces every returned result, trap and divergence of the source. -/
theorem spill_then_backend (hv : a.Valid) {T : Type} {TStep : T → T → Prop} {p : Prog V}
    (sim : ForwardSimulation (spill a p) TStep) {f : FuncId} {args : List Word} {mem : Memory}
    {s : State V} {τ : T} (hs : p.start f args mem = some s)
    (hmatch : ∀ t, (spill a p).start f args mem = some t → sim.Match t τ) :
    (∀ vs m, Behaves p s (.returned vs m) → ∃ τ', ReflTransGen TStep τ τ' ∧ sim.Returned vs m τ') ∧
    (∀ m, Behaves p s (.trapped m) → ∃ τ', ReflTransGen TStep τ τ' ∧ sim.Trapped m τ') ∧
    (Diverges p s → InfiniteTrace TStep τ) := by
  refine ⟨fun vs m hb => ?_, fun m hb => ?_, fun hb => ?_⟩
  · obtain ⟨t, ht, hb'⟩ := spill_behaves hv hs hb (by intro h; cases h)
    exact sim.returns (hmatch t ht) hb'
  · obtain ⟨t, ht, hb'⟩ := spill_behaves hv hs hb (by intro h; cases h)
    exact sim.traps (hmatch t ht) hb'
  · obtain ⟨t, ht, hb'⟩ := spill_behaves (b := .diverges) hv hs hb (by intro h; cases h)
    exact sim.diverges (hmatch t ht) hb'

end Silmaril.Machine.Lir.Alloc
