module

public import Silmaril.Machine.RiscV.Lir.Mem.Defs
/-!
# Code emission and layout

The emitted program is one instruction list placed at `codeBase`:

* indices `0`, `1`, `2`: three `EBREAK` stubs, the *halt*, *trap* and *stack
  overflow* addresses;
* then every function: a prologue followed by its blocks in label order, each
  block the code of its instructions followed by the code of its terminator.

Instruction and terminator code sizes depend only on the Lir instruction
(`instrSize`, `termSize`), so the layout (`funcStart`, `blockStart`,
`pointIdx`) is computed before emission and the emitted code refers to it for
`JAL` offsets. `code_at_instr`, `code_at_term` and `code_at_prologue` show that
the code found at the index of a program point is the code emitted for it.

## Frames

Every function uses a frame of the same size `frameSize N`, where `N` bounds
the stack slots used by the program. From `sp`:

| Offset | Content |
| --- | --- |
| `8 * i`, `i < 14` | save area of allocatable register `i` across calls |
| `slotOff n = 8 * (14 + n)`, `n < N` | Lir stack slot `n` |
| `raOff N = 8 * (14 + N)` | saved return address |

## Calls

A call saves the 14 allocatable registers, loads the arguments into
`a0 …`, executes `JAL ra`, reloads the 14 registers and stores the results from
`a0 …` into their locations. The callee prologue is

```
addi sp, sp, -F
bgeu sp, s10, +8        # skip the next instruction if sp ≥ stack limit
jal  x0, overflow       # stack exhausted
sd   ra, raOff(sp)
<parameters from a0 …>
jal  x0, entry
```

and `ret` loads the returned values into `a0 …`, reloads `ra`, adds `F` to
`sp` and executes `jalr x0, 0(ra)`.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Machine.Lir (Prog Func Block Point Loc Op Term Unop Binop Label FuncId)

variable {P : Type}

/-! ## Frame layout -/

def slotOff (n : Nat) : Nat := 8 * (14 + n)
def raOff (N : Nat) : Nat := 8 * (14 + N)
def frameSize (N : Nat) : Nat := 16 * ((N + 16) / 2)

theorem raOff_lt (N : Nat) : raOff N + 8 ≤ frameSize N := by
  unfold raOff frameSize; omega

theorem frameSize_mod (N : Nat) : frameSize N % 16 = 0 := by
  unfold frameSize; omega

theorem slotOff_lt {n N : Nat} (h : n < N) : slotOff n + 8 ≤ raOff N := by
  unfold slotOff raOff; omega

/-! ## Instruction shorthands -/

def argRegN (j : Nat) : Reg := BitVec.ofNat 5 (10 + j)

theorem argRegN_eq {j : Nat} (h : j < 8) : argRegN j = argReg ⟨j, h⟩ := rfl

def mvI (rd rs : Reg) : Ext.Instr := .compute (.base (.imm .add rd rs 0#12))
def addiI (rd rs : Reg) (imm : BitVec 12) : Ext.Instr := .compute (.base (.imm .add rd rs imm))
def ldI (rd base : Reg) (off : Nat) : Ext.Instr := .load .ld rd base (imm12 off)
def sdI (base src : Reg) (off : Nat) : Ext.Instr := .store .sd base src (imm12 off)

/-- The `JAL` immediate from instruction index `src` to instruction index `dst`. -/
def jalHalf (src dst : Nat) : BitVec 20 :=
  (BitVec.ofInt 21 (4 * ((dst : Int) - src))).extractLsb' 1 20

/-- The byte offset from `src` to `dst` is in the `JAL` range. -/
def jalFits (src dst : Nat) : Bool :=
  decide (-(2 ^ 20 : Int) ≤ 4 * ((dst : Int) - src) ∧ 4 * ((dst : Int) - src) < 2 ^ 20)

def jalI (rd : Reg) (src dst : Nat) : Ext.Instr := .jal rd (jalHalf src dst)

/-! ## Operation code -/

section Code

variable (reg : P → Reg) (N : Nat)

def opCode : Op P → List Ext.Instr
  | .const d v => (li (reg d) v).map .compute
  | .move d s => (selMove (reg d) (reg s)).map .compute
  | .unary op d s => ((selUnop op (reg d) (reg s)).getD []).map .compute
  | .binary op d x y => (selBinop op (reg d) (reg x) (reg y)).map .compute
  | .load w e d b off => selLoad w e (reg d) (reg b) off
  | .store w b off s => selStore w (reg b) off (reg s)
  | .slotGet d n => [ldI (reg d) sp (slotOff n)]
  | .slotSet n s => [sdI sp (reg s) (slotOff n)]

/-- `a_j := loc`. -/
def locLoad (j : Nat) : Loc P → Ext.Instr
  | .reg r => mvI (argRegN j) (reg r)
  | .slot n => ldI (argRegN j) sp (slotOff n)

/-- `loc := a_j`. -/
def locStore (j : Nat) : Loc P → Ext.Instr
  | .reg r => mvI (reg r) (argRegN j)
  | .slot n => sdI sp (argRegN j) (slotOff n)

/-- `a_j, a_(j+1), … := locs`. -/
def loadLocsFrom (j : Nat) : List (Loc P) → List Ext.Instr
  | [] => []
  | l :: ls => locLoad reg j l :: loadLocsFrom (j + 1) ls

/-- `locs := a_j, a_(j+1), …`, from left to right. -/
def storeLocsFrom (j : Nat) : List (Loc P) → List Ext.Instr
  | [] => []
  | l :: ls => locStore reg j l :: storeLocsFrom (j + 1) ls

def loadLocs (locs : List (Loc P)) : List Ext.Instr := loadLocsFrom reg 0 locs
def storeLocs (locs : List (Loc P)) : List Ext.Instr := storeLocsFrom reg 0 locs

end Code

def saveAll : List Ext.Instr := (List.finRange 14).map fun i => sdI sp (allocReg i) (8 * i.val)
def restoreAll : List Ext.Instr := (List.finRange 14).map fun i => ldI (allocReg i) sp (8 * i.val)

@[simp] theorem saveAll_length : saveAll.length = 14 := by simp [saveAll]
@[simp] theorem restoreAll_length : restoreAll.length = 14 := by simp [restoreAll]
@[simp] theorem loadLocsFrom_length (reg : P → Reg) (j : Nat) (locs : List (Loc P)) :
    (loadLocsFrom reg j locs).length = locs.length := by
  induction locs generalizing j <;> simp [loadLocsFrom, *]
@[simp] theorem storeLocsFrom_length (reg : P → Reg) (j : Nat) (locs : List (Loc P)) :
    (storeLocsFrom reg j locs).length = locs.length := by
  induction locs generalizing j <;> simp [storeLocsFrom, *]
@[simp] theorem loadLocs_length (reg : P → Reg) (locs : List (Loc P)) :
    (loadLocs reg locs).length = locs.length := by simp [loadLocs]
@[simp] theorem storeLocs_length (reg : P → Reg) (locs : List (Loc P)) :
    (storeLocs reg locs).length = locs.length := by simp [storeLocs]

/-! ## Sizes -/

theorem liN_length (d d' : Reg) : ∀ n (v : Word), (liN d n v).length = (liN d' n v).length
  | 0, _ => rfl
  | n + 1, v => by
    unfold liN
    split
    · rfl
    · simp only [List.length_append, liN_length d d' n, List.length_cons, List.length_nil]

theorem li_length (d d' : Reg) (v : Word) : (li d v).length = (li d' v).length :=
  liN_length d d' 5 v

theorem selBinop_length (op : Binop) (d x y d' x' y' : Reg) :
    (selBinop op d x y).length = (selBinop op d' x' y').length := by
  cases op with
  | cmp c => cases c <;> rfl
  | cmp32 c => cases c <;> rfl
  | _ => rfl

theorem selUnop_length (op : Unop) (d x d' x' : Reg) :
    ((selUnop op d x).getD []).length = ((selUnop op d' x').getD []).length := by
  cases op <;> rfl

theorem addrSetup_length (rb rb' : Reg) (off : Nat) :
    (addrSetup rb off).1.length = (addrSetup rb' off).1.length ∧
      (addrSetup rb off).2 = (addrSetup rb' off).2 := by
  unfold addrSetup; split <;> simp

theorem loadBytes_length (rd : Reg) (i k : Nat) : (loadBytes rd i k).length = 1 + 3 * k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [loadBytes, ih]; omega

theorem storeBytes_length (rs : Reg) (i k : Nat) : (storeBytes rs i k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [storeBytes, ih]; omega

theorem signTail_length (w : Machine.Lir.Width) (e : Machine.Lir.Ext) (rd rd' : Reg) :
    (signTail w e rd).length = (signTail w e rd').length := by
  cases e <;> cases w <;> rfl

theorem opCode_length (reg reg' : P → Reg) (o : Op P) :
    (opCode reg o).length = (opCode reg' o).length := by
  cases o with
  | const d v => simp [opCode, li_length (reg d) (reg' d)]
  | move => rfl
  | unary op d s => simp [opCode, selUnop_length op (reg d) (reg s) (reg' d) (reg' s)]
  | binary op d x y =>
    simp only [opCode, List.length_map]
    exact selBinop_length op _ _ _ _ _ _
  | load w e d b off =>
    simp only [opCode, selLoad, List.length_append, loadBytes_length,
      (addrSetup_length (reg b) (reg' b) off).1, signTail_length w e (reg d) (reg' d)]
  | store w b off s =>
    simp only [opCode, selStore, List.length_append, storeBytes_length,
      (addrSetup_length (reg b) (reg' b) off).1]
  | slotGet => rfl
  | slotSet => rfl

def instrSize : Machine.Lir.Instr P → Nat
  | .op o => (opCode (fun _ => 0#5) o).length
  | .call _ args results => 29 + args.length + results.length
  | .fop .. => 1

def termSize : Term P → Nat
  | .jump _ => 1
  | .branch .. => 3
  | .ret locs => locs.length + 3
  | .trap => 1

def blockSize (b : Block P) : Nat := (b.instrs.map instrSize).sum + termSize b.term

def prologueSize (fn : Func P) : Nat := 5 + fn.params.length

def funcSize (fn : Func P) : Nat := prologueSize fn + (fn.blocks.map blockSize).sum

/-! ## Layout -/

def haltIdx : Nat := 0
def trapIdx : Nat := 1
def overflowIdx : Nat := 2

def funcStart (p : Prog P) (g : FuncId) : Nat := 3 + ((p.funcs.map funcSize).take g).sum

def blockStart (p : Prog P) (f : FuncId) (l : Label) : Nat :=
  match p.func? f with
  | some fn => funcStart p f + prologueSize fn + ((fn.blocks.map blockSize).take l).sum
  | none => 0

def blockInstrs (p : Prog P) (f : FuncId) (l : Label) : List (Machine.Lir.Instr P) :=
  ((p.block? f l).map (·.instrs)).getD []

def pointIdx (p : Prog P) (pt : Point) : Nat :=
  blockStart p pt.func pt.label + (((blockInstrs p pt.func pt.label).map instrSize).take pt.index).sum

/-- The index just after the `JAL` of the call at `pt`: the return address. -/
def retIdx (p : Prog P) (pt : Point) : Nat :=
  match p.fetch pt with
  | some (.instr (.call _ args _)) => pointIdx p pt + 15 + args.length
  | _ => 0

theorem pointIdx_zero (p : Prog P) (f : FuncId) (l : Label) :
    pointIdx p ⟨f, l, 0⟩ = blockStart p f l := by
  simp [pointIdx]

/-! ## Emission -/

section Emit

variable (reg : P → Reg) (N : Nat) (p : Prog P)

def emitInstr (pt : Point) : Machine.Lir.Instr P → List Ext.Instr
  | .op o => opCode reg o
  | .call g args results =>
    saveAll ++ loadLocs reg args ++ [jalI ra (pointIdx p pt + 14 + args.length) (funcStart p g)] ++
      restoreAll ++ storeLocs reg results
  | .fop .. => [.ebreak]

def emitTerm (pt : Point) : Term P → List Ext.Instr
  | .jump l => [jalI 0#5 (pointIdx p pt) (blockStart p pt.func l)]
  | .branch c l₁ l₂ =>
    [.branch .eq (reg c) 0#5 4#12, jalI 0#5 (pointIdx p pt + 1) (blockStart p pt.func l₁),
      jalI 0#5 (pointIdx p pt + 2) (blockStart p pt.func l₂)]
  | .ret locs =>
    loadLocs reg locs ++
      [ldI ra sp (raOff N), addiI sp sp (imm12 (frameSize N)), .jalr 0#5 ra 0#12]
  | .trap => [jalI 0#5 (pointIdx p pt) trapIdx]

def emitBlock (f l : Nat) (b : Block P) : List Ext.Instr :=
  (b.instrs.mapIdx fun i ins => emitInstr reg p ⟨f, l, i⟩ ins).flatten ++
    emitTerm reg N p ⟨f, l, b.instrs.length⟩ b.term

def prologue (g : FuncId) (fn : Func P) : List Ext.Instr :=
  [addiI sp sp (BitVec.ofInt 12 (-(frameSize N : Int))), .branch .geu sp s10 4#12,
    jalI 0#5 (funcStart p g + 2) overflowIdx, sdI sp ra (raOff N)] ++ storeLocs reg fn.params ++
    [jalI 0#5 (funcStart p g + 4 + fn.params.length) (blockStart p g fn.entry)]

def emitFunc (g : FuncId) (fn : Func P) : List Ext.Instr :=
  prologue reg N p g fn ++ (fn.blocks.mapIdx fun l b => emitBlock reg N p g l b).flatten

def emitProg : List Ext.Instr :=
  [.ebreak, .ebreak, .ebreak] ++ (p.funcs.mapIdx fun g fn => emitFunc reg N p g fn).flatten

end Emit

/-! ## Emitted sizes -/

section Sizes

variable (reg : P → Reg) (N : Nat) (p : Prog P)

theorem emitInstr_length (pt : Point) (ins : Machine.Lir.Instr P) :
    (emitInstr reg p pt ins).length = instrSize ins := by
  cases ins with
  | op o => exact opCode_length reg _ o
  | call g args results => simp [emitInstr, instrSize]; omega
  | fop => rfl

theorem emitTerm_length (pt : Point) (t : Term P) :
    (emitTerm reg N p pt t).length = termSize t := by
  cases t <;> simp [emitTerm, termSize]

theorem map_length_mapIdx {α β : Type} (xs : List α) (g : Nat → α → List β)
    (size : α → Nat) (hg : ∀ i x, (g i x).length = size x) :
    (xs.mapIdx g).map List.length = xs.map size := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [hg]

theorem flatten_mapIdx_take_length {α β : Type} (xs : List α) (g : Nat → α → List β)
    (size : α → Nat) (hg : ∀ i x, (g i x).length = size x) (i : Nat) :
    (((xs.mapIdx g).map List.length).take i).sum = ((xs.map size).take i).sum := by
  rw [map_length_mapIdx xs g size hg]

theorem flatten_mapIdx_length {α β : Type} (xs : List α) (g : Nat → α → List β)
    (size : α → Nat) (hg : ∀ i x, (g i x).length = size x) :
    (xs.mapIdx g).flatten.length = (xs.map size).sum := by
  rw [List.length_flatten, map_length_mapIdx xs g size hg]

theorem emitBlock_length (f l : Nat) (b : Block P) :
    (emitBlock reg N p f l b).length = blockSize b := by
  simp only [emitBlock, List.length_append, emitTerm_length, blockSize]
  rw [flatten_mapIdx_length _ _ instrSize (fun i x => emitInstr_length reg p _ x)]

theorem prologue_length (g : FuncId) (fn : Func P) :
    (prologue reg N p g fn).length = prologueSize fn := by
  simp [prologue, prologueSize]; omega

theorem emitFunc_length (g : FuncId) (fn : Func P) :
    (emitFunc reg N p g fn).length = funcSize fn := by
  simp only [emitFunc, List.length_append, prologue_length, funcSize]
  rw [flatten_mapIdx_length _ _ blockSize (fun i x => emitBlock_length reg N p g i x)]

end Sizes

/-! ## Finding emitted code -/

theorem flatten_drop {α : Type} (L : List (List α)) (i : Nat) (h : i < L.length) :
    L.flatten.drop ((L.map List.length).take i).sum = L[i] ++ (L.drop (i + 1)).flatten := by
  conv => lhs; rw [← List.take_append_drop i L]
  rw [List.flatten_append, List.drop_append_of_le_length (by simp [List.length_flatten, List.map_take])]
  rw [List.drop_eq_nil_of_le (by simp [List.length_flatten, List.map_take]), List.nil_append]
  rw [List.drop_eq_getElem_cons h, List.flatten_cons]

theorem flatten_mapIdx_drop {α β : Type} (xs : List α) (g : Nat → α → List β)
    (size : α → Nat) (hg : ∀ i x, (g i x).length = size x) (i : Nat) (h : i < xs.length) :
    ∃ rest, (xs.mapIdx g).flatten.drop ((xs.map size).take i).sum = g i xs[i] ++ rest := by
  rw [← flatten_mapIdx_take_length xs g size hg i, flatten_drop _ i (by simpa using h)]
  exact ⟨_, by rw [List.getElem_mapIdx]⟩

theorem flatten_mapIdx_drop_all {α β : Type} (xs : List α) (g : Nat → α → List β)
    (size : α → Nat) (hg : ∀ i x, (g i x).length = size x) :
    (xs.mapIdx g).flatten.drop (xs.map size).sum = [] := by
  rw [List.drop_eq_nil_of_le]
  rw [flatten_mapIdx_length xs g size hg]

theorem drop_of_drop {α : Type} {X Y rest : List α} {a b : Nat} (h : X.drop a = Y ++ rest)
    (hb : b ≤ Y.length) : X.drop (a + b) = Y.drop b ++ rest := by
  rw [← List.drop_drop, h, List.drop_append_of_le_length hb]

theorem sum_take_le (xs : List Nat) (i : Nat) : (xs.take i).sum ≤ xs.sum := by
  conv => rhs; rw [← List.take_append_drop i xs]
  rw [List.sum_append]; omega

theorem sum_take_add_le (xs : List Nat) {i : Nat} (h : i < xs.length) :
    (xs.take i).sum + xs[i] ≤ xs.sum := by
  conv => rhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons h]
  rw [List.sum_append, List.sum_cons]; omega

section CodeAt

variable (reg : P → Reg) (N : Nat) (p : Prog P)

theorem code_at_func {g : FuncId} {fn : Func P} (hfn : p.func? g = some fn) :
    ∃ rest, (emitProg reg N p).drop (funcStart p g) = emitFunc reg N p g fn ++ rest := by
  unfold Prog.func? at hfn
  obtain ⟨hg, rfl⟩ := List.getElem?_eq_some_iff.mp hfn
  obtain ⟨rest, h⟩ := flatten_mapIdx_drop p.funcs (fun g fn => emitFunc reg N p g fn) funcSize
    (fun i x => emitFunc_length reg N p i x) g hg
  refine ⟨rest, ?_⟩
  rw [funcStart, emitProg, ← List.drop_drop, List.drop_left' (by rfl)]
  exact h

theorem code_at_block {f l : Nat} {fn : Func P} {b : Block P} (hfn : p.func? f = some fn)
    (hb : fn.blocks[l]? = some b) :
    ∃ rest, (emitProg reg N p).drop (blockStart p f l) = emitBlock reg N p f l b ++ rest := by
  obtain ⟨r₁, h₁⟩ := code_at_func reg N p hfn
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨r₂, h₂⟩ := flatten_mapIdx_drop fn.blocks (fun l b => emitBlock reg N p f l b) blockSize
    (fun i x => emitBlock_length reg N p f i x) l hl
  have h₃ := drop_of_drop (b := prologueSize fn + ((fn.blocks.map blockSize).take l).sum) h₁
    (by
      rw [emitFunc_length, funcSize]
      have := sum_take_le (fn.blocks.map blockSize) l
      omega)
  refine ⟨r₂ ++ r₁, ?_⟩
  rw [blockStart, hfn]
  simp only
  rw [← Nat.add_assoc] at h₃
  rw [h₃, emitFunc, ← List.drop_drop, List.drop_left' (prologue_length reg N p f fn), h₂,
    List.append_assoc]

theorem prog_block {pt : Point} {c : Machine.Lir.Code P} (hf : p.fetch pt = some c) :
    ∃ fn b, p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b ∧
      p.block? pt.func pt.label = some b := by
  obtain ⟨b, hb, _⟩ := Prog.fetch_eq_some hf
  unfold Prog.block? at hb
  cases hfn : p.func? pt.func with
  | none => simp [hfn] at hb
  | some fn =>
    simp only [hfn, Option.bind_some] at hb
    exact ⟨fn, b, rfl, hb, by simp [Prog.block?, hfn, hb]⟩

theorem code_at_instr {pt : Point} {ins : Machine.Lir.Instr P}
    (hf : p.fetch pt = some (.instr ins)) :
    ∃ rest, (emitProg reg N p).drop (pointIdx p pt) = emitInstr reg p pt ins ++ rest := by
  obtain ⟨fn, b, hfn, hb, hblk⟩ := prog_block p hf
  obtain ⟨b', hb', hc⟩ := Prog.fetch_eq_some hf
  rw [hblk] at hb'; cases hb'
  rcases hc with ⟨i, hi, e⟩ | ⟨_, e⟩
  · cases e
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨r₁, h₁⟩ := code_at_block reg N p hfn hb
    obtain ⟨r₂, h₂⟩ := flatten_mapIdx_drop b.instrs (fun i ins => emitInstr reg p ⟨pt.func, pt.label, i⟩ ins)
      instrSize (fun i x => emitInstr_length reg p _ x) pt.index hlt
    have h₃ := drop_of_drop (b := ((b.instrs.map instrSize).take pt.index).sum) h₁
      (by
        rw [emitBlock_length, blockSize]
        have := sum_take_le (b.instrs.map instrSize) pt.index
        omega)
    refine ⟨r₂ ++ emitTerm reg N p ⟨pt.func, pt.label, b.instrs.length⟩ b.term ++ r₁, ?_⟩
    have hpi : pointIdx p pt = blockStart p pt.func pt.label + ((b.instrs.map instrSize).take pt.index).sum := by
      simp [pointIdx, blockInstrs, hblk]
    rw [hpi, h₃, emitBlock, List.drop_append_of_le_length (by
      rw [flatten_mapIdx_length _ _ instrSize (fun i x => emitInstr_length reg p _ x)]
      exact sum_take_le _ _), h₂]
    simp
  · cases e

theorem code_at_term {pt : Point} {t : Term P} (hf : p.fetch pt = some (.term t)) :
    ∃ rest, (emitProg reg N p).drop (pointIdx p pt) = emitTerm reg N p pt t ++ rest := by
  obtain ⟨fn, b, hfn, hb, hblk⟩ := prog_block p hf
  obtain ⟨b', hb', hc⟩ := Prog.fetch_eq_some hf
  rw [hblk] at hb'; cases hb'
  rcases hc with ⟨i, _, e⟩ | ⟨hlen, e⟩
  · cases e
  · cases e
    obtain ⟨r₁, h₁⟩ := code_at_block reg N p hfn hb
    have hsum : ((b.instrs.map instrSize).take pt.index).sum = (b.instrs.map instrSize).sum := by
      rw [List.take_of_length_le (by simp [hlen])]
    have h₃ := drop_of_drop (b := (b.instrs.map instrSize).sum) h₁
      (by rw [emitBlock_length, blockSize]; omega)
    refine ⟨r₁, ?_⟩
    have hpi : pointIdx p pt = blockStart p pt.func pt.label + (b.instrs.map instrSize).sum := by
      simp [pointIdx, blockInstrs, hblk, ← hsum]
    rw [hpi, h₃, emitBlock, List.drop_append_of_le_length (by
      rw [flatten_mapIdx_length _ _ instrSize (fun i x => emitInstr_length reg p _ x)]),
      flatten_mapIdx_drop_all _ _ instrSize (fun i x => emitInstr_length reg p _ x), List.nil_append,
      ← hlen]

theorem code_at_prologue {g : FuncId} {fn : Func P} (hfn : p.func? g = some fn) :
    ∃ rest, (emitProg reg N p).drop (funcStart p g) = prologue reg N p g fn ++ rest := by
  obtain ⟨r, h⟩ := code_at_func reg N p hfn
  exact ⟨_, by rw [h, emitFunc, List.append_assoc]⟩

theorem code_at_stubs : (emitProg reg N p).take 3 = [.ebreak, .ebreak, .ebreak] := by
  simp [emitProg]

theorem pointIdx_next {pt : Point} {ins : Machine.Lir.Instr P}
    (hf : p.fetch pt = some (.instr ins)) : pointIdx p pt.next = pointIdx p pt + instrSize ins := by
  obtain ⟨fn, b, hfn, hb, hblk⟩ := prog_block p hf
  obtain ⟨b', hb', hc⟩ := Prog.fetch_eq_some hf
  rw [hblk] at hb'; cases hb'
  rcases hc with ⟨i, hi, e⟩ | ⟨_, e⟩
  · cases e
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    simp only [pointIdx, blockInstrs, hblk, Option.map_some, Option.getD_some, Point.next]
    rw [List.take_add_one, List.sum_append]
    simp [Nat.add_assoc, hi]
  · cases e

end CodeAt

end Silmaril.RiscV.Backend
