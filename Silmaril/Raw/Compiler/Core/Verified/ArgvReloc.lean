module

public import Silmaril.Compiler.Core.Source.StartupArgsMem.Defs
public import Silmaril.Compiler.Core.Verified.ArgBlock.Defs
public import Silmaril.Compiler.Core.Verified.Locals.Defs

/-! # The startup objects of `main(argc, argv)` relocated onto `Spec.argBlock`

The Core startup (`Startup.objects`, created by `startObjects`) and the loader's argument block
(`Spec.argBlock`) lay out the same data differently: Core allocates the strings first, each below
the previous one, then the `argv` array, the `argc` object and the `argv` parameter object; the
block puts the pointer array first and the strings after it in increasing order. No single shift
relates them (by the layout check), so the relation is indexed by allocation: `argvReloc`
sends string `i` to `strAddr base args i` and the array to `base`, and a Core pointer
`.allocated id a` relocates to `t + (a - b)` when allocation `id`, based at `b`, sits at `t`
(`relocPtr`).

`startup_reloc` proves that for every `ArgsOk` argument vector the startup objects exist, and that
in every later memory that keeps them (`Keeps`), loads through relocated pointers agree with the
block: `char` loads in the strings read the block's bytes, `char *` loads in the array read
pointers that relocate to the block's words, the `argc` object holds `argc`, and the `argv`
parameter object holds the array's pointer, which relocates to `base` (`ArgvAgree`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvReloc

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.StartupArgs
open Silmaril.Compile.Core.Spec
open Silmaril.Compile.Core.Verified.ArgBlock
open Mem.Concrete (Tags Pointer MemoryValue loadTyped)

/-- An allocation-indexed relocation: `ρ id = some (b, t)` puts the Core allocation `id`, based at
`b`, at linear address `t`. -/
abbrev Reloc := Int → Option (Int × Int)

/-- The linear address of a Core pointer under a relocation (null is address 0). -/
def relocPtr (ρ : Reloc) : Pointer → Option Int
  | .null _ => some 0
  | .allocated id a => (ρ id).map fun bt => bt.2 + (a - bt.1)
  | _ => none

/-- Relocation commutes with offsets within an allocation (Core's `array_shift` is address
arithmetic on the relocated address). -/
theorem relocPtr_shift (ρ : Reloc) (id a k : Int) :
    relocPtr ρ (.allocated id (a + k)) = (relocPtr ρ (.allocated id a)).map (· + k) := by
  simp only [relocPtr, Option.map_map]
  congr 1
  funext bt
  simp only [Function.comp]
  ring

/-- The relocation of the `argv` startup objects: string `i` (identifier `id0 + i`, the pointer
`qs[i]`) to `strAddr base args i`, the array (identifier `id0 + argc`, at `B`) to `base`. -/
def argvReloc (id0 B : Int) (qs : List Pointer) (base : Nat) (args : List String) : Reloc := fun id =>
  if id = id0 + args.length then some (B, base)
  else if id0 ≤ id then
    match qs[(id - id0).toNat]? with
    | some (.allocated _ b) => some (b, strAddr base args (id - id0).toNat)
    | _ => none
  else none

/-- Loads through relocated pointers agree with the argument block at `base`: the strings `qs`,
the array at `pa`, the `argc` object at `pc` and the `argv` parameter object at `pv`. -/
structure ArgvAgree (tags : Tags) (ρ : Reloc) (m : Mem.Concrete.State) (base : Nat)
    (args : List String) (qs : List Pointer) (pa pc pv : Pointer) : Prop where
  /-- Character `j ≤ length` of string `i` (the terminator last) is the block's byte there. -/
  chars : ∀ (i j : Nat) (hi : i < args.length), j ≤ args[i].length →
    ∃ id b, qs[i]? = some (.allocated id b) ∧
      relocPtr ρ (.allocated id (b + j)) = some (strAddr base args i + j : Nat) ∧
      ∃ (x : UInt8) (m' : Mem.Concrete.State), (argBlock base args)[strAddr base args i + j - base]? = some x ∧
        loadTyped tags m Startup.charType (.allocated id (b + j)) = .ok (.integer .char x.toNat, m')
  /-- Slot `i ≤ argc` of the array holds a pointer that relocates to the block's word there. -/
  slots : ∀ i : Nat, i ≤ args.length →
    ∃ id B, pa = .allocated id B ∧ relocPtr ρ (.allocated id (B + 8 * i)) = some (base + 8 * i : Nat) ∧
      ∃ (p : Pointer) (w : Nat) (m' : Mem.Concrete.State), relocPtr ρ p = some w ∧
        ((argBlock base args).drop (8 * i)).take 8 = le8 w ∧
        loadTyped tags m Startup.charPointer (.allocated id (B + 8 * i)) =
          .ok (.pointer Startup.charType p, m')
  /-- The `argc` object holds `argc`. -/
  argc : ∃ m', loadTyped tags m Startup.intType pc = .ok (.integer (.signed .int) args.length, m')
  /-- The argc object has the compiler local invariant, including intact integer bytes. -/
  argcSlot : ∃ id addr, pc = .allocated id addr ∧ Locals.Slot m id addr args.length
  /-- The `argv` parameter object holds the array's pointer, which relocates to `base`. -/
  argv : relocPtr ρ pa = some base ∧
    ∃ m', loadTyped tags m Startup.argvType pv = .ok (.pointer Startup.charPointer pa, m')

theorem chars_of_argsOk {args : List String} (h : ArgsOk args) : ∀ s ∈ args, Chars s := h.2.1

theorem strRoom_eq (args : List String) :
    strRoom args = ((args.map fun s => s.length + 1).sum : Nat) := rfl

/-- The room the startup objects need, from the bound on the block. -/
theorem room_of_argsOk {args : List String} (h : ArgsOk args) :
    strRoom args + 8 * (args.length + 1) ≤ 4096 := by
  have hl := length_argBlock 0 args (ascii_of_argsOk h)
  have hb := h.2.2
  simp only [minArgSize] at hb
  rw [strAddr, List.take_length] at hl
  simp only [strRoom_eq]
  omega

theorem toNat_toUInt8 {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem le_strAddr (base : Nat) (args : List String) (i : Nat) : base ≤ strAddr base args i := by
  simp [strAddr]; omega

/-- **The startup objects relocate onto the argument block.** For every `ArgsOk` argument vector
and every block base, `startObjects` creates the startup objects of `main(argc, argv)` from the
fresh memory, and in every later memory that keeps them, loads through `argvReloc` agree with
`argBlock base args`. -/
theorem startup_reloc (tags : Tags) (enums : Map Sym IntegerType) (args : List String)
    (h : ArgsOk args) (loc : Loc) (main argc argv : Sym) (base : Nat) :
    ∃ objs qs B pc pv m1, Startup.objects args false loc main argc argv = .ok objs ∧
      startObjects tags {enumTypes := enums} objs [] = .ok (qs ++ [.allocated args.length B, pc, pv], m1) ∧
      m1.dead = [] ∧ 281474976710655 - 4096 - 32 ≤ m1.lastAddress ∧ m1.stdout = "" ∧
      ∀ tags' m', Keeps m1 m' →
        ArgvAgree tags' (argvReloc 0 B qs base args) m' base args qs (.allocated args.length B) pc pv := by
  have hc := chars_of_argsOk h
  have ha := ascii_of_argsOk h
  have hroom := room_of_argsOk h
  have hr0 : 0 ≤ strRoom args := Int.natCast_nonneg _
  let m0 : Mem.Concrete.State := {enumTypes := enums}
  obtain ⟨qs, B, C, V, m1, hs, g, hn, hd, hpos, hptrs, harr, hint, hptr, hB0, hBtop, hlV, hVC, hCB⟩ :=
    startObjects_args tags args hc (by omega) loc main argc argv m0 rfl (by simp [m0]) (by
      simp [m0]; omega)
  have hn0 : m0.nextId = 0 := rfl
  simp only [hn0, Int.zero_add] at hs hn harr hint hptr hptrs
  refine ⟨_, qs, B, _, _, m1, objects_ok' args hc loc main argc argv, hs, hd, by change (281474976710655 : Int) - _ - _ - _ ≤ _ at hpos; omega, by simpa [m0] using g.stdout,
    fun tags' m' k => ?_⟩
  set ρ := argvReloc 0 B qs base args with hρ
  have hlen : qs.length = args.length := hptrs.1
  have hρa : ρ args.length = some (B, (base : Int)) := by simp [hρ, argvReloc]
  have hρs : ∀ i b, i < args.length → qs[i]? = some (.allocated i b) →
      ρ i = some (b, (strAddr base args i : Int)) := by
    intro i b hi hq
    have hne : (i : Int) ≠ args.length := by omega
    simp [hρ, argvReloc, hne, hq]
  have hlast : m1.lastAddress ≤ B := by omega
  refine ⟨fun i j hi hj => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · -- characters
    obtain ⟨b, hq, hstr, hlb, hbtop, hbpos⟩ := hptrs.2 i args[i] (List.getElem?_eq_getElem hi)
    simp only [Int.zero_add] at hq hstr
    have hstr' := hstr.keeps k (by rw [hn]; omega) hlb
    refine ⟨i, b, hq, by simp [relocPtr, hρs i b hi hq], ?_⟩
    rw [show strAddr base args i + j - base = strAddr base args i - base + j by
      have := le_strAddr base args i; omega]
    rcases Nat.lt_or_ge j args[i].length with hj' | hj'
    · have hjl : j < args[i].toList.length := by rw [String.length_toList]; exact hj'
      have hcj : args[i].toList[j]? = some (args[i].toList[j]'hjl) := List.getElem?_eq_getElem hjl
      obtain ⟨h1, h2, -⟩ := hc _ (List.getElem_mem hi) _ (args[i].toList.getElem_mem hjl)
      obtain ⟨m'', hl⟩ := load_char tags' m' hstr'.live (a := b + j) (by omega) (by omega)
        (hstr'.chars j _ hcj) (by omega) (by omega)
      refine ⟨_, m'', argBlock_char base args ha hi hj', ?_⟩
      rw [toNat_toUInt8 (by omega)]
      exact hl
    · obtain rfl : j = args[i].length := by omega
      obtain ⟨m'', hl⟩ := load_char tags' m' hstr'.live (a := b + args[i].length) (by omega) (by omega)
        hstr'.nul le_rfl (by norm_num)
      exact ⟨0, m'', argBlock_nul base args ha hi, by simpa using hl⟩
  · -- slots
    have harr' := harr.keeps k (by rw [hn]; omega) hlast
    refine ⟨args.length, B, rfl, by simp [relocPtr, hρa], ?_⟩
    rcases Nat.lt_or_ge i args.length with hi' | hi'
    · obtain ⟨b, hq, hstr, hlb, hbtop, hbpos⟩ := hptrs.2 i args[i] (List.getElem?_eq_getElem hi')
      simp only [Int.zero_add] at hq hstr
      obtain ⟨hf, hp⟩ := harr'.slot i i b hq
      obtain ⟨m'', hl⟩ := load_pointer tags' m' harr'.live ⟨false, false, false⟩ Startup.charType
        (a := B + 8 * i) (by omega) (by rw [hlen]; omega) hf (by omega) (by omega)
        (abstractPointer_allocated m' (Or.inl rfl) (by omega) hp)
      refine ⟨_, strAddr base args i, m'', by simp [relocPtr, hρs i b hi' hq], argBlock_slot base args ha hi',
        hl⟩
    · obtain rfl : i = args.length := by omega
      have hf := harr'.null
      rw [hlen] at hf
      obtain ⟨m'', hl⟩ := load_pointer tags' m' harr'.live ⟨false, false, false⟩ Startup.charType
        (a := B + 8 * args.length) (by omega) (by rw [hlen]; omega) hf le_rfl (by norm_num)
        (abstractPointer_null m' _ _)
      exact ⟨_, 0, m'', by simp [relocPtr], argBlock_slot_null base args ha, hl⟩
  · -- argc
    have hint' := hint.keeps k (by rw [hn]; omega) (by omega)
    exact load_int tags' m' hint'.live le_rfl le_rfl hint'.bytes (by omega) (by
      have : (args.length : Int) * 8 < 4096 := by omega
      omega)
  · -- argc as an integer slot
    have hint' := hint.keeps k (by rw [hn]; omega) (by omega)
    obtain ⟨a, ha, hb, hz, hat⟩ := hint'.live.lookup
    exact ⟨_, _, rfl, ⟨hint'.live.alive, a, ha, hb, hz, hat, hint'.readonly a ha⟩,
      hint'.plain, hint'.bytes⟩
  · -- argv
    have hptr' := hptr.keeps k (by rw [hn]; omega) (by omega)
    refine ⟨by simp [relocPtr, hρa], ?_⟩
    exact load_pointer tags' m' hptr'.live ⟨false, false, false⟩ Startup.charPointer le_rfl le_rfl
      hptr'.bytes (by omega) (by omega) (abstractPointer_allocated m' (Or.inr rfl) (by omega) hptr'.prov)

/-- **`main(argc, argv)` starts on the relocated argument block.** From the initial state of a file
without global definitions whose `main` takes `argc` and `argv` (normal calling convention), for
every `ArgsOk` argument vector, the dynamics reaches `main`'s body with `argc` and `argv` bound to
pointers to the `argc` object and the `argv` parameter object, in a memory whose later memories
that keep it agree with `argBlock base args` through `argvReloc`, for every block base. -/
theorem initial_reaches_body_reloc (file : Program) (enums : Map Sym IntegerType) (args : List String)
    (h : ArgsOk args) {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {argc argv : Sym}
    {tc tv : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body))
    (normal : file.callingConvention = .normal) (base : Nat) :
    ∃ s labels xs qs B pc pv m, initial file enums args = .ok (s, labels) ∧
      StartupReach.Reaches file labels s ⟨.effectExpr body
        (extendEnv ([argc, argv].zip (paramValues (qs ++ [.allocated args.length B, pc, pv]))) ∅),
        [.annotations xs], m⟩ ∧
      m.stdout = "" ∧ ∀ tags m', Keeps m m' →
        ArgvAgree tags (argvReloc 0 B qs base args) m' base args qs (.allocated args.length B) pc pv := by
  obtain ⟨objs, qs, B, pc, pv, m1, hobjs, hstart, hd, hlast, hout, hagree⟩ :=
    startup_reloc file.tagDefs enums args h loc sym argc argv base
  obtain ⟨hb1, -⟩ := nextBase_ge m1 4 4 (by norm_num)
  obtain ⟨pe, m2, herrno, g⟩ := createErrno_spec ⟨file.tagDefs, m1.enumTypes⟩ m1 hd (by omega)
  obtain ⟨s, labels, xs, hinit, hreach⟩ := initial_reaches_body_args file enums args nodefs main decl normal
    hobjs hstart herrno
  refine ⟨s, labels, xs, qs, B, pc, pv, _, hinit, hreach, by simpa using g.stdout.trans hout, fun tags m' k => hagree tags m' ?_⟩
  exact Grows.keeps_trans (m2 := m2) g ⟨k.allocs, k.dead, k.bytes⟩

end Silmaril.Compile.Core.Verified.ArgvReloc
