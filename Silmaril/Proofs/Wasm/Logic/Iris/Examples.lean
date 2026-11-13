module

public import Silmaril.Wasm.Logic.Iris.Adequacy.Thms
public import Silmaril.Wasm.Logic.Iris.Examples.Defs

/-!
# Worked examples for the Iris logic of Wasm Core 3.0
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (leNat leNat_encodeLE)
open Silmaril.Wasm.Logic.IrisWasm
open _root_.Iris _root_.Iris.BI _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The little-endian bytes of an `i32`. -/
abbrev le32 (c : BitVec IntType.i32.width) : List UInt8 :=
  (Memory.encodeLE (IntType.i32.width / 8) (c.setWidth (8 * (IntType.i32.width / 8))).toNat).data.toList

theorem i32_load_store (c : BitVec 32) :
    (BitVec.ofNat (8 * (IntType.i32.width / 8)) (leNat (le32 c))).setWidth IntType.i32.width = c := by
  apply BitVec.eq_of_toNat_eq
  have hc : c.toNat < 4294967296 := c.isLt
  simp [le32, leNat_encodeLE, IntType.width, Nat.mod_eq_of_lt hc]

section Iris

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-- The postcondition of `storeLoad`. -/
abbrev storeLoadPost (f : Frame) (ma : Nat) (p : BitVec 64) (c : BitVec 32) : Res H → IProp GF :=
  fun r => iprop(⌜r.out = .normal [.i32 c]⌝ ∗ ownFrame f ∗
    ownBytes ma (effAddr p.toNat memarg0) (le32 c))

theorem storeLoad_load {x : MemIdx} {ma : Nat} {f : Frame} {p : BitVec 64} {c : BitVec 32}
    (hx : f.module.mems[x.toNat]? = some ma) :
    ownFrame f ∗ ownBytes ma (effAddr p.toNat memarg0) (le32 c) ⊢
      WP (IExpr.run (vals [] ++ (vals [addr64 p] ++ [.plain (.intLoad .i32 none x memarg0)])) :
        IExpr P host) {{ storeLoadPost f ma p c }} := by
  refine Entails.trans ?_ (wp_intLoad (P := P) (host := host) (a := .i64) (i := p) (t := .i32)
    (arg := memarg0) (pa := effAddr p.toNat memarg0) (bs := le32 c) (vs := []) (rest := []) hx rfl (by simp [IntType.width]))
  iintro ⟨Hf, Hb⟩
  iframe Hf Hb
  iintro !> ⟨Hf, Hb⟩
  simp only [List.nil_append, List.append_nil]
  iapply wp_vals
  iintro %s %f'
  dsimp only [storeLoadPost]
  iframe
  ipureintro
  simp [i32_load_store, Val.i32]

/-- **memory64**: a store followed by a load at an `i64` address returns the stored
value, and the four bytes hold its encoding. -/
theorem storeLoad_wp {x : MemIdx} {ma : Nat} {f : Frame} {p : BitVec 64} {c : BitVec 32}
    {bs : List UInt8} (hx : f.module.mems[x.toNat]? = some ma) (hbs : bs.length = 4) :
    ownFrame f ∗ ownBytes ma (effAddr p.toNat memarg0) bs ⊢
      WP (IExpr.run (storeLoad x p c) : IExpr P host) {{ storeLoadPost f ma p c }} := by
  refine Entails.trans ?_ (wp_intStore (P := P) (host := host) (a := .i64) (i := p) (t := .i32)
    (c := c) (arg := memarg0) (pa := effAddr p.toNat memarg0) (bs := bs) (vs := [])
    (rest := vals [addr64 p] ++ [.plain (.intLoad .i32 none x memarg0)]) hx rfl hbs)
  iintro ⟨Hf, Hb⟩
  iframe Hf Hb
  iintro !> Hc
  iapply storeLoad_load (p := p) (c := c) hx $$ Hc

/-! ## Multiple memories -/

/-- The postcondition of `twoMems`. -/
abbrev twoMemsPost (ma₁ ma₂ : Nat) (p : BitVec 64) (c₁ c₂ : BitVec 32) : Res H → IProp GF :=
  fun r => iprop(⌜r.out = .normal [.i32 c₁]⌝ ∗
    ownBytes ma₁ (effAddr p.toNat memarg0) (le32 c₁) ∗
    ownBytes ma₂ (effAddr p.toNat memarg0) (le32 c₂))

theorem twoMems_load {x₁ : MemIdx} {ma₁ ma₂ : Nat} {f : Frame} {p : BitVec 64}
    {c₁ c₂ : BitVec 32} (hx₁ : f.module.mems[x₁.toNat]? = some ma₁) :
    ownFrame f ∗ ownBytes ma₁ (effAddr p.toNat memarg0) (le32 c₁) ∗
      ownBytes ma₂ (effAddr p.toNat memarg0) (le32 c₂) ⊢
      WP (IExpr.run (vals [] ++ (vals [addr64 p] ++ [.plain (.intLoad .i32 none x₁ memarg0)])) :
        IExpr P host) {{ twoMemsPost ma₁ ma₂ p c₁ c₂ }} := by
  refine Entails.trans ?_ (wp_intLoad (P := P) (host := host) (a := .i64) (i := p) (t := .i32)
    (arg := memarg0) (pa := effAddr p.toNat memarg0) (bs := le32 c₁) (vs := []) (rest := []) hx₁
    rfl (by simp [IntType.width]))
  iintro ⟨Hf, Hb₁, Hb₂⟩
  iframe Hf Hb₁
  iintro !> ⟨-, Hb₁⟩
  simp only [List.nil_append, List.append_nil]
  iapply wp_vals
  iintro %s %f'
  dsimp only [twoMemsPost]
  iframe
  ipureintro
  simp [i32_load_store, Val.i32]

theorem twoMems_store₂ {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {f : Frame} {p : BitVec 64}
    {c₁ c₂ : BitVec 32} {bs₂ : List UInt8} (hx₁ : f.module.mems[x₁.toNat]? = some ma₁)
    (hx₂ : f.module.mems[x₂.toNat]? = some ma₂) (hbs₂ : bs₂.length = 4) :
    ownFrame f ∗ ownBytes ma₁ (effAddr p.toNat memarg0) (le32 c₁) ∗
      ownBytes ma₂ (effAddr p.toNat memarg0) bs₂ ⊢
      WP (IExpr.run (vals [] ++ (vals [addr64 p, .i32 c₂] ++
        (.plain (.intStore .i32 none x₂ memarg0) ::
          (vals [addr64 p] ++ [.plain (.intLoad .i32 none x₁ memarg0)])))) : IExpr P host)
        {{ twoMemsPost ma₁ ma₂ p c₁ c₂ }} := by
  refine Entails.trans ?_ (wp_intStore (P := P) (host := host) (a := .i64) (i := p) (t := .i32)
    (c := c₂) (arg := memarg0) (pa := effAddr p.toNat memarg0) (bs := bs₂) (vs := [])
    (rest := vals [addr64 p] ++ [.plain (.intLoad .i32 none x₁ memarg0)]) hx₂ rfl hbs₂)
  iintro ⟨Hf, Hb₁, Hb₂⟩
  iframe Hf Hb₂
  iintro !> ⟨Hf, Hb₂⟩
  iapply twoMems_load (c₁ := c₁) (c₂ := c₂) hx₁
  iframe

/-- **Multiple memories**: stores to two memories at the same address do not
interfere; the load from the first memory returns its own value. -/
theorem twoMems_wp {x₁ x₂ : MemIdx} {ma₁ ma₂ : Nat} {f : Frame} {p : BitVec 64}
    {c₁ c₂ : BitVec 32} {bs₁ bs₂ : List UInt8} (hx₁ : f.module.mems[x₁.toNat]? = some ma₁)
    (hx₂ : f.module.mems[x₂.toNat]? = some ma₂) (hbs₁ : bs₁.length = 4) (hbs₂ : bs₂.length = 4) :
    ownFrame f ∗ ownBytes ma₁ (effAddr p.toNat memarg0) bs₁ ∗
      ownBytes ma₂ (effAddr p.toNat memarg0) bs₂ ⊢
      WP (IExpr.run (twoMems x₁ x₂ p c₁ c₂) : IExpr P host) {{ twoMemsPost ma₁ ma₂ p c₁ c₂ }} := by
  refine Entails.trans ?_ (wp_intStore (P := P) (host := host) (a := .i64) (i := p) (t := .i32)
    (c := c₁) (arg := memarg0) (pa := effAddr p.toNat memarg0) (bs := bs₁) (vs := [])
    (rest := vals [addr64 p, .i32 c₂] ++ (.plain (.intStore .i32 none x₂ memarg0) ::
      (vals [addr64 p] ++ [.plain (.intLoad .i32 none x₁ memarg0)]))) hx₁ rfl hbs₁)
  iintro ⟨Hf, Hb₁, Hb₂⟩
  iframe Hf Hb₁
  iintro !> ⟨Hf, Hb₁⟩
  iapply twoMems_store₂ (c₁ := c₁) (c₂ := c₂) hx₁ hx₂ hbs₂
  iframe

/-! ## A global counter -/

/-- An `i32` value. -/
abbrev n32 (n : BitVec 32) : Val := .num ⟨.int .i32, n⟩

/-- The postcondition of `bump`: it falls through, and the global holds `n + 1`. -/
abbrev bumpPost (a : Nat) (n : BitVec 32) : Silmaril.Wasm.Logic.Core.Post H :=
  fun s f o => o = .normal [] ∧ cellOf s f (.global a) = some (.val (n32 (n + 1)))

theorem bump_set {x : GlobalIdx} {a : Nat} {f : Frame} {n : BitVec 32}
    (hx : f.module.globals[x.toNat]? = some a) :
    ownFrame f ∗ ownGlobal a (n32 n) ⊢
      WP (IExpr.run (vals ([] ++ [n32 (n + 1)]) ++ [.plain (.globalSet x)]) : IExpr P host)
        {{ r, ⌜bumpPost a n r.store r.frame r.out⌝ }} := by
  refine Entails.trans ?_ (wp_globalSet (P := P) (host := host) (vs := []) (v := n32 n)
    (w := n32 (n + 1)) (rest := []) hx)
  iintro ⟨Hf, Hg⟩
  iframe Hf Hg
  iintro !> Hc
  iapply wp_exit_cells (ps := [(.frame, .frame f), (.global a, .val (n32 (n + 1)))])
    (show Hoare.Exits (.normal []) (vals [] ++ []) from rfl)
  simp only [ownCells_two]
  iframe Hc
  iintro %s %f' %hc -
  ipureintro
  exact ⟨rfl, hc (.global a, .val (n32 (n + 1))) (by simp)⟩

theorem bump_add {x : GlobalIdx} {a : Nat} {f : Frame} {n : BitVec 32}
    (hx : f.module.globals[x.toNat]? = some a) :
    ownFrame f ∗ ownGlobal a (n32 n) ⊢
      WP (IExpr.run (vals ([] ++ [n32 n]) ++ [.plain (.intConst .i32 1),
        .plain (.intBinOp .i32 .add), .plain (.globalSet x)]) : IExpr P host)
        {{ r, ⌜bumpPost a n r.store r.frame r.out⌝ }} := by
  refine Entails.trans ?_ (wp_intBinOp (P := P) (host := host) (vs := []) (t := .i32) (x := (n : BitVec 32))
    (y := (1 : BitVec 32)) (z := (n + 1 : BitVec 32)) (op := .add) (rest := [.plain (.globalSet x)]) rfl)
  iintro Hc
  inext
  iapply bump_set hx $$ Hc

/-- **A global counter**: `bump` adds one to the global. -/
theorem bump_wp {x : GlobalIdx} {a : Nat} {f : Frame} {n : BitVec 32}
    (hx : f.module.globals[x.toNat]? = some a) :
    ownFrame f ∗ ownGlobal a (n32 n) ⊢
      WP (IExpr.run (bump x) : IExpr P host) {{ r, ⌜bumpPost a n r.store r.frame r.out⌝ }} := by
  refine Entails.trans ?_ (wp_globalGet (P := P) (host := host) (vs := []) (v := n32 n)
    (rest := [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .add), .plain (.globalSet x)]) hx)
  iintro ⟨Hf, Hg⟩
  iframe Hf Hg
  iintro !> Hc
  iapply bump_add hx $$ Hc

/-! ## GC arrays -/

theorem arrLen_len {a : Nat} {fvs : List FieldVal} (hl : fvs.length = 2) :
    ownArray a fvs ⊢
      WP (IExpr.run (vals ([] ++ [.ref (.array a)]) ++ [.plain .arrayLen]) : IExpr P host)
        {{ r, ⌜r.out = .normal [n32 2]⌝ }} := by
  refine Entails.trans ?_ (wp_arrayLen (P := P) (host := host) (us := []) (a := a)
    (n := fvs.length) (rest := []))
  simp only [ownArray, arrayCells, ownCells_cons]
  iintro ⟨Hl, -⟩
  iframe Hl
  iintro !> -
  simp only [List.nil_append, List.append_nil]
  iapply wp_vals
  iintro %s %f
  ipureintro
  simp [hl, Val.i32]

/-- **GC arrays**: `array.new_fixed` of two elements, then `array.len`, returns `2`. -/
theorem arrLen_wp {x : TypeIdx} {v : Val} {f : Frame} {d : DefType} {ft : CFieldType}
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hp : ∀ w ∈ [v, v], packable (fieldStorage ft) w) :
    ownFrame f ⊢ WP (IExpr.run (arrLen x v) : IExpr P host) {{ r, ⌜r.out = .normal [n32 2]⌝ }} := by
  refine Entails.trans ?_ (wp_arrayNewFixed (P := P) (host := host) (us := []) (vs := [v, v])
    (n := ⟨2, by decide⟩) (rest := [.plain .arrayLen]) hd he rfl hp)
  iintro Hf
  iframe Hf
  iintro !> %a - Ha
  iapply arrLen_len (by simp) $$ Ha

/-! ## Exceptions -/

/-- **Exceptions**: `throw` of a tag without parameters exits with an exception at a
fresh address. -/
theorem throw_wp {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {f : Frame}
    (hx : f.module.tags[x.toNat]? = some ta) (he : Expand ti.type (.func ts .nil))
    (hts : ts.length = 0) :
    ownFrame f ∗ pts (.tag ta) (.tag ti) ⊢
      WP (IExpr.run (throwCode x) : IExpr P host) {{ r, ⌜∃ a, r.out = .throw a⌝ }} := by
  refine Entails.trans ?_ (wp_throw (P := P) (host := host) (us := []) (vs := []) (rest := [])
    hx he hts.symm)
  iintro ⟨Hf, Ht⟩
  iframe Hf Ht
  iintro !> %a -
  iapply wp_throwing
  iintro %s %f'
  ipureintro
  exact ⟨a, rfl⟩

/-! ## `memory.grow` -/

theorem wp_aconst {a : AddrType} {b : BitVec a.intType.width} {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .normal [.num ⟨.int a.intType, b⟩]⟩) ⊢
      WP (IExpr.run (vals [] ++ aconst a b :: []) : IExpr P host) {{ Φ }} :=
  wp_vals (vs := [.num ⟨.int a.intType, b⟩])

/-- The two possible results of `memory.grow` on an `i64` memory. -/
abbrev growPost (sz : Nat) (o : Silmaril.Wasm.Logic.Core.Outcome) : Prop :=
  o = .normal [.num ⟨.int AddrType.i64.intType, BitVec.ofNat _ (sz / Memory.pageSize)⟩] ∨
    o = .normal [.num ⟨.int AddrType.i64.intType, BitVec.allOnes _⟩]

/-- **`memory.grow` on a memory64 memory**, in every profile: the result is the old
size in pages or `-1`, whichever the profile chooses. -/
theorem grow_wp {x : MemIdx} {ma : Nat} {t : MemoryType} {sz : Nat} {n : BitVec 64} {f : Frame}
    (hx : f.module.mems[x.toNat]? = some ma)
    (hprog : (growOk t sz n.toNat ∧ P.growMaySucceed .memory ma (sz / Memory.pageSize) n.toNat) ∨
      (P.growMayFail .memory ma (sz / Memory.pageSize) n.toNat ∨ ¬ growOk t sz n.toNat)) :
    ownFrame f ∗ ownMem ma t sz ⊢
      WP (IExpr.run (grow x n) : IExpr P host) {{ r, ⌜growPost sz r.out⌝ }} := by
  refine Entails.trans ?_ (wp_memoryGrow (P := P) (host := host) (a := .i64) (n := n) (vs := [])
    (rest := []) hx hprog)
  iintro ⟨Hf, Hm⟩
  iframe Hf Hm
  iintro !>
  isplit
  · iintro %_ - - -
    iapply wp_aconst
    iintro %s %f'
    ipureintro
    exact .inl rfl
  · iintro - -
    iapply wp_aconst
    iintro %s %f'
    ipureintro
    exact .inr rfl

end Iris

/-- **Exceptions, adequacy**: every run of `throw x` is safe and every exit is an
exception. -/
theorem throw_hwp {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} (hx : f.module.tags[x.toNat]? = some ta)
    (he : Expand ti.type (.func ts .nil)) (hts : ts.length = 0)
    (hcells : Cells [(.frame, .frame f), (.tag ta, .tag ti)] s f) :
    Hoare.HWP P host s f (throwCode x) (fun _ _ o => ∃ a, o = .throw a) := by
  refine wp_hwp (GF := WasmGF) _ (by simp) hcells ?_
  intro _
  rw [ownCells_two]
  iintro Hc
  iapply throw_wp (P := P) (host := host) hx he hts $$ Hc

/-- **`memory.grow`, adequacy**: every run is safe and returns the old size or `-1`. -/
theorem grow_hwp {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {t : MemoryType} {sz : Nat}
    {n : BitVec 64} (hx : f.module.mems[x.toNat]? = some ma)
    (hprog : (growOk t sz n.toNat ∧ P.growMaySucceed .memory ma (sz / Memory.pageSize) n.toNat) ∨
      (P.growMayFail .memory ma (sz / Memory.pageSize) n.toNat ∨ ¬ growOk t sz n.toNat))
    (hcells : Cells [(.frame, .frame f), (.mem ma, .mem t sz)] s f) :
    Hoare.HWP P host s f (grow x n) (fun _ _ o => growPost sz o) := by
  refine wp_hwp (GF := WasmGF) _ (by simp) hcells ?_
  intro _
  rw [ownCells_two]
  iintro Hc
  iapply grow_wp (P := P) (host := host) hx hprog $$ Hc

/-- **An Iris triple for `bump`**: owning the frame and the global. -/
theorem bump_itriple {x : GlobalIdx} {a : Nat} {f₀ : Frame} {n : BitVec 32}
    (hx : f₀.module.globals[x.toNat]? = some a) :
    ITriple WasmGF P host
      (fun s f => f = f₀ ∧ cellOf s f (.global a) = some (.val (n32 n)))
      (fun _ _ => [(.frame, .frame f₀), (.global a, .val (n32 n))]) (bump x) (bumpPost a n) := by
  intro s f ⟨hf, hg⟩
  refine ⟨by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp [cellOf, hf]
    · exact hg
  · intro _
    rw [ownCells_two]
    iintro Hc
    iapply bump_wp (P := P) (host := host) hx $$ Hc

/-- **The Silmaril triple for `bump`**, from the Iris one: every run from a store whose
global holds `n` is safe, and every exit falls through with the global holding
`n + 1`. -/
theorem bump_triple {x : GlobalIdx} {a : Nat} {f₀ : Frame} {n : BitVec 32}
    (hx : f₀.module.globals[x.toNat]? = some a) :
    Hoare.Triple P host (fun s f => f = f₀ ∧ cellOf s f (.global a) = some (.val (n32 n)))
      (bump x) (bumpPost a n) :=
  (bump_itriple hx).sound

/-- **memory64, adequacy**: every run of `storeLoad` from a store that holds the
frame and the four bytes is safe, and the one that terminates returns `c`. -/
theorem storeLoad_hwp {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {p : BitVec 64}
    {c : BitVec 32} {bs : List UInt8} (hx : f.module.mems[x.toNat]? = some ma)
    (hbs : bs.length = 4) (hcells : Cells (storeCells f ma (effAddr p.toNat memarg0) bs) s f) :
    Hoare.HWP P host s f (storeLoad x p c) (fun _ _ o => o = .normal [.i32 c]) := by
  refine wp_hwp (GF := WasmGF) (storeCells f ma (effAddr p.toNat memarg0) bs) ?_ hcells ?_
  · simpa using fst_storeCells_nodup f ma (effAddr p.toNat memarg0) bs
  · intro _
    simp only [storeCells, ownCells_cons]
    iintro Hc
    ihave H := storeLoad_wp (P := P) (host := host) (c := c) hx hbs $$ Hc
    iapply wp_mono ?_ $$ H
    intro r
    iintro ⟨%h, -⟩
    ipureintro
    exact h

end Silmaril.Wasm.Logic.IrisWasm.Examples
