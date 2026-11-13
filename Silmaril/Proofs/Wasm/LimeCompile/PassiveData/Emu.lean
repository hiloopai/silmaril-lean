module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveData.Exec

/-!
# The passive-data container: the emulation of `memory.init`

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation Silmaril.Wasm.LimeCompile.PassiveData

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The helper's frame on arguments `i`, `j`, `n`. -/
abbrev hframe (mod : ModuleInst) (i j n : BitVec 32) : Frame :=
  ⟨[some (I32 i), some (I32 j), some (I32 n)], mod⟩

/-- The value the bounds check leaves before its `if`. -/
def checkVal (i j n : BitVec 32) (pages L : Nat) : BitVec 32 :=
  intRelOp .i64 (.gt .unsigned) (i.setWidth 64 + n.setWidth 64)
      ((BitVec.ofNat 32 pages).setWidth 64 * (65536 : BitVec 64)) |||
    intRelOp .i64 (.gt .unsigned) (j.setWidth 64 + n.setWidth 64) (BitVec.ofNat 64 L)

/-- The bounds check up to `memory.size`: `i + n` in `i64`. -/
def check1 : List Instr := get64 0 ++ get64 2 ++ [.intBinOp .i64 .add]

/-- The bounds check after `memory.size`, up to the `or` of the two comparisons. -/
def check2 (L : Nat) : List Instr :=
  [.convert (.extend .unsigned), .intConst .i64 65536, .intBinOp .i64 .mul,
    .intRelOp .i64 (.gt .unsigned)] ++ get64 1 ++ get64 2 ++
  [.intBinOp .i64 .add, .intConst .i64 (BitVec.ofNat 64 L), .intRelOp .i64 (.gt .unsigned),
    .intBinOp .i32 .or]

/-- The trap of the bounds check. -/
abbrev ifTrap : Instr := .if_ .empty [.unreachable] []

theorem checkCode_split (L : Nat) (rest : List Admin) :
    expression (checkCode L) ++ rest = expression check1 ++
      (.plain (.memorySize (idx 0)) :: (expression (check2 L) ++ (.plain ifTrap :: rest))) := by
  simp [checkCode, check1, check2, expression, get64]

theorem check_run {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {ma : Nat} {mi : MemInst}
    {L : Nat} {rest : List Admin} (hm : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi))
    (ha : mi.type.address = .i32) :
    Steps P host ⟨t, hframe mod i j n, expression (checkCode L) ++ rest⟩
      ⟨t, hframe mod i j n, vals [I32 (checkVal i j n mi.pages L)] ++
        (.plain ifTrap :: rest)⟩ := by
  have s1 : Steps P host ⟨t, hframe mod i j n, vals [] ++ (expression check1 ++
        (.plain (.memorySize (idx 0)) :: (expression (check2 L) ++ (.plain ifTrap :: rest))))⟩
      ⟨t, hframe mod i j n, vals [I64 (i.setWidth 64 + n.setWidth 64)] ++
        (.plain (.memorySize (idx 0)) :: (expression (check2 L) ++ (.plain ifTrap :: rest)))⟩ :=
    sexec_sound check1 [] [I64 (i.setWidth 64 + n.setWidth 64)] _ rfl
  have s2 : Steps P host ⟨t, hframe mod i j n, vals [I64 (i.setWidth 64 + n.setWidth 64)] ++
        (.plain (.memorySize (idx 0)) :: (expression (check2 L) ++ (.plain ifTrap :: rest)))⟩
      ⟨t, hframe mod i j n, vals [I64 (i.setWidth 64 + n.setWidth 64),
        I32 (BitVec.ofNat 32 mi.pages)] ++ (expression (check2 L) ++ (.plain ifTrap :: rest))⟩ :=
    r_memorySize hm ha
  have s3 : Steps P host ⟨t, hframe mod i j n, vals [I64 (i.setWidth 64 + n.setWidth 64),
        I32 (BitVec.ofNat 32 mi.pages)] ++ (expression (check2 L) ++ (.plain ifTrap :: rest))⟩
      ⟨t, hframe mod i j n, vals [I32 (checkVal i j n mi.pages L)] ++
        (.plain ifTrap :: rest)⟩ :=
    sexec_sound (check2 L) [I32 (BitVec.ofNat 32 mi.pages), I64 (i.setWidth 64 + n.setWidth 64)]
      [I32 (checkVal i j n mi.pages L)] _ rfl
  rw [checkCode_split]
  exact s1.trans (s2.trans s3)

theorem checkVal_eq_zero {i j n : BitVec 32} {pages L : Nat} (hp : pages ≤ 65536)
    (hL : L < 2 ^ 64) :
    checkVal i j n pages L = 0 ↔ i.toNat + n.toNat ≤ pages * 65536 ∧ j.toNat + n.toNat ≤ L := by
  have hi := i.isLt
  have hj := j.isLt
  have hn := n.isLt
  have h1 : (i.setWidth 64 + n.setWidth 64).toNat = i.toNat + n.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : (j.setWidth 64 + n.setWidth 64).toNat = j.toNat + n.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h3 : ((BitVec.ofNat 32 pages).setWidth 64 * (65536 : BitVec 64)).toNat = pages * 65536 := by
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := pages) (by omega), Nat.mod_eq_of_lt (a := pages) (by omega)]
    have h65 : (65536 : BitVec 64).toNat = 65536 := rfl
    rw [h65, Nat.mod_eq_of_lt (by omega)]
  have h4 : (BitVec.ofNat 64 L).toNat = L := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL]
  unfold checkVal
  simp only [intRelOp, bool32, gt_iff_lt, decide_eq_true_eq, IntType.width]
  rw [h1, h2, h3, h4]
  by_cases ha : pages * 65536 < i.toNat + n.toNat <;> by_cases hb : L < j.toNat + n.toNat
  · simp only [ha, hb, ↓reduceIte]; constructor <;> intro h <;> first | omega | exact absurd h (by decide)
  · simp only [ha, hb, ↓reduceIte]; constructor <;> intro h <;> first | omega | exact absurd h (by decide)
  · simp only [ha, hb, ↓reduceIte]; constructor <;> intro h <;> first | omega | exact absurd h (by decide)
  · simp only [ha, hb, ↓reduceIte]; constructor <;> intro h <;> first | omega | decide

/-- The bounds check passes (leaves nothing) when its value is 0. -/
theorem check_pass {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {ma : Nat} {mi : MemInst}
    {L : Nat} {rest : List Admin} (hm : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi))
    (ha : mi.type.address = .i32) (hc : checkVal i j n mi.pages L = 0) :
    Steps P host ⟨t, hframe mod i j n, expression (checkCode L) ++ rest⟩
      ⟨t, hframe mod i j n, rest⟩ := by
  have s1 := check_run (P := P) (host := host) (L := L) (rest := rest) hm ha
  rw [hc] at s1
  have s2 := r_ifFalse (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest) (bt := .empty) (b₁ := [.unreachable]) (b₂ := [])
  have s3 := r_block (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest) (body := [])
  have s4 := r_labelVals (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (us := []) (rest := rest) (n := 0) (cont := [])
  simp only [List.nil_append] at s2
  simp only [expression, List.map_nil] at s3
  simp only [vals, List.map_nil, List.nil_append, List.append_nil] at s1 s2 s3 s4 ⊢
  exact s1.trans (s2.trans (s3.trans s4))

/-- The bounds check traps when its value is not 0. -/
theorem check_fail {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {ma : Nat} {mi : MemInst}
    {L : Nat} {rest : List Admin} (hm : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi))
    (ha : mi.type.address = .i32) (hc : checkVal i j n mi.pages L ≠ 0) :
    Steps P host ⟨t, hframe mod i j n, expression (checkCode L) ++ rest⟩
      ⟨t, hframe mod i j n, [.trap]⟩ := by
  have s1 := check_run (P := P) (host := host) (L := L) (rest := rest) hm ha
  have s2 := r_ifTrue (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest) (bt := .empty) (b₁ := [.unreachable]) (b₂ := []) hc
  have s3 := r_block (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest) (body := [.unreachable])
  have s4 : Steps P host ⟨t, hframe mod i j n, vals [] ++
      (.label 0 [] (expression [.unreachable]) :: rest)⟩
      ⟨t, hframe mod i j n, vals [] ++ (.label 0 [] [.trap] :: rest)⟩ :=
    r_label (Step.parametric .unreachable).steps
  have s5 := r_trapLabel (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest) (n := 0) (cont := [])
  have s6 := r_trap (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := rest)
  simp only [List.nil_append] at s1 s2
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))

/-- The copy with `n = 0` does nothing. -/
theorem copy_zero {t : Store H} {mod : ModuleInst} {i j : BitVec 32} {bs : List UInt8} {h : Nat} :
    Steps P host ⟨t, hframe mod i j 0, expression (copyCode bs h)⟩ ⟨t, hframe mod i j 0, []⟩ := by
  have s1 := r_localGet (P := P) (host := host) (t := t) (F := hframe mod i j 0) (vs := [])
    (rest := [.plain (.if_ .empty (stepCode bs h) [])]) (x := idx 2) (v := I32 0) rfl
  have s2 := r_ifFalse (P := P) (host := host) (t := t) (F := hframe mod i j 0) (vs := [])
    (rest := []) (bt := .empty) (b₁ := stepCode bs h) (b₂ := [])
  have s3 := r_block (P := P) (host := host) (t := t) (F := hframe mod i j 0) (vs := [])
    (rest := []) (body := [])
  have s4 := r_labelVals (P := P) (host := host) (t := t) (F := hframe mod i j 0) (vs := [])
    (us := []) (rest := []) (n := 0) (cont := [])
  simp only [List.nil_append] at s1 s2
  simp only [expression, List.map_nil] at s3
  simp only [vals, List.map_nil, List.nil_append, List.append_nil, List.map_cons] at s1 s2 s3 s4 ⊢
  exact s1.trans (s2.trans (s3.trans s4))

/-- The copy with `n ≠ 0` enters the step block. -/
theorem copy_enter {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {bs : List UInt8} {h : Nat}
    (hn : n ≠ 0) :
    Steps P host ⟨t, hframe mod i j n, expression (copyCode bs h)⟩
      ⟨t, hframe mod i j n, [.label 0 [] (expression (stepCode bs h))]⟩ := by
  have s1 := r_localGet (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := [.plain (.if_ .empty (stepCode bs h) [])]) (x := idx 2) (v := I32 n) rfl
  have s2 := r_ifTrue (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := []) (bt := .empty) (b₁ := stepCode bs h) (b₂ := []) hn
  have s3 := r_block (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := []) (body := stepCode bs h)
  simp only [List.nil_append] at s1 s2
  simp only [vals, List.map_nil, List.nil_append, List.map_cons] at s1 s2 s3 ⊢
  exact s1.trans (s2.trans s3)

/-- **One byte of the emulation**: look up `b[j]`, store it at `i`, and prepare the recursive
call on `i + 1`, `j + 1`, `n - 1`. -/
theorem step_run {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {bs : List UInt8} {h : Nat}
    {ma : Nat} {mi : MemInst} {byte : UInt8} {b : ByteArray}
    (hm : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi)) (hbs : bs.length ≤ 2 ^ 32)
    (hbyte : bs[j.toNat]? = some byte)
    (hst : Memory.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
      ((BitVec.ofNat 32 byte.toNat).setWidth _) = some b) :
    Steps P host ⟨t, hframe mod i j n, expression (stepCode bs h)⟩
      ⟨t.setMem ma { mi with bytes := b }, hframe mod i j n,
        vals [I32 (i + 1), I32 (j + 1), I32 (n - 1)] ++ [.plain (.call (idx h))]⟩ := by
  have hj : (hframe mod i j n).local? (idx 1) = some (some (I32 j)) := rfl
  have e1 : sexec (hframe mod i j n) [] ([.localGet (idx 0), .intConst .i32 0] ++ chain bs 0) =
      some [I32 (BitVec.ofNat 32 byte.toNat), I32 i] := by
    have := sexec_chain hj bs 0 0 [I32 i] []
    rw [List.append_nil] at this
    rw [chainVal_get bs 0 0 (Nat.zero_le _) (by omega) (by simpa using hbyte)] at this
    exact this
  have s1 := sexec_sound (P := P) (host := host) (t := t) _ _ _
    (.plain store8I :: expression [.localGet (idx 0), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 1), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 2), .intConst .i32 1, .intBinOp .i32 .sub, .call (idx h)]) e1
  have s2 := r_store8 (P := P) (host := host) (t := t) (F := hframe mod i j n) (vs := [])
    (rest := expression [.localGet (idx 0), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 1), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 2), .intConst .i32 1, .intBinOp .i32 .sub, .call (idx h)]) hm hst
  have e3 : sexec (hframe mod i j n) [] [.localGet (idx 0), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 1), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 2), .intConst .i32 1, .intBinOp .i32 .sub] =
      some [I32 (n - 1), I32 (j + 1), I32 (i + 1)] := rfl
  have s3 := sexec_sound (P := P) (host := host) (t := t.setMem ma { mi with bytes := b }) _ _ _
    [.plain (.call (idx h))] e3
  have hc : expression (stepCode bs h) = vals ([] : List Val).reverse ++
      (expression ([.localGet (idx 0), .intConst .i32 0] ++ chain bs 0) ++
      (.plain store8I :: expression [.localGet (idx 0), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 1), .intConst .i32 1, .intBinOp .i32 .add,
      .localGet (idx 2), .intConst .i32 1, .intBinOp .i32 .sub, .call (idx h)])) := by
    simp [stepCode, expression, vals]
  rw [hc]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    vals, List.map_nil, List.map_cons, expression] at s1 s2 s3 ⊢
  exact s1.trans (s2.trans s3)

/-- A memory instance as validation guarantees it for Lime1: 32-bit addresses, whole pages, at
most `2 ^ 32` bytes. -/
def MemOk (mi : MemInst) : Prop :=
  mi.type.address = .i32 ∧ mi.bytes.size % 65536 = 0 ∧ mi.bytes.size ≤ 2 ^ 32

theorem MemOk.pages {mi : MemInst} (h : MemOk mi) :
    mi.pages * 65536 = mi.bytes.size ∧ mi.pages ≤ 65536 := by
  obtain ⟨-, h1, h2⟩ := h
  simp only [MemInst.pages, Memory.pageSize]
  omega

/-- The function at address `a` of `t` is the helper for the bytes `bs`, calling itself at index
`h`, in a module instance whose memory 0 is at address `ma`. -/
def HelperAt (t : Store H) (a h ma : Nat) (bs : List UInt8) : Prop :=
  ∃ (fi : FuncInst H) (code : Func) (ps rs : Ty (.list .val)),
    t.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧ ps.length = 3 ∧ rs.length = 0 ∧
    fi.code = .wasm code ∧ code.locals = [] ∧ code.body = helperBody bs h ∧
    fi.module.funcs[(idx h : FuncIdx).toNat]? = some a ∧
    fi.module.mems[(idx 0 : MemIdx).toNat]? = some ma

/-- Calling the helper: a frame of the helper's module around the helper's body. -/
theorem helper_enter {t : Store H} {g : Frame} {a h ma : Nat} {bs : List UInt8}
    (hH : HelperAt t a h ma bs) (hg : g.module.funcs[(idx h : FuncIdx).toNat]? = some a)
    (i j n : BitVec 32) :
    ∃ mod : ModuleInst, mod.funcs[(idx h : FuncIdx).toNat]? = some a ∧
      mod.mems[(idx 0 : MemIdx).toNat]? = some ma ∧
      Steps P host ⟨t, g, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx h))]⟩
        ⟨t, g, [.frame 0 (hframe mod i j n) [.label 0 [] (expression (helperBody bs h))]]⟩ := by
  obtain ⟨fi, code, ps, rs, hf, he, hps, hrs, hcode, hloc, hbody, hmf, hmm⟩ := hH
  refine ⟨fi.module, hmf, hmm, ?_⟩
  have s := r_call (P := P) (host := host) (t := t) (F := g) (vs := []) (rest := [])
    (args := [I32 i, I32 j, I32 n]) hg hf he (by simp [hps]) hcode
  rw [hrs, hloc, hbody] at s
  simpa [Frame.forCall, vals] using s

/-- The helper's body splits into the bounds check and the copy. -/
theorem helperBody_expr (bs : List UInt8) (h : Nat) :
    expression (helperBody bs h) = expression (checkCode bs.length) ++ expression (copyCode bs h) := by
  simp [helperBody, expression]

theorem mem_of_frame {t : Store H} {mod : ModuleInst} {i j n : BitVec 32} {ma : Nat} {mi : MemInst}
    (hmm : mod.mems[(idx 0 : MemIdx).toNat]? = some ma) (ht : t.mems[ma]? = some mi) :
    t.mem? (hframe mod i j n) (idx 0) = some (ma, mi) := by
  simp [Store.mem?, hmm, ht]

/-- **The emulation of a successful `memory.init`.** If the source's `memory.init 0 y` on `i`, `j`,
`n` succeeds with store `s'` (`memoryInitLoop`), then calling the helper of `y` on the same
arguments, from a target store with the same memories, returns with the memories of `s'` and
everything else unchanged. -/
theorem emu_ok {y : DataIdx} {da ma a h : Nat} {di : DataInst} {bs : List UInt8}
    (hbs : bs.length ≤ 2 ^ 32) (hdi : di.bytes.data.toList = bs) :
    ∀ (n : BitVec 32) {s s' t : Store H} {f g : Frame} {i j : BitVec 32},
      memoryInitLoop s f (idx 0) y .i32 i j n = some s' →
      s.data? f y = some (da, di) →
      f.module.mems[(idx 0 : MemIdx).toNat]? = some ma →
      (∀ mi, s.mems[ma]? = some mi → MemOk mi) →
      t.mems = s.mems → HelperAt t a h ma bs →
      g.module.funcs[(idx h : FuncIdx).toNat]? = some a →
      Steps P host ⟨t, g, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx h))]⟩
        ⟨{ t with mems := s'.mems }, g, []⟩ := by
  intro n
  induction hk : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' t f g i j hl hd hfm hmo htm hH hg
  obtain ⟨mod, hmodf, hmodm, hent⟩ := helper_enter (P := P) (host := host) hH hg i j n
  replace hl := (memoryInitLoop.eq_1 s f (idx 0) y .i32 i j n).symm.trans hl
  split at hl
  · rename_i ma' mi da' di' hm hd'
    have hsm : s.mems[ma]? = some mi ∧ ma = ma' := by
      rcases hx : s.mems[ma]? with _ | mi0
      · simp [Store.mem?, hfm, hx] at hm
      · simp [Store.mem?, hfm, hx] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact ⟨rfl, rfl⟩
    obtain ⟨hsm, rfl⟩ := hsm
    rw [hd] at hd'
    cases hd'
    have htmem : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi) :=
      mem_of_frame hmodm (by rw [htm]; exact hsm)
    have hmi := hmo mi hsm
    obtain ⟨hpg, hple⟩ := hmi.pages
    have hlen : di.bytes.size = bs.length := by
      rw [← hdi]; simp
    split at hl
    · rename_i hb
      have hb' : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size := hb
      have hc0 : checkVal i j n mi.pages bs.length = 0 :=
        (checkVal_eq_zero hple (by omega)).mpr ⟨by omega, by omega⟩
      have hchk := check_pass (P := P) (host := host) (L := bs.length)
        (rest := expression (copyCode bs h)) htmem hmi.1 hc0
      split at hl
      · rename_i hn
        subst hn
        cases hl
        have hin : Steps P host ⟨t, hframe mod i j 0, expression (helperBody bs h)⟩
            ⟨t, hframe mod i j 0, []⟩ := by
          rw [helperBody_expr]
          exact hchk.trans copy_zero
        have hfr := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
          (r_label (vs := []) (rest := []) (n := 0) (cont := []) hin)
        have hl1 := r_labelVals (P := P) (host := host) (t := t) (F := hframe mod i j 0) (vs := [])
          (us := []) (rest := []) (n := 0) (cont := [])
        have hfr2 := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
          hl1
        have hf0 := r_frameNil (P := P) (host := host) (t := t) (F := g)
          (Fi := hframe mod i j 0) (vs := []) (rest := [])
        have ht : ({ t with mems := s.mems } : Store H) = t := by rw [← htm]
        rw [ht]
        simp only [vals, List.map_nil, List.nil_append, List.append_nil] at hent hfr hfr2 hf0 ⊢
        exact hent.trans (hfr.trans (hfr2.trans hf0))
      · rename_i hn
        split at hl
        · rename_i byte hbyte
          split at hl
          · rename_i b hst
            have hbyte' : bs[j.toNat]? = some byte := by
              rw [← hdi]; simpa using hbyte
            have hstep := step_run (P := P) (host := host) (t := t) (h := h) htmem hbs hbyte' hst
            have hlt : (n - 1).toNat < k := hk ▸ bv32_sub_one_lt hn
            have hmo' : ∀ mi', (s.setMem ma { mi with bytes := b }).mems[ma]? = some mi' →
                MemOk mi' := by
              intro mi' hmi'
              have hlt' : ma < s.mems.length := by
                by_contra hc
                rw [List.getElem?_eq_none (by omega)] at hsm
                cases hsm
              simp only [Store.setMem, List.getElem?_set_self hlt', Option.some.injEq] at hmi'
              subst hmi'
              refine ⟨hmi.1, ?_, ?_⟩
              · rw [Memory.store_size hst]; exact hmi.2.1
              · rw [Memory.store_size hst]; exact hmi.2.2
            have hrec := ih _ hlt (n - 1) rfl (s := s.setMem ma { mi with bytes := b }) (s' := s')
              (t := t.setMem ma { mi with bytes := b }) (f := f) (g := hframe mod i j n)
              (i := i + 1) (j := j + 1) hl hd hfm hmo' (by simp [Store.setMem, htm]) hH hmodf
            have hin : Steps P host ⟨t, hframe mod i j n, expression (helperBody bs h)⟩
                ⟨{ t with mems := s'.mems }, hframe mod i j n, []⟩ := by
              rw [helperBody_expr]
              refine hchk.trans ((copy_enter hn).trans ?_)
              have h1 := r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0)
                (cont := []) hstep
              have h2 := r_label (P := P) (host := host) (vs := []) (rest := []) (n := 0)
                (cont := []) hrec
              have h3 := r_labelVals (P := P) (host := host)
                (t := { t with mems := s'.mems }) (F := hframe mod i j n) (vs := [])
                (us := []) (rest := []) (n := 0) (cont := [])
              simp only [vals, List.map_nil, List.nil_append, List.append_nil] at h1 h2 h3 ⊢
              exact h1.trans (h2.trans h3)
            have hfr := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
              (r_label (vs := []) (rest := []) (n := 0) (cont := []) hin)
            have hl1 := r_labelVals (P := P) (host := host) (t := { t with mems := s'.mems })
              (F := hframe mod i j n) (vs := []) (us := []) (rest := []) (n := 0) (cont := [])
            have hfr2 := r_frame (P := P) (host := host) (F := g) (vs := []) (rest := []) (n := 0)
              hl1
            have hf0 := r_frameNil (P := P) (host := host) (t := { t with mems := s'.mems }) (F := g)
              (Fi := hframe mod i j n) (vs := []) (rest := [])
            simp only [vals, List.map_nil, List.nil_append, List.append_nil] at hent hfr hfr2 hf0 ⊢
            exact hent.trans (hfr.trans (hfr2.trans hf0))
          · cases hl
        · cases hl
    · cases hl
  · cases hl

theorem mem?_inv {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) :
    f.module.mems[x.toNat]? = some ma ∧ s.mems[ma]? = some mi := by
  rcases hx : f.module.mems[x.toNat]? with _ | ma'
  · simp [Store.mem?, hx] at hm
  · rcases hy : s.mems[ma']? with _ | mi0
    · simp [Store.mem?, hx, hy] at hm
    · have he : (ma', mi0) = (ma, mi) := by simpa [Store.mem?, hx, hy] using hm
      have hma : ma' = ma := congrArg Prod.fst he
      have hmi : mi0 = mi := congrArg Prod.snd he
      exact ⟨hma ▸ rfl, hma ▸ hmi ▸ hy⟩

theorem setMem_mem? {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (mi' : MemInst) :
    (s.setMem ma mi').mem? f x = some (ma, mi') := by
  have hinv := mem?_inv hm
  have hlt : ma < s.mems.length := by
    by_contra hc
    have hnone : s.mems[ma]? = none := List.getElem?_eq_none (by omega)
    rw [hnone] at hinv
    exact absurd hinv.2 (by simp)
  simp [Store.mem?, hinv.1, Store.setMem, List.getElem?_set_self hlt]

/-- A frame of the helper around a trapping body traps. -/
theorem frame_trap {t : Store H} {g F : Frame} {body : List Admin}
    (h : Steps P host ⟨t, F, body⟩ ⟨t, F, [.trap]⟩) :
    Steps P host ⟨t, g, [.frame 0 F [.label 0 [] body]]⟩ ⟨t, g, [.trap]⟩ := by
  have s1 : Steps P host ⟨t, g, vals [] ++ (.frame 0 F [.label 0 [] body] :: [])⟩
      ⟨t, g, vals [] ++ (.frame 0 F [.label 0 [] [.trap]] :: [])⟩ :=
    r_frame (P := P) (host := host) (r_label (vs := []) (rest := []) h)
  have s2 : Steps P host ⟨t, F, vals [] ++ (.label 0 [] [.trap] :: [])⟩
      ⟨t, F, vals [] ++ (.trap :: [])⟩ := r_trapLabel
  have s3 : Steps P host ⟨t, g, vals [] ++ (.frame 0 F [.label 0 [] [.trap]] :: [])⟩
      ⟨t, g, vals [] ++ (.frame 0 F [.trap] :: [])⟩ := r_frame s2
  have s4 : Steps P host ⟨t, g, vals [] ++ (.frame 0 F [.trap] :: [])⟩
      ⟨t, g, vals [] ++ (.trap :: [])⟩ := r_trapFrame
  exact s1.trans (s3.trans s4)

theorem checkVal_ne_zero {i j n : BitVec 32} {mi : MemInst} {L : Nat} (hmi : MemOk mi)
    (hL : L ≤ 2 ^ 32) (hb : ¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ L)) :
    checkVal i j n mi.pages L ≠ 0 := by
  have hpg := hmi.pages
  intro h0
  have hz := (checkVal_eq_zero hpg.2 (by omega)).mp h0
  exact hb ⟨by omega, by omega⟩

/-- **The emulation of a trapping `memory.init`.** If the source's bounds fail (`memory.init-oob`,
one step to a trap on an unchanged store), calling the helper traps on an unchanged store. -/
theorem emu_trap {ma a h : Nat} {di : DataInst} {mi : MemInst}
    {bs : List UInt8} {s t : Store H} {f g : Frame} {i j n : BitVec 32}
    (hbs : bs.length ≤ 2 ^ 32) (hdi : di.bytes.data.toList = bs)
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi)
    (hb : ¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size))
    (htm : t.mems = s.mems) (hH : HelperAt t a h ma bs)
    (hg : g.module.funcs[(idx h : FuncIdx).toNat]? = some a) :
    Steps P host ⟨t, g, vals [I32 i, I32 j, I32 n] ++ [.plain (.call (idx h))]⟩ ⟨t, g, [.trap]⟩ := by
  obtain ⟨mod, -, hmodm, hent⟩ := helper_enter (P := P) (host := host) hH hg i j n
  have hsm : s.mems[ma]? = some mi := (mem?_inv hm).2
  have htmem : t.mem? (hframe mod i j n) (idx 0) = some (ma, mi) :=
    mem_of_frame hmodm (htm ▸ hsm)
  have hlen : di.bytes.size = bs.length := by rw [← hdi]; simp
  have hc : checkVal i j n mi.pages bs.length ≠ 0 := checkVal_ne_zero hmi hbs (hlen ▸ hb)
  have hin : Steps P host ⟨t, hframe mod i j n, expression (helperBody bs h)⟩
      ⟨t, hframe mod i j n, [.trap]⟩ :=
    helperBody_expr bs h ▸ check_fail htmem hmi.1 hc
  exact hent.trans (frame_trap hin)

theorem store1_some {bytes : ByteArray} {a : Nat} (w : BitVec (8 * (PackSize.i8.width / 8)))
    (h : a + 1 ≤ bytes.size) : ∃ b, Memory.store bytes a w = some b := by
  have hsz : (Memory.encodeLE (PackSize.i8.width / 8) w.toNat).size = 1 := rfl
  have hle : a + (Memory.encodeLE (PackSize.i8.width / 8) w.toNat).size ≤ bytes.size := by
    rw [hsz]; exact h
  refine ⟨(Memory.encodeLE (PackSize.i8.width / 8) w.toNat).copySlice 0 bytes a
    (Memory.encodeLE (PackSize.i8.width / 8) w.toNat).size, ?_⟩
  simp only [Memory.store, Memory.writeBytes, hle, ↓reduceIte]

theorem memoryInitLoop_zero {y : DataIdx} {ma da : Nat} {di : DataInst} {s : Store H}
    {f : Frame} {i j : BitVec 32} {mi : MemInst} (hm : s.mem? f (idx 0) = some (ma, mi))
    (hd : s.data? f y = some (da, di)) (hbi : i.toNat ≤ mi.bytes.size)
    (hbj : j.toNat ≤ di.bytes.size) :
    memoryInitLoop s f (idx 0) y .i32 i j 0 = some s := by
  have hbi' : i.toNat + (0 : BitVec 32).toNat ≤ mi.bytes.size := by simpa using hbi
  have hbj' : j.toNat + (0 : BitVec 32).toNat ≤ di.bytes.size := by simpa using hbj
  rw [memoryInitLoop.eq_1 s f (idx 0) y .i32 i j 0, hm, hd]
  simp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hbi', hbj'⟩)]
  rfl

theorem memoryInitLoop_succ {y : DataIdx} {ma da : Nat} {di : DataInst} {s : Store H}
    {f : Frame} {i j n : BitVec 32} {mi : MemInst} {byte : UInt8} {b : ByteArray}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (hbi : i.toNat + n.toNat ≤ mi.bytes.size) (hbj : j.toNat + n.toNat ≤ di.bytes.size)
    (hn : n ≠ 0) (hbyte : di.bytes.data[j.toNat]? = some byte)
    (hst : Memory.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
      ((BitVec.ofNat 32 byte.toNat).setWidth _) = some b) :
    memoryInitLoop s f (idx 0) y .i32 i j n =
      memoryInitLoop (s.setMem ma { mi with bytes := b }) f (idx 0) y .i32 (i + 1 : BitVec 32)
        (j + 1) (n - 1) := by
  rw [memoryInitLoop.eq_1 s f (idx 0) y .i32 i j n, hm, hd]
  simp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hbi, hbj⟩), dite_eq_right_of_eq_false (eq_false hn),
    hbyte]
  simp only
  split
  · rename_i b' hb'
    have hbb : b' = b := Option.some.inj (hb'.symm.trans hst)
    exact hbb ▸ rfl
  · rename_i hb'
    exact absurd (hb'.symm.trans hst) (by simp)

theorem effAddr_memarg0 (a : Nat) : effAddr a memarg0 = a := by
  simp [effAddr, memarg0]

theorem bv_add_one_toNat_le (i : BitVec 32) : (i + 1).toNat ≤ i.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem bv_sub_one_toNat {n : BitVec 32} (hn : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have hn0 : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- In bounds, the source's `memory.init` succeeds: `memoryInitLoop` is defined. -/
theorem memoryInitLoop_some {y : DataIdx} {ma da : Nat} {di : DataInst} :
    ∀ (n : BitVec 32) {s : Store H} {f : Frame} {i j : BitVec 32} {mi : MemInst},
      s.mem? f (idx 0) = some (ma, mi) → s.data? f y = some (da, di) →
      i.toNat + n.toNat ≤ mi.bytes.size → j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s', memoryInitLoop s f (idx 0) y .i32 i j n = some s' := by
  intro n
  induction hk : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s f i j mi hm hd hbi hbj
  by_cases hn : n = 0
  · have hn' : n.toNat = 0 := by rw [hn]; rfl
    exact ⟨s, hn ▸ memoryInitLoop_zero hm hd (by omega) (by omega)⟩
  · show ∃ s', memoryInitLoop s f (idx 0) y .i32 i j n = some s'
    have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hds : di.bytes.size = di.bytes.data.size := rfl
    have hjl : j.toNat < di.bytes.data.size := by omega
    obtain ⟨b, hst⟩ := store1_some (bytes := mi.bytes) (a := effAddr i.toNat memarg0)
      ((BitVec.ofNat 32 (di.bytes.data[j.toNat]'hjl).toNat).setWidth _)
      (by rw [effAddr_memarg0]; omega)
    have hb := Memory.store_size hst
    have hsub := bv_sub_one_toNat hn
    have hi1 := bv_add_one_toNat_le i
    have hj1 := bv_add_one_toNat_le j
    obtain ⟨s', hs'⟩ := ih _ (hk ▸ bv32_sub_one_lt hn) (n - 1) rfl (i := i + 1) (j := j + 1)
      (setMem_mem? hm { mi with bytes := b }) hd
      (by show (i + 1).toNat + (n - 1).toNat ≤ b.size; omega)
      (by show (j + 1).toNat + (n - 1).toNat ≤ di.bytes.size; omega)
    have hbi' : i.toNat + n.toNat ≤ mi.bytes.size := by omega
    have hbj' : j.toNat + n.toNat ≤ di.bytes.size := by omega
    exact ⟨s', (memoryInitLoop_succ hm hd hbi' hbj' hn (Array.getElem?_eq_getElem hjl) hst).trans hs'⟩

end Silmaril.Proofs.Wasm.LimeCompile.PassiveData
