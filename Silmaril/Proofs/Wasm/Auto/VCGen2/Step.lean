module

public import Silmaril.Proofs.Wasm.Auto.VCGen2.Basic
public import Silmaril.Wasm.Auto.VCGen.Thms
public import Silmaril.Wasm.Logic.Instr.Thms

/-!
# The VC generator with SSA names and memory: the relation and straight-line instructions

`Rel`: the concrete configurations a symbolic state denotes in an environment `ρ` (the store is
the entry store with memory `0` replaced by the current memory variable, the frame's locals and
the stack are the symbolic ones, the path condition holds, the state is fresh). `step1_sound`:
a straight-line instruction run from a related configuration continues, in every run, with a
configuration related to the generator's next state in an environment that agrees with `ρ` below
`σ.nv` (it extends `ρ` at the fresh variable of a `local.set`/`local.tee` or a store).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen2

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen2
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec1 popInt popV localVal?)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Corr)
open Silmaril.Wasm.Auto.VCGen (binW relW relB unW litT unT binT relP relV eqzV nz32 iteT wrapW
  extSW extUW popInt_num intUnOp_eq_unT intTestOp_eq_eqzV intRelOp_eq_relV litT_toNat)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {c : Corr}

/-! ## Environments -/

theorem eqBelow_setV (ρ : Env) (t : IntType) (n : Nat) (x : BitVec t.width) :
    EqBelow n ρ (ρ.setV t n x) := by
  intro i hi
  have : i ≠ n := by omega
  cases t <;> simp [Env.setV, this]

theorem eqBelow_setM (ρ : Env) (n : Nat) (B : ByteArray) : EqBelow n ρ (ρ.setM n B) := by
  intro i hi
  have : i ≠ n := by omega
  simp [Env.setM, this]

theorem setV_get (ρ : Env) (t : IntType) (n : Nat) (x : BitVec t.width) :
    (ρ.setV t n x).get t n = x := by
  cases t <;> simp [Env.setV, Env.get]

theorem setV_mem (ρ : Env) (t : IntType) (n : Nat) (x : BitVec t.width) :
    (ρ.setV t n x).mem = ρ.mem := by
  cases t <;> rfl

theorem agree_of_eqBelow {ps : List IntType} {n : Nat} {ρ ρ' : Env} (h : EqBelow n ρ ρ')
    (hn : ps.length < n) : Agree ps ρ ρ' := by
  refine ⟨fun i t hi => EqBelow.get h ?_ t, (h 0 (by omega)).2.2⟩
  have := (List.getElem?_eq_some_iff.mp hi).1
  omega

/-! ## Stores -/

/-- Memory `0` of `m` in `s`. -/
theorem setM_some {s : Store H} {m : ModuleInst} {ma : Nat} {mi : MemInst}
    (hm : m.mems[0]? = some ma) (hs : s.mems[ma]? = some mi) (B : ByteArray) :
    setM s m B = s.setMem ma { mi with bytes := B } := by
  simp [setM, hm, hs]

theorem mems_setMem {s : Store H} {ma : Nat} {mi mi' : MemInst} (hs : s.mems[ma]? = some mi) :
    (s.setMem ma mi').mems[ma]? = some mi' := by
  have := (List.getElem?_eq_some_iff.mp hs).1
  simp [Store.setMem, this]

theorem setMem_setMem (s : Store H) (ma : Nat) (mi mi' : MemInst) :
    (s.setMem ma mi).setMem ma mi' = s.setMem ma mi' := by
  simp [Store.setMem, List.set_set]

theorem setMem_self {s : Store H} {ma : Nat} {mi : MemInst} (hs : s.mems[ma]? = some mi) :
    s.setMem ma mi = s := by
  have h := (List.getElem?_eq_some_iff.mp hs)
  cases s
  simp only [Store.setMem, Store.mk.injEq, and_true, true_and]
  rw [← h.2]
  exact List.set_getElem_self h.1

theorem rd_of_load {B : ByteArray} {a n : Nat} (h : a + n ≤ B.size) :
    Memory.load B a n = some (rd B a n) := by
  simp [rd, Memory.load, Memory.readBytes, h]

theorem store_some {B : ByteArray} {a n : Nat} (w : BitVec (8 * n)) (h : a + n ≤ B.size) :
    ∃ B', Memory.store B a w = some B' := by
  simp [Memory.store, Memory.writeBytes, Memory.encodeLE_size, h]

theorem ldT_eq (t : IntType) (n : Nat) (sx : Signedness) (B : ByteArray) (a : Nat) :
    ldT t n sx B a = match sx with
      | .unsigned => (rd B a n).setWidth t.width
      | .signed => (rd B a n).signExtend t.width := by
  cases t <;> cases sx <;> rfl

theorem stT_eq (t : IntType) (n : Nat) (B : ByteArray) (a : Nat) (x : BitVec t.width) :
    stT t n B a x = (Memory.store B a (x.setWidth (8 * n))).getD B := by
  cases t <;> rfl

/-! ## The relation -/


variable {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

theorem fresh_iff (σ : SSt) : σ.fresh = true ↔ (∀ v ∈ σ.locals, v.vlt σ.nv = true) ∧
    (∀ v ∈ σ.stack, v.vlt σ.nv = true) ∧ (∀ φ ∈ σ.pc, φ.vlt σ.nv = true) ∧
    σ.mem < σ.nv := by
  simp [SSt.fresh, List.all_eq_true, and_assoc]

/-- The memory of a related configuration (if the function uses memory). -/
theorem Rel.mem? {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : S.mem = true) {x : MemIdx} (hx : x.toNat = 0) :
    ∃ ma mi, s.mem? f x = some (ma, mi) ∧ mi.bytes = ρ.mem σ.mem ∧
      ∀ B, s.setMem ma { mi with bytes := B } = upd S s₀ m B := by
  have hok := hR.memOk
  simp only [MemOk, hmem, ↓reduceIte] at hok
  obtain ⟨ma, mi₀, hm, hs, -⟩ := hok
  have hst := hR.store
  simp only [upd, hmem, ↓reduceIte, setM_some hm hs] at hst
  refine ⟨ma, { mi₀ with bytes := ρ.mem σ.mem }, ?_, rfl, fun B => ?_⟩
  · simp [Store.mem?, hx, hR.modl, hm, hst, mems_setMem hs]
  · simp [upd, hmem, setM_some hm hs, hst, setMem_setMem]

/-- A state with a new stack below `next`. -/
theorem Rel.withStack {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) {st : List SV}
    (hst : ∀ v ∈ st, v.vlt σ.nv = true) :
    Rel F S lt ρ₀ s₀ m ρ { σ with stack := st } s f (dens F ρ st) := by
  obtain ⟨hl, -, hp, hm⟩ := (fresh_iff σ).mp hR.fresh
  exact { hR with stack := rfl, fresh := (fresh_iff _).mpr ⟨hl, hst, hp, hm⟩ }

/-! ## Straight-line instructions -/

section Instr

variable {i : Instr} {σ σ' : SSt} {side : List Fm} {ρ : Env} {s : Store H} {f : Frame}
  {rs : List Val} {rest : List Admin} {Q : Post H}

/-- An instruction that `exec1` evaluates to a new stack below `next`, with the store, frame and
environment unchanged. -/
theorem pure_step {st : List SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (he : exec1 s f rs i = some (s, f, dens F ρ st)) (hst : ∀ v ∈ st, v.vlt σ.nv = true)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv { σ with stack := st } rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: rest) Q :=
  Silmaril.Wasm.Examples.Common.Wp.exec1 (m := c) he
    (hk ρ s f (Rel.withStack hR hst) (EqBelow.refl _ _))

theorem stack_vlt (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) : ∀ v ∈ σ.stack, v.vlt σ.nv = true :=
  ((fresh_iff σ).mp hR.fresh).2.1

theorem pop1_vlt {t : IntType} {st : List SV} {a : Tm t} (hp : pop1 t σ.stack = some (a, st))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    a.vlt σ.nv = true ∧ ∀ v ∈ st, v.vlt σ.nv = true := by
  have h := stack_vlt hR
  rw [pop1_eq hp] at h
  refine ⟨?_, fun v hv => h v (List.mem_cons_of_mem _ hv)⟩
  have := h _ List.mem_cons_self
  rwa [SV.vlt_of] at this

theorem pop2_vlt {t t' : IntType} {b : Tm t} {a : Tm t'} {st st' : List SV}
    (hp : pop1 t σ.stack = some (b, st)) (hp' : pop1 t' st = some (a, st'))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    σ.stack = SV.of t b :: SV.of t' a :: st' ∧ b.vlt σ.nv = true ∧ a.vlt σ.nv = true ∧
      ∀ w ∈ st', w.vlt σ.nv = true := by
  have hst' : σ.stack = SV.of t b :: SV.of t' a :: st' := by rw [pop1_eq hp, pop1_eq hp']
  have hall : ∀ w ∈ SV.of t b :: SV.of t' a :: st', w.vlt σ.nv = true := hst' ▸ stack_vlt hR
  refine ⟨hst', by simpa [SV.vlt_of] using hall _ List.mem_cons_self,
    by simpa [SV.vlt_of] using hall _ (List.mem_cons_of_mem _ List.mem_cons_self),
    fun w hw => hall w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))⟩

theorem dens_pop1 {t : IntType} {st : List SV} {a : Tm t} (hp : pop1 t σ.stack = some (a, st))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    rs = .num ⟨.int t, a.den F ρ ρ⟩ :: dens F ρ st := by
  rw [hR.stack, pop1_eq hp, dens, List.map_cons, SV.den_of]

theorem cons_vlt {v : SV} {st : List SV} {n : Nat} (hv : v.vlt n = true)
    (hst : ∀ w ∈ st, w.vlt n = true) : ∀ w ∈ v :: st, w.vlt n = true := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hv
  · exact hst w hw

theorem sound_intUnOp {t : IntType} {op : IntUnOp}
    (h : step1 S.mem (.intUnOp t op) σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intUnOp t op) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 t σ.stack = some (a, st) ∧
      { σ with stack := SV.of t (.un op a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  obtain ⟨ha, hst⟩ := pop1_vlt hp hR
  refine pure_step hR ?_ (cons_vlt (by simpa [SV.vlt_of, Tm.vlt] using ha) hst) hk
  simp [exec1, dens_pop1 hp hR, popInt_num, SV.den_of, Tm.den, intUnOp_eq_unT]

theorem sound_intBinOp {t : IntType} {op : IntBinOp}
    (h : step1 S.mem (.intBinOp t op) σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hs : ∀ φ ∈ side, φ.den F ρ ρ) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intBinOp t op) :: rest) Q := by
  obtain ⟨b, st, a, st', hp, hp', rfl, rfl⟩ : ∃ b st a st', pop1 t σ.stack = some (b, st) ∧
      pop1 t st = some (a, st') ∧ { σ with stack := SV.of t (.bin op a b) :: st' } = σ' ∧
      safeF t op a b = side := by
    simp only [step1] at h
    rcases hp : pop1 t σ.stack with _ | ⟨b, st⟩ <;> simp only [hp, reduceCtorEq] at h
    rcases hp' : pop1 t st with _ | ⟨a, st'⟩ <;>
      simp only [hp', Option.map_none, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at h
    exact ⟨b, st, a, st', rfl, hp', h⟩
  obtain ⟨hst', hb, ha, hst⟩ := pop2_vlt hp hp' hR
  refine pure_step hR ?_ (cons_vlt (by simp [SV.vlt_of, Tm.vlt, ha, hb]) hst) hk
  rw [hR.stack, hst']
  simp [exec1, popInt_num, SV.den_of, Tm.den, intBinOp_of_safe hs]

theorem sound_intTestOp {t : IntType} {op : IntTestOp}
    (h : step1 S.mem (.intTestOp t op) σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intTestOp t op) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 t σ.stack = some (a, st) ∧
      { σ with stack := .i32 (.eqz a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  obtain ⟨ha, hst⟩ := pop1_vlt hp hR
  refine pure_step hR ?_ (cons_vlt (by simpa [SV.vlt, Tm.vlt] using ha) hst) hk
  simp [exec1, dens_pop1 hp hR, popInt_num, SV.den, Tm.den, Val.i32, intTestOp_eq_eqzV]

theorem sound_intRelOp {t : IntType} {op : IntRelOp}
    (h : step1 S.mem (.intRelOp t op) σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intRelOp t op) :: rest) Q := by
  obtain ⟨b, st, a, st', hp, hp', rfl, rfl⟩ : ∃ b st a st', pop1 t σ.stack = some (b, st) ∧
      pop1 t st = some (a, st') ∧ { σ with stack := .i32 (.rel op a b) :: st' } = σ' ∧
      [] = side := by
    simp only [step1] at h
    rcases hp : pop1 t σ.stack with _ | ⟨b, st⟩ <;> simp only [hp, reduceCtorEq] at h
    rcases hp' : pop1 t st with _ | ⟨a, st'⟩ <;>
      simp only [hp', Option.map_none, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at h
    exact ⟨b, st, a, st', rfl, hp', h⟩
  obtain ⟨hst', hb, ha, hst⟩ := pop2_vlt hp hp' hR
  refine pure_step hR ?_ (cons_vlt (by simp [SV.vlt, Tm.vlt, ha, hb]) hst) hk
  rw [hR.stack, hst']
  simp only [dens, List.map_cons, SV.den_of]
  simp [exec1, popInt_num, SV.den, Tm.den, Val.i32, intRelOp_eq_relV]

/-- **`i32.wrap_i64`** in either reading of the logic. -/
theorem wpWrap {s : Store H} {f : Frame} {vs : List Val} {x : BitVec 64} {rest : List Admin}
    {Q : Post H} (h : Wp c P host s f (vals (vs ++ [.num ⟨.int .i32, x.setWidth 32⟩]) ++ rest) Q) :
    Wp c P host s f (vals (vs ++ [.num ⟨.int .i64, x⟩]) ++ .plain (.convert .wrap) :: rest) Q := by
  refine Silmaril.Wasm.Logic.Hoare.Wp.convert (op := .wrap) (x := x) (fun z hz => ?_) (fun e he => ?_)
  · have h' := (Silmaril.Wasm.Auto.VCGen.convertP_wrap (P := P) _).1 hz
    injection h' with h''
    subst h''
    exact h
  · have h' := (Silmaril.Wasm.Auto.VCGen.convertP_wrap (P := P) _).1 he
    cases h'

/-- **`i64.extend_i32_s`/`i64.extend_i32_u`** in either reading of the logic. -/
theorem wpExtend {s : Store H} {f : Frame} {vs : List Val} {sx : Signedness} {x : BitVec 32}
    {rest : List Admin} {Q : Post H}
    (h : Wp c P host s f (vals (vs ++ [.num ⟨.int .i64, match sx with
      | .signed => x.signExtend 64
      | .unsigned => x.setWidth 64⟩]) ++ rest) Q) :
    Wp c P host s f (vals (vs ++ [.num ⟨.int .i32, x⟩]) ++ .plain (.convert (.extend sx)) :: rest)
      Q := by
  refine Silmaril.Wasm.Logic.Hoare.Wp.convert (op := .extend sx) (x := x) (fun z hz => ?_)
    (fun e he => ?_)
  · have h' := (Silmaril.Wasm.Auto.VCGen.convertP_extend (P := P) _).1 hz
    cases sx <;> (injection h' with h''; subst h''; exact h)
  · have h' := (Silmaril.Wasm.Auto.VCGen.convertP_extend (P := P) _).1 he
    cases sx <;> cases h'

theorem sound_wrap (h : step1 S.mem (.convert .wrap) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.convert .wrap) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 .i64 σ.stack = some (a, st) ∧
      { σ with stack := .i32 (.wrap a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  obtain ⟨ha, hst⟩ := pop1_vlt hp hR
  have hk' := hk ρ s f (Rel.withStack hR (cons_vlt (by simpa [SV.vlt, Tm.vlt] using ha) hst))
    (EqBelow.refl _ _)
  rw [dens_pop1 hp hR]
  simp only [dens, List.map_cons, List.reverse_cons, SV.den, Tm.den, wrapW] at hk' ⊢
  exact wpWrap hk'

theorem sound_extend {sx : Signedness} (h : step1 S.mem (.convert (.extend sx)) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.convert (.extend sx)) :: rest) Q := by
  obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 .i32 σ.stack = some (a, st) ∧
      { σ with stack := .i64 (.ext sx a) :: st } = σ' ∧ [] = side := by simpa [step1] using h
  obtain ⟨ha, hst⟩ := pop1_vlt hp hR
  have hk' := hk ρ s f (Rel.withStack hR (cons_vlt (by simpa [SV.vlt, Tm.vlt] using ha) hst))
    (EqBelow.refl _ _)
  rw [dens_pop1 hp hR]
  cases sx <;> simp only [dens, List.map_cons, List.reverse_cons, SV.den, Tm.den, extSW,
    extUW] at hk' ⊢ <;>
    exact wpExtend hk'

theorem sound_convert {op : ConvertOp} (h : step1 S.mem (.convert op) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.convert op) :: rest) Q := by
  cases op
  case wrap => exact sound_wrap h hR hk
  case extend sx => exact sound_extend h hR hk
  all_goals exact absurd h (by simp [step1])

/-- A load whose address is in bounds, evaluated. -/
theorem exec1_load {t : IntType} {pk : Option (PackSize × Signedness)} {x : MemIdx} {arg : MemArg}
    {a : Tm .i32} {st : List SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hc : S.mem = true ∧ x.toNat = 0) (hp : pop1 .i32 σ.stack = some (a, st))
    (hin : (a.den F ρ ρ).toNat + arg.offset.val + (ldSz t pk).1 ≤ (ρ.mem σ.mem).size) :
    exec1 s f rs (.intLoad t pk x arg) = some (s, f, dens F ρ (SV.of t (.load t (ldSz t pk).1
      (ldSz t pk).2 (.v σ.mem) a arg.offset.val) :: st)) := by
  obtain ⟨ma, mi, hmem, hb, -⟩ := Rel.mem? hR hc.1 hc.2
  rw [dens_pop1 hp hR]
  rcases pk with _ | ⟨sz, sx⟩
  · have hin' : (a.den F ρ ρ).toNat + arg.offset.val + t.width / 8 ≤ (ρ.mem σ.mem).size := hin
    simp only [exec1, popInt_num, Option.bind_some, hmem, hb,
      Silmaril.Wasm.Execution.Core.effAddr, rd_of_load hin', Option.map_some, dens, List.map_cons,
      SV.den_of, Tm.den, MR.den, ldSz, ldT_eq]
  · have hin' : (a.den F ρ ρ).toNat + arg.offset.val + sz.width / 8 ≤ (ρ.mem σ.mem).size := hin
    simp only [exec1, popInt_num, Option.bind_some, hmem, hb,
      Silmaril.Wasm.Execution.Core.effAddr, rd_of_load hin', Option.map_some, dens, List.map_cons,
      SV.den_of, Tm.den, MR.den, ldSz, ldT_eq]
    cases sx <;> rfl

theorem sound_load {t : IntType} {pk : Option (PackSize × Signedness)} {x : MemIdx} {arg : MemArg}
    (h : step1 S.mem (.intLoad t pk x arg) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hs : ∀ φ ∈ side, φ.den F ρ ρ)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intLoad t pk x arg) :: rest) Q := by
  simp only [step1] at h
  split at h
  next hc =>
    have hc' : S.mem = true ∧ x.toNat = 0 := by simpa using hc
    obtain ⟨a, st, hp, rfl, rfl⟩ : ∃ a st, pop1 .i32 σ.stack = some (a, st) ∧
        { σ with stack := SV.of t (.load t (ldSz t pk).1 (ldSz t pk).2 (.v σ.mem) a
          arg.offset.val) :: st } = σ' ∧
        [Fm.inb (.v σ.mem) a (arg.offset.val + (ldSz t pk).1)] = side := by simpa using h
    obtain ⟨ha, hst⟩ := pop1_vlt hp hR
    have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
    have hin : (a.den F ρ ρ).toNat + arg.offset.val + (ldSz t pk).1 ≤ (ρ.mem σ.mem).size := by
      have h₁ : (a.den F ρ ρ).toNat + (arg.offset.val + (ldSz t pk).1) ≤ (ρ.mem σ.mem).size :=
        hs _ List.mem_cons_self
      omega
    exact pure_step hR (exec1_load hR hc' hp hin)
      (cons_vlt (by simp [SV.vlt_of, Tm.vlt, MR.vlt, hm, ha]) hst) hk
  next => simp at h

/-- One more path condition, true in an environment that agrees below `n`. -/
theorem pc_ext {n : Nat} {ρ ρ' : Env} {φ : Fm} {pc : List Fm} (hE : EqBelow n ρ ρ')
    (hpc : ∀ ψ ∈ pc, ψ.den F ρ ρ) (hpcb : ∀ ψ ∈ pc, ψ.vlt n = true) (hφ : φ.den F ρ' ρ') :
    ∀ ψ ∈ φ :: pc, ψ.den F ρ' ρ' := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact (Fm.den_eqBelow hE hE ψ (hpcb ψ hψ)).mp (hpc ψ hψ)

theorem vlt_ext {n n' : Nat} {φ : Fm} {pc : List Fm} (hn : n ≤ n')
    (hpcb : ∀ ψ ∈ pc, ψ.vlt n = true) (hφ : φ.vlt n' = true) : ∀ ψ ∈ φ :: pc, ψ.vlt n' = true := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact Fm.vlt_mono hn ψ (hpcb ψ hψ)

theorem store_inv {t : IntType} {pk : Option PackSize} {x : MemIdx} {arg : MemArg}
    (h : step1 S.mem (.intStore t pk x arg) σ = some (σ', side)) :
    (S.mem = true ∧ x.toNat = 0) ∧ ∃ v st a st', pop1 t σ.stack = some (v, st) ∧
      pop1 .i32 st = some (a, st') ∧
      σ' = { σ with
        stack := st'
        mem := σ.nv
        nv := σ.nv + 1
        pc := .st σ.nv (.v σ.mem) (stSz t pk) a arg.offset.val v :: σ.pc } ∧
      side = [Fm.inb (.v σ.mem) a (arg.offset.val + stSz t pk)] := by
  simp only [step1] at h
  split at h
  next hc =>
    refine ⟨by simpa using hc, ?_⟩
    rcases hp : pop1 t σ.stack with _ | ⟨v, st⟩ <;> simp only [hp, reduceCtorEq] at h
    rcases hp' : pop1 .i32 st with _ | ⟨a, st'⟩ <;>
      simp only [hp', Option.map_none, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq] at h
    exact ⟨v, st, a, st', rfl, hp', h.1.symm, h.2.symm⟩
  next => simp at h

/-- A store whose address is in bounds, evaluated: memory `0` becomes `stT …`. -/
theorem exec1_store {t : IntType} {pk : Option PackSize} {x : MemIdx} {arg : MemArg}
    {v : Tm t} {a : Tm .i32} {st' : List SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hc : S.mem = true ∧ x.toNat = 0) (hst : σ.stack = SV.of t v :: SV.of .i32 a :: st')
    (hin : (a.den F ρ ρ).toNat + arg.offset.val + stSz t pk ≤ (ρ.mem σ.mem).size) :
    exec1 s f rs (.intStore t pk x arg) = some (upd S s₀ m (stT t (stSz t pk) (ρ.mem σ.mem)
      ((a.den F ρ ρ).toNat + arg.offset.val) (v.den F ρ ρ)), f, dens F ρ st') := by
  obtain ⟨ma, mi, hmem, hb, hupd⟩ := Rel.mem? hR hc.1 hc.2
  obtain ⟨B', hB'⟩ := store_some (B := mi.bytes) (a := (a.den F ρ ρ).toNat + arg.offset.val)
    (n := stSz t pk) ((v.den F ρ ρ).setWidth (8 * stSz t pk)) (by rw [hb]; omega)
  have hsB : stT t (stSz t pk) (ρ.mem σ.mem) ((a.den F ρ ρ).toNat + arg.offset.val)
      (v.den F ρ ρ) = B' := by
    rw [← hb, stT_eq, hB']
    rfl
  rw [hsB, hR.stack, hst, ← hupd]
  rcases pk with _ | sz <;> simp only [stSz] at hB' <;>
    simp [exec1, popInt_num, SV.den_of, hmem, Silmaril.Wasm.Execution.Core.effAddr, hB']

/-- The state after a store is related to the new configuration, with memory variable `σ.nv`
set to the new memory. -/
theorem rel_store {t : IntType} {n : Nat} {off : Nat} {v : Tm t} {a : Tm .i32} {st' : List SV}
    {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : v.vlt σ.nv = true) (ha : a.vlt σ.nv = true) (hst : ∀ w ∈ st', w.vlt σ.nv = true)
    (hsB : stT t n (ρ.mem σ.mem) ((a.den F ρ ρ).toNat + off) (v.den F ρ ρ) = B') :
    Rel F S lt ρ₀ s₀ m (ρ.setM σ.nv B')
      { σ with stack := st', mem := σ.nv, nv := σ.nv + 1, pc := .st σ.nv (.v σ.mem) n a off v :: σ.pc }
      (upd S s₀ m B') f (dens F (ρ.setM σ.nv B') st') := by
  obtain ⟨hl, -, hpc, hm⟩ := (fresh_iff σ).mp hR.fresh
  have hE : EqBelow σ.nv ρ (ρ.setM σ.nv B') := eqBelow_setM ρ σ.nv B'
  have h0 : (0 : Nat) ≠ σ.nv := by have := hR.pnv; omega
  have hφ : (Fm.st σ.nv (.v σ.mem) n a off v).den F (ρ.setM σ.nv B') (ρ.setM σ.nv B') := by
    simp only [Fm.den, MR.den]
    rw [← Tm.den_eqBelow hE hE a ha, ← Tm.den_eqBelow hE hE v hv]
    simp only [Env.setM, ↓reduceIte, show σ.mem ≠ σ.nv by omega]
    exact hsB.symm
  have hφb : (Fm.st σ.nv (.v σ.mem) n a off v).vlt (σ.nv + 1) = true := by
    simp [Fm.vlt, MR.vlt, Tm.vlt_mono (Nat.le_succ _) a ha, Tm.vlt_mono (Nat.le_succ _) v hv]
    omega
  exact { store := by simp [Env.setM]
          memOk := by simpa [Env.setM, h0] using hR.memOk
          modl := hR.modl
          locals := by
            rw [hR.locals]
            exact List.map_congr_left fun w hw => congrArg some (SV.den_eqBelow hE hE w (hl w hw))
          stack := rfl, types := hR.types
          agree := Agree.trans (Agree.symm (agree_of_eqBelow hE hR.pnv)) hR.agree
          pc := pc_ext hE hR.pc hpc hφ
          fresh := (fresh_iff _).mpr ⟨fun w hw => SV.vlt_mono (Nat.le_succ _) w (hl w hw),
            fun w hw => SV.vlt_mono (Nat.le_succ _) w (hst w hw),
            vlt_ext (Nat.le_succ _) hpc hφb, by simp⟩
          pnv := Nat.lt_succ_of_lt hR.pnv, pre := hR.pre }

theorem sound_store {t : IntType} {pk : Option PackSize} {x : MemIdx} {arg : MemArg}
    (h : step1 S.mem (.intStore t pk x arg) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hs : ∀ φ ∈ side, φ.den F ρ ρ)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intStore t pk x arg) :: rest) Q := by
  obtain ⟨hc, v, st, a, st', hp, hp', rfl, rfl⟩ := store_inv h
  obtain ⟨hst', hv, ha, hst⟩ := pop2_vlt hp hp' hR
  have hin : (a.den F ρ ρ).toNat + arg.offset.val + stSz t pk ≤ (ρ.mem σ.mem).size := by
    have h₁ : (a.den F ρ ρ).toNat + (arg.offset.val + stSz t pk) ≤ (ρ.mem σ.mem).size :=
      hs _ List.mem_cons_self
    omega
  have hE := eqBelow_setM ρ σ.nv (stT t (stSz t pk) (ρ.mem σ.mem)
    ((a.den F ρ ρ).toNat + arg.offset.val) (v.den F ρ ρ))
  have hden : dens F (ρ.setM σ.nv _) st' = dens F ρ st' :=
    List.map_congr_left fun w hw => (SV.den_eqBelow hE hE w (hst w hw)).symm
  refine Silmaril.Wasm.Examples.Common.Wp.exec1 (m := c) (exec1_store hR hc hst' hin) ?_
  rw [← hden]
  exact hk _ _ _ (rel_store hR hv ha hst rfl) hE

theorem setSV_eqBelow (ρ : Env) (n : Nat) (v : SV) : EqBelow n ρ (ρ.setSV F n v) := by
  cases v <;> (simp only [Env.setSV]; exact eqBelow_setV _ _ _ _)

theorem setSV_mem (ρ : Env) (n : Nat) (v : SV) : (ρ.setSV F n v).mem = ρ.mem := by
  cases v <;> rfl

theorem setSV_var {ρ : Env} {n : Nat} {v : SV} (hv : v.vlt n = true) :
    (SV.of v.ty (.var v.ty n)).den F (ρ.setSV F n v) (ρ.setSV F n v) = v.den F ρ ρ := by
  cases v <;> simp [Env.setSV, SV.of, SV.ty, SV.den, Tm.den, setV_get]

theorem defF_setSV {ρ : Env} {n : Nat} {v : SV} (hv : v.vlt n = true) :
    (defF n v).den F (ρ.setSV F n v) (ρ.setSV F n v) := by
  have hE := setSV_eqBelow (F := F) ρ n v
  rcases v with a | a <;> simp only [defF, Fm.den, relP, relW, Tm.den] <;>
    rw [← Tm.den_eqBelow hE hE a hv] <;> simp only [Env.setSV] <;> exact setV_get ρ _ _ _

theorem defF_vlt {n : Nat} {v : SV} (hv : v.vlt n = true) : (defF n v).vlt (n + 1) = true := by
  rcases v with a | a <;> simp [defF, Fm.vlt, Tm.vlt, Tm.vlt_mono (Nat.le_succ _) a hv]

/-- Binding a value of the stack to a fresh variable: the new environment. -/
theorem bindV_sound {v : SV} {σ₁ : SSt} (hv : v.vlt σ₁.nv = true)
    (hpc : ∀ φ ∈ σ₁.pc, φ.den F ρ ρ) (hpcb : ∀ φ ∈ σ₁.pc, φ.vlt σ₁.nv = true) :
    ∃ ρ', EqBelow σ₁.nv ρ ρ' ∧ ρ'.mem = ρ.mem ∧
      (bindV σ₁ v).1.den F ρ' ρ' = v.den F ρ ρ ∧ (bindV σ₁ v).1.ty = v.ty ∧
      (bindV σ₁ v).1.vlt (bindV σ₁ v).2.nv = true ∧
      σ₁.nv ≤ (bindV σ₁ v).2.nv ∧
      (bindV σ₁ v).2.locals = σ₁.locals ∧ (bindV σ₁ v).2.stack = σ₁.stack ∧
      (bindV σ₁ v).2.mem = σ₁.mem ∧
      (∀ φ ∈ (bindV σ₁ v).2.pc, φ.den F ρ' ρ') ∧
      (∀ φ ∈ (bindV σ₁ v).2.pc, φ.vlt (bindV σ₁ v).2.nv = true) := by
  unfold bindV
  split
  · exact ⟨ρ, EqBelow.refl _ _, rfl, rfl, rfl, hv, le_rfl, rfl, rfl, rfl, hpc, hpcb⟩
  · have hE := setSV_eqBelow (F := F) ρ σ₁.nv v
    exact ⟨ρ.setSV F σ₁.nv v, hE, setSV_mem ρ σ₁.nv v, setSV_var hv, SV.ty_of _ _,
      by simp [SV.vlt_of, Tm.vlt], Nat.le_succ _, rfl, rfl, rfl,
      pc_ext hE hpc hpcb (defF_setSV hv), vlt_ext (Nat.le_succ _) hpcb (defF_vlt hv)⟩

/-- After `local.set x`/`local.tee x` of the top value `v` (bound to a fresh variable when not
atomic), with the new stack `stk`: the configuration with local `x` set to `v`'s value is related
to the new state. -/
theorem rel_set {x : LocalIdx} {v w : SV} {st stk : List SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hst : σ.stack = v :: st) (hw : σ.locals[x.toNat]? = some w) (hty : v.ty = w.ty)
    (hstk : stk = st ∨ stk = (bindV { σ with stack := st } v).1 :: st) :
    ∃ ρ', EqBelow σ.nv ρ ρ' ∧ Rel F S lt ρ₀ s₀ m ρ'
      { (bindV { σ with stack := st } v).2 with
        locals := σ.locals.set x.toNat (bindV { σ with stack := st } v).1, stack := stk }
      s (f.setLocal x (v.den F ρ ρ)) (dens F ρ' stk) ∧
      (stk = st → dens F ρ' stk = dens F ρ st) ∧
      (stk ≠ st → dens F ρ' stk = v.den F ρ ρ :: dens F ρ st) := by
  obtain ⟨hl, hall, hpcb, hm⟩ := (fresh_iff σ).mp hR.fresh
  rw [hst] at hall
  have hv : v.vlt σ.nv = true := hall v List.mem_cons_self
  have hstb : ∀ u ∈ st, u.vlt σ.nv = true := fun u hu => hall u (List.mem_cons_of_mem _ hu)
  obtain ⟨ρ', hE, hmem, hden, hty', hb, hnx, -, -, hbm, hpc', hpcb'⟩ :=
    bindV_sound (ρ := ρ) (σ₁ := { σ with stack := st }) hv hR.pc hpcb
  have hx : x.toNat < σ.locals.length := (List.getElem?_eq_some_iff.mp hw).1
  have hdst : dens F ρ' st = dens F ρ st :=
    List.map_congr_left fun u hu => (SV.den_eqBelow hE hE u (hstb u hu)).symm
  have hstk' : ∀ u ∈ stk, u.vlt (bindV { σ with stack := st } v).2.nv = true := by
    intro u hu
    rcases hstk with rfl | rfl
    · exact SV.vlt_mono hnx u (hstb u hu)
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact hb
      · exact SV.vlt_mono hnx u (hstb u hu)
  refine ⟨ρ', hE, {
    store := by rw [show (bindV { σ with stack := st } v).2.mem = σ.mem from hbm, hmem]; exact hR.store
    memOk := by rw [hmem]; exact hR.memOk
    modl := hR.modl
    locals := by
      simp only [Frame.setLocal, hR.locals, List.map_set, hden]
      congr 1
      exact List.map_congr_left fun u hu => congrArg some (SV.den_eqBelow hE hE u (hl u hu))
    stack := rfl
    types := by
      rw [List.map_set, hty', ← hR.types]
      have hwt : (σ.locals.map SV.ty)[x.toNat]'(by simpa using hx) = w.ty := by
        simp [(List.getElem?_eq_some_iff.mp hw).2]
      rw [hty, ← hwt, List.set_getElem_self]
    agree := Agree.trans (Agree.symm (agree_of_eqBelow hE hR.pnv)) hR.agree
    pc := hpc'
    fresh := (fresh_iff _).mpr ⟨?_, hstk', hpcb', by simpa [hbm] using Nat.lt_of_lt_of_le hm hnx⟩
    pnv := Nat.lt_of_lt_of_le hR.pnv hnx
    pre := hR.pre }, fun h => by rw [h, hdst], fun h => ?_⟩
  · intro u hu
    rcases List.mem_or_eq_of_mem_set hu with hu | rfl
    · exact SV.vlt_mono hnx u (hl u hu)
    · exact hb
  · rcases hstk with rfl | rfl
    · exact absurd rfl h
    · simp only [dens, List.map_cons, hden]
      exact congrArg _ hdst

theorem localSet_inv {x : LocalIdx} (h : step1 S.mem (.localSet x) σ = some (σ', side)) :
    ∃ v st w, σ.stack = v :: st ∧ σ.locals[x.toNat]? = some w ∧ v.ty = w.ty ∧
      σ' = { (bindV { σ with stack := st } v).2 with
        locals := σ.locals.set x.toNat (bindV { σ with stack := st } v).1 } := by
  simp only [step1] at h
  split at h
  next v st w hst hw =>
    split at h
    next hty =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨v, st, w, hst, hw, hty, h.1.symm⟩
    next => simp at h
  next => simp at h

theorem sound_localSet {x : LocalIdx} (h : step1 S.mem (.localSet x) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.localSet x) :: rest) Q := by
  obtain ⟨v, st, w, hst, hw, hty, rfl⟩ := localSet_inv h
  have hx : x.toNat < f.locals.length := by
    rw [hR.locals]; simpa using (List.getElem?_eq_some_iff.mp hw).1
  have hstk : (bindV { σ with stack := st } v).2.stack = st := by unfold bindV; split <;> rfl
  obtain ⟨ρ', hEρ, hrel, hd, -⟩ := rel_set hR hst hw hty
    (stk := (bindV { σ with stack := st } v).2.stack) (.inl hstk)
  refine Silmaril.Wasm.Examples.Common.Wp.exec1 (m := c)
    (rs' := dens F ρ' (bindV { σ with stack := st } v).2.stack) (s' := s)
    (f' := f.setLocal x (v.den F ρ ρ)) ?_ (hk ρ' s _ hrel hEρ)
  rw [hd hstk]
  simp [exec1, popV, hR.stack, hst, hx]

theorem sound_localTee {x : LocalIdx} (h : step1 S.mem (.localTee x) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.localTee x) :: rest) Q := by
  simp only [step1] at h
  split at h
  next v st w hst hw =>
    split at h
    next hty =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx : x.toNat < f.locals.length := by
        rw [hR.locals]; simpa using (List.getElem?_eq_some_iff.mp hw).1
      obtain ⟨ρ', hEρ, hrel, -, hd⟩ := rel_set hR hst hw hty
        (stk := (bindV { σ with stack := st } v).1 :: st) (.inr rfl)
      have hd' := hd (fun h => by simpa using congrArg List.length h)
      refine Silmaril.Wasm.Examples.Common.Wp.exec1 (m := c)
        (rs' := dens F ρ' ((bindV { σ with stack := st } v).1 :: st)) (s' := s)
        (f' := f.setLocal x (v.den F ρ ρ)) ?_ (hk ρ' s _ hrel hEρ)
      rw [hd']
      simp [exec1, popV, hR.stack, hst, hx]
    next => simp at h
  next => simp at h

theorem sound_nop (h : step1 S.mem .nop σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain .nop :: rest) Q := by
  obtain ⟨rfl, rfl⟩ : σ = σ' ∧ [] = side := by simpa [step1] using h
  refine pure_step (st := σ.stack) hR (by simp [exec1, hR.stack]) (stack_vlt hR) ?_
  exact hk

theorem sound_drop (h : step1 S.mem .drop σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain .drop :: rest) Q := by
  obtain ⟨v, st, hst, rfl, rfl⟩ : ∃ v st, σ.stack = v :: st ∧
      { σ with stack := st } = σ' ∧ [] = side := by
    simp only [step1] at h
    split at h <;> simp_all
  have hall := stack_vlt hR
  rw [hst] at hall
  exact pure_step hR (by simp [exec1, popV, hR.stack, hst])
    (fun u hu => hall u (List.mem_cons_of_mem _ hu)) hk

theorem sound_intConst {t : IntType} {x : BitVec t.width}
    (h : step1 S.mem (.intConst t x) σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.intConst t x) :: rest) Q := by
  obtain ⟨rfl, rfl⟩ : { σ with stack := SV.of t (.lit t x.toNat) :: σ.stack } = σ' ∧
      [] = side := by simpa [step1] using h
  refine pure_step hR ?_ (cons_vlt (by simp [SV.vlt_of, Tm.vlt]) (stack_vlt hR)) hk
  simp [exec1, hR.stack, SV.den_of, Tm.den, litT_toNat]

theorem sound_localGet {x : LocalIdx} (h : step1 S.mem (.localGet x) σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.localGet x) :: rest) Q := by
  obtain ⟨v, hv, rfl, rfl⟩ : ∃ v, σ.locals[x.toNat]? = some v ∧
      { σ with stack := v :: σ.stack } = σ' ∧ [] = side := by simpa [step1] using h
  have hl := ((fresh_iff σ).mp hR.fresh).1
  refine pure_step hR ?_ (cons_vlt (hl v (List.mem_of_getElem? hv)) (stack_vlt hR)) hk
  simp [exec1, localVal?, Frame.local?, hR.locals, hR.stack, hv]

/-- **A straight-line instruction**, every run. -/
theorem step1_sound (h : step1 S.mem i σ = some (σ', side)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hs : ∀ φ ∈ side, φ.den F ρ ρ) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ' rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: rest) Q := by
  cases i
  case nop => exact sound_nop h hR hk
  case drop => exact sound_drop h hR hk
  case intConst => exact sound_intConst h hR hk
  case localGet => exact sound_localGet h hR hk
  case localSet => exact sound_localSet h hR hk
  case localTee => exact sound_localTee h hR hk
  case intUnOp => exact sound_intUnOp h hR hk
  case intBinOp => exact sound_intBinOp h hR hs hk
  case intTestOp => exact sound_intTestOp h hR hk
  case intRelOp => exact sound_intRelOp h hR hk
  case convert => exact sound_convert h hR hk
  case intLoad => exact sound_load h hR hs hk
  case intStore => exact sound_store h hR hs hk
  all_goals exact absurd h (by simp [step1])

end Instr

end Silmaril.Proofs.Wasm.Auto.VCGen2