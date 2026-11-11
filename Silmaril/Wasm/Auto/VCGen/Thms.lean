module

public import Silmaril.Wasm.Auto.VCGen.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Logic.VC.Thms
import Silmaril.Proofs.Wasm.Auto.VCGen.Func

/-!
# A reflective verification-condition generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto.VCGen.{Basic,Convert,Step,Sound,Func}`:

* **`genFunc_sound`**: `AllValid F (genFunc S code fuel)` gives
  `FSpecValid P host a (fspec F S a fi)` for every profile `P` and host relation `host`, for the
  function instance `fi` at address `a` running `code` (given its type has as many parameters
  and results as `S`): every call with arguments `argsOf S ρ` satisfying `S.pre` returns results
  satisfying `S.post`, does not trap and leaves the store unchanged (partial correctness);
* `gen_sound` (the generator for any code, labels and continuation), `step1_wp` (straight-line
  instructions), `HWP.wrap`/`HWP.extend` (every-run rules for `i32.wrap_i64`,
  `i64.extend_i32_s/u`, which the existing `exec1` does not evaluate).

## Tactics

* **`vcgen_reduce`**: on a goal `AllValid F l` with `l` closed (typically `genFunc S code fuel`),
  computes the list of conditions by `Meta.reduce` and replaces `l` by it; the equation
  `l = l'` is an auxiliary lemma checked by the kernel's definitional check (as
  `Silmaril.Wasm.Verify.Kernel.kernel_rfl`), so neither the elaborator nor `simp` executes the
  generator.
* **`vcgen`**: `vcgen_reduce`, then unfold the denotation of the conditions with `simp only`
  into ordinary `BitVec 32`/`BitVec 64` propositions, split them into one goal each and name
  the variables (`vcgen_vars`: `ρ.e32 i` becomes `vi`, `ρ.e64 i` becomes `wi`; parameter `i` is
  variable `i`, the locals at the head of a loop are `p + j`). The goals are what `omega`,
  `bv_omega`, `simp` and `decide` work on; no SAT solving and no compiled evaluation.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.VCGen

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.VCGen` -/

section
-- from Silmaril/Proofs/Wasm/Auto/VCGen/Basic.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem Fm.den_conj {F : Fns} (ρ ξ : Env)
    (l : List Fm) : (Fm.conj l).den F ρ ξ ↔ ∀ p ∈ l, p.den F ρ ξ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Fm.den_conj (F := F) (ρ := ρ) (ξ := ξ) (l := l)

theorem allValid_append {F : Fns} {l₁ l₂ : List Fm} :
    AllValid F (l₁ ++ l₂) ↔ AllValid F l₁ ∧ AllValid F l₂ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.allValid_append (F := F) (l₁ := l₁) (l₂ := l₂)

theorem allValid_iff {F : Fns} {l : List Fm} : AllValid F l ↔ ∀ φ ∈ l, Valid F φ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.allValid_iff (F := F) (l := l)

theorem allValid_map_vc {F : Fns} {σ : SSt} {l : List Fm} {ρ : Env} (h : AllValid F (l.map (vc σ)))
    (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) : ∀ φ ∈ l, φ.den F ρ ρ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.allValid_map_vc (F := F) (σ := σ) (l := l) (ρ := ρ) (h := h)
    (hpc := hpc)

theorem vc_holds {F : Fns} {σ : SSt} {φ : Fm} {ρ : Env} (h : Valid F (vc σ φ))
    (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) : φ.den F ρ ρ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.vc_holds (F := F) (σ := σ) (φ := φ) (ρ := ρ) (h := h) (hpc := hpc)

theorem not_bad {F : Fns}
    {σ : SSt} {ρ : Env} (h : AllValid F (bad σ)) (hpc : ∀ p ∈ σ.pc, p.den F ρ ρ) :
    False :=
  Silmaril.Proofs.Wasm.Auto.VCGen.not_bad (F := F) (σ := σ) (ρ := ρ) (h := h) (hpc := hpc)

theorem locEnv_eq_valEnv {F : Fns} (ρ ξ : Env) (ls : List SV) :
    locEnv F ρ ξ ls = valEnv (ls.map (SV.den F ρ ξ)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.locEnv_eq_valEnv (F := F) (ρ := ρ) (ξ := ξ) (ls := ls)

theorem Tm.den_subst {F : Fns} (ρ ξ : Env) (ls : List SV) :
    ∀ {t : IntType} (a : Tm t), (a.subst ls).den F ρ ξ = a.den F ρ (locEnv F ρ ξ ls) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Tm.den_subst (F := F) (ρ := ρ) (ξ := ξ) (ls := ls)

theorem Fm.den_subst {F : Fns} (ρ ξ : Env) (ls : List SV) :
    ∀ φ : Fm, (φ.subst ls).den F ρ ξ ↔ φ.den F ρ (locEnv F ρ ξ ls) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Fm.den_subst (F := F) (ρ := ρ) (ξ := ξ) (ls := ls)

theorem Agree.trans {ps : List IntType} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : Agree ps ρ₁ ρ₂)
    (h₂ : Agree ps ρ₂ ρ₃) : Agree ps ρ₁ ρ₃ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Agree.trans (ps := ps) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃) (h₁ := h₁)
    (h₂ := h₂)

theorem Agree.symm {ps : List IntType} {ρ₁ ρ₂ : Env} (h : Agree ps ρ₁ ρ₂) : Agree ps ρ₂ ρ₁ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Agree.symm (ps := ps) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (h := h)

theorem Agree.refl (ps : List IntType) (ρ : Env) : Agree ps ρ ρ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Agree.refl (ps := ps) (ρ := ρ)

theorem Tm.den_scoped {F : Fns} {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ {t : IntType} (a : Tm t), a.scoped ps = true → a.den F ρ ξ = a.den F ρ' ξ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Tm.den_scoped (F := F) (ps := ps) (ρ := ρ) (ρ' := ρ') (hρ := hρ)
    (ξ := ξ)

theorem Fm.den_scoped {F : Fns} {ps : List IntType} {ρ ρ' : Env} (hρ : Agree ps ρ ρ') (ξ : Env) :
    ∀ φ : Fm, φ.scoped ps = true → (φ.den F ρ ξ ↔ φ.den F ρ' ξ) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Fm.den_scoped (F := F) (ps := ps) (ρ := ρ) (ρ' := ρ') (hρ := hρ)
    (ξ := ξ)

theorem SV.den_of {F : Fns} (ρ ξ : Env) : ∀ (t : IntType) (a : Tm t),
    (SV.of t a).den F ρ ξ = .num ⟨.int t, a.den F ρ ξ⟩ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.SV.den_of (F := F) (ρ := ρ) (ξ := ξ)

theorem SV.ty_of : ∀ (t : IntType) (a : Tm t), (SV.of t a).ty = t :=
  Silmaril.Proofs.Wasm.Auto.VCGen.SV.ty_of

theorem pop1_eq {t : IntType} {st st' : List SV} {a : Tm t} (h : pop1 t st = some (a, st')) :
    st = SV.of t a :: st' :=
  Silmaril.Proofs.Wasm.Auto.VCGen.pop1_eq (t := t) (st := st) (st' := st') (a := a) (h := h)

theorem selV_den {F : Fns} {c : Tm .i32} {v₁ v₂ v : SV} (h : selV c v₁ v₂ = some v) (ρ ξ : Env) :
    v.den F ρ ξ = cond (nz32 (c.den F ρ ξ)) (v₁.den F ρ ξ) (v₂.den F ρ ξ) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.selV_den (F := F) (c := c) (v₁ := v₁) (v₂ := v₂) (v := v) (h := h)
    (ρ := ρ) (ξ := ξ)

theorem bool32_ne_zero (b : Bool) : bool32 b ≠ 0 ↔ b = true :=
  Silmaril.Proofs.Wasm.Auto.VCGen.bool32_ne_zero (b := b)

theorem bool32_bne_zero (b : Bool) : (bool32 b != 0) = b :=
  Silmaril.Proofs.Wasm.Auto.VCGen.bool32_bne_zero (b := b)

theorem relV_ne_zero (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
    relV t op x y ≠ 0 ↔ relP t op x y :=
  Silmaril.Proofs.Wasm.Auto.VCGen.relV_ne_zero (t := t) (op := op) (x := x) (y := y)

theorem eqzV_ne_zero : ∀ (t : IntType) (x : BitVec t.width), eqzV t x ≠ 0 ↔ x = litT t 0 :=
  Silmaril.Proofs.Wasm.Auto.VCGen.eqzV_ne_zero

theorem intRelOp_eq_relV (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
    intRelOp t op x y = relV t op x y :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intRelOp_eq_relV (t := t) (op := op) (x := x) (y := y)

theorem intTestOp_eq_eqzV (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
    intTestOp t op x = eqzV t x :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intTestOp_eq_eqzV (t := t) (op := op) (x := x)

theorem intUnOp_eq_unT (t : IntType) (op : IntUnOp) (x : BitVec t.width) :
    intUnOp t op x = unT t op x :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intUnOp_eq_unT (t := t) (op := op) (x := x)

theorem litT_toNat : ∀ (t : IntType) (c : BitVec t.width), litT t c.toNat = c :=
  Silmaril.Proofs.Wasm.Auto.VCGen.litT_toNat

theorem nz32_iff (x : BitVec 32) : nz32 x = true ↔ x ≠ 0 :=
  Silmaril.Proofs.Wasm.Auto.VCGen.nz32_iff (x := x)

theorem den_condF {F : Fns} (ρ ξ : Env) (c : Tm .i32) :
    (condF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) ≠ 0 :=
  Silmaril.Proofs.Wasm.Auto.VCGen.den_condF (F := F) (ρ := ρ) (ξ := ξ) (c := c)

theorem den_ncondF {F : Fns} (ρ ξ : Env) (c : Tm .i32) :
    (ncondF c).den F ρ ξ ↔ (c.den F ρ ξ : BitVec 32) = 0 :=
  Silmaril.Proofs.Wasm.Auto.VCGen.den_ncondF (F := F) (ρ := ρ) (ξ := ξ) (c := c)

/-- The side condition `b ≠ 0`. -/
theorem den_ne_zero {F : Fns} {t : IntType} {b : Tm t} {ρ ξ : Env}
    (h : (Fm.rel .ne b (.lit t 0)).den F ρ ξ) : ¬ b.den F ρ ξ = 0 :=
  Silmaril.Proofs.Wasm.Auto.VCGen.den_ne_zero (F := F) (t := t) (b := b) (ρ := ρ) (ξ := ξ) (h := h)

theorem intBinOp_sdiv {F : Fns} {t : IntType} {a b : Tm t} {ρ ξ : Env}
    (h : ∀ φ ∈ safeF t (.div .signed) a b, φ.den F ρ ξ) :
    intBinOp t (.div .signed) (a.den F ρ ξ) (b.den F ρ ξ) =
      .ok (binT t (.div .signed) (a.den F ρ ξ) (b.den F ρ ξ)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intBinOp_sdiv (F := F) (t := t) (a := a) (b := b) (ρ := ρ) (ξ := ξ)
    (h := h)

theorem intBinOp_of_safe {F : Fns} {t : IntType} {op : IntBinOp} {a b : Tm t} {ρ ξ : Env}
    (h : ∀ φ ∈ safeF t op a b, φ.den F ρ ξ) :
    intBinOp t op (a.den F ρ ξ) (b.den F ρ ξ) = .ok (binT t op (a.den F ρ ξ) (b.den F ρ ξ)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intBinOp_of_safe (F := F) (t := t) (op := op) (a := a) (b := b)
    (ρ := ρ) (ξ := ξ) (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/VCGen/Convert.lean

open Silmaril.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Logic.Hoare (HWP fnv_eq_split)

theorem num_convert {P : Profile} {args : List Val} {op : ConvertOp} {is' : List Admin}
    (h : NumericStep P (vals args ++ [.plain (.convert op)]) is') :
    ∃ x : BitVec op.source.width, args = [.num ⟨op.source, x⟩] ∧
      ((∃ z, convertP P op x (.ok z) ∧ is' = [(Val.num ⟨op.target, z⟩).toAdmin]) ∨
        (∃ e, convertP P op x (.error e) ∧ is' = [.trap])) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.num_convert (P := P) (args := args) (op := op) (is' := is') (h := h)

theorem head_convert {H : Type} {P : Profile}
    {s : Store H} {f : Frame} {args : List Val} {op : ConvertOp}
    {c₀ : Config H} (h : Head P s f args (.plain (.convert op)) c₀) :
    ∃ x : BitVec op.source.width, args = [.num ⟨op.source, x⟩] ∧
      ((∃ z, convertP P op x (.ok z) ∧ c₀ = ⟨s, f, [(Val.num ⟨op.target, z⟩).toAdmin]⟩) ∨
        (∃ e, convertP P op x (.error e) ∧ c₀ = ⟨s, f, [.trap]⟩)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.head_convert (H := H) (P := P) (s := s) (f := f) (args := args)
    (op := op) (c₀ := c₀) (h := h)

theorem numVal_inj {t : NumType} {x y : BitVec t.width} (h : (⟨t, x⟩ : NumVal) = ⟨t, y⟩) :
    x = y :=
  Silmaril.Proofs.Wasm.Auto.VCGen.numVal_inj (t := t) (x := x) (y := y) (h := h)

/-- **A non-trapping conversion whose result is a function of its argument**, every run. -/
theorem HWP.convertInt {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {vs : List Val} {op : ConvertOp}
    {x : BitVec op.source.width} {z : BitVec op.target.width} {rest : List Admin} {Q : Post H}
    (hP : ∀ r, convertP P op x r ↔ r = Silmaril.Wasm.Numerics.convert op x)
    (hz : Silmaril.Wasm.Numerics.convert op x = .ok z)
    (h : HWP P host s f (vals (vs ++ [.num ⟨op.target, z⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨op.source, x⟩]) ++ .plain (.convert op) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.HWP.convertInt (H := H) (P := P) (host := host) (s := s) (f := f)
    (vs := vs) (op := op) (x := x) (z := z) (rest := rest) (Q := Q) (hP := hP) (hz := hz) (h := h)

theorem convertP_wrap {P : Profile} {x : NumValue ConvertOp.wrap.source}
    (r : Except FloatTrap (NumValue ConvertOp.wrap.target)) :
    convertP P .wrap x r ↔ r = Silmaril.Wasm.Numerics.convert .wrap x :=
  Silmaril.Proofs.Wasm.Auto.VCGen.convertP_wrap (P := P) (x := x) (r := r)

theorem convertP_extend {P : Profile} {sx : Signedness} {x : NumValue (ConvertOp.extend sx).source}
    (r : Except FloatTrap (NumValue (ConvertOp.extend sx).target)) :
    convertP P (.extend sx) x r ↔ r = Silmaril.Wasm.Numerics.convert (.extend sx) x :=
  Silmaril.Proofs.Wasm.Auto.VCGen.convertP_extend (P := P) (sx := sx) (x := x) (r := r)

/-- **`i32.wrap_i64`**, every run. -/
theorem HWP.wrap {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {vs : List Val} {x : BitVec 64} {rest : List Admin}
    {Q : Post H} (h : HWP P host s f (vals (vs ++ [.num ⟨.int .i32, x.setWidth 32⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨.int .i64, x⟩]) ++ .plain (.convert .wrap) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.HWP.wrap (H := H) (P := P) (host := host) (s := s) (f := f)
    (vs := vs) (x := x) (rest := rest) (Q := Q) (h := h)

/-- **`i64.extend_i32_s`/`i64.extend_i32_u`**, every run. -/
theorem HWP.extend {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {vs : List Val} {sx : Signedness} {x : BitVec 32}
    {rest : List Admin} {Q : Post H}
    (h : HWP P host s f (vals (vs ++ [.num ⟨.int .i64, match sx with
      | .signed => x.signExtend 64
      | .unsigned => x.setWidth 64⟩]) ++ rest) Q) :
    HWP P host s f (vals (vs ++ [.num ⟨.int .i32, x⟩]) ++ .plain (.convert (.extend sx)) :: rest)
      Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.HWP.extend (H := H) (P := P) (host := host) (s := s) (f := f)
    (vs := vs) (sx := sx) (x := x) (rest := rest) (Q := Q) (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/VCGen/Func.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP FSpecValid FSpecAt bodyPostK callPost)

theorem agree_of_args {S : FnSpec} {ρ ρ' : Env}
    (h : argsOf S ρ = argsOf S ρ') : Agree S.params ρ ρ' :=
  Silmaril.Proofs.Wasm.Auto.VCGen.agree_of_args (S := S) (ρ := ρ) (ρ' := ρ') (h := h)

/-- The postcondition from its condition at the top `n` values of the stack, for every
environment of the same arguments. -/
theorem post_of_vc {F : Fns} {S : FnSpec} (hS : S.wellScoped = true) {ρ ρ₀ : Env} {ls : List SV}
    (hag : Agree S.params ρ ρ₀) (hv : (S.post.subst ls).den F ρ ρ) :
    ∀ ρ', argsOf S ρ₀ = argsOf S ρ' → S.post.den F ρ' (valEnv (dens F ρ ls)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.post_of_vc (F := F) (S := S) (hS := hS) (ρ := ρ) (ρ₀ := ρ₀)
    (ls := ls) (hag := hag) (hv := hv)

theorem intTys?_eq {ts : List ValType} {lts : List IntType} (h : intTys? ts = some lts) :
    ts = lts.map fun t => .num (.int t) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.intTys?_eq (ts := ts) (lts := lts) (h := h)

theorem defaultVal_int (ts : List Validation.CTypeUse) :
    ∀ t : IntType, defaultVal? ((Validation.liftVal (.num (.int t))).substAll ts) =
      some (.num ⟨.int t, 0⟩) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.defaultVal_int (ts := ts)

theorem rel_init {H : Type} {F : Fns} {S : FnSpec}
    {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) (hpre : S.pre.den F ρ₀ ρ₀) :
    Rel F S (S.params ++ lts) ρ₀ s mi ρ₀ (initSt S lts) s
      (Frame.forCall mi (argsOf S ρ₀) code.locals) [] :=
  Silmaril.Proofs.Wasm.Auto.VCGen.rel_init (H := H) (F := F) (S := S) (ρ₀ := ρ₀) (s := s) (mi := mi)
    (code := code) (lts := lts) (hl := hl) (hpre := hpre)

/-- Falling through at the end of the body. -/
theorem bodyPostK_normal {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {a : Nat} {fi : FuncInst H}
    {n : Nat} {k : Nat} {f : Frame} {vs₀ : List Val} {s' : Store H} {F' : Frame}
    (hS : S.wellScoped = true) (hn : S.results.length = n) {vs : List Val}
    (h : Kc F S lt ρ₀ s mi (endVC S) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.normal vs) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.bodyPostK_normal (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s := s) (mi := mi) (a := a) (fi := fi) (n := n) (k := k) (f := f)
    (vs₀ := vs₀) (s' := s') (F' := F') (hS := hS) (hn := hn) (vs := vs) (h := h)

/-- A `return`. -/
theorem bodyPostK_ret {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {a : Nat} {fi : FuncInst H}
    {n : Nat} {k : Nat} {f : Frame} {vs₀ : List Val} {s' : Store H} {F' : Frame}
    (hS : S.wellScoped = true) (hn : S.results.length = n) {vs : List Val}
    (h : Kc F S lt ρ₀ s mi (retVC S) s' F' vs) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F'
      (.ret vs) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.bodyPostK_ret (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s := s) (mi := mi) (a := a) (fi := fi) (n := n) (k := k) (f := f)
    (vs₀ := vs₀) (s' := s') (F' := F') (hS := hS) (hn := hn) (vs := vs) (h := h)

theorem bodyPostK_of_postOf {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s : Store H} {mi : ModuleInst} {a : Nat} {fi : FuncInst H}
    {n : Nat} {k : Nat} {f : Frame} {vs₀ : List Val} {s' : Store H} {F' : Frame}
    (hS : S.wellScoped = true) (hn : S.results.length = n) {o : Outcome}
    (h : postOf F S lt ρ₀ s mi [] (endVC S) s' F' o) :
    bodyPostK P host n f vs₀ (callPost f vs₀ ((fspec F S a fi).post s (argsOf S ρ₀))) k s' F' o :=
  Silmaril.Proofs.Wasm.Auto.VCGen.bodyPostK_of_postOf (H := H) (P := P) (host := host) (F := F)
    (S := S) (lt := lt) (ρ₀ := ρ₀) (s := s) (mi := mi) (a := a) (fi := fi) (n := n) (k := k)
    (f := f) (vs₀ := vs₀) (s' := s') (F' := F') (hS := hS) (hn := hn) (o := o) (h := h)

/-- The body of a well-scoped specification, from the initial state. -/
theorem body_hwp {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {fuel : Nat} {fi : FuncInst H} {code : Func} {lts : List IntType}
    (hl : intTys? code.locals = some lts) (hS : S.wellScoped = true)
    (hvc : AllValid F (gen S (S.params ++ lts) fuel [] (endVC S) 0 code.body (initSt S lts)))
    {s : Store H} {ρ₀ : Env} (hp : S.pre.den F ρ₀ ρ₀) :
    HWP P host s (Frame.forCall fi.module (argsOf S ρ₀) code.locals) (expression code.body)
      (postOf F S (S.params ++ lts) ρ₀ s fi.module [] (endVC S)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.body_hwp (H := H) (P := P) (host := host) (F := F) (S := S)
    (fuel := fuel) (fi := fi) (code := code) (lts := lts) (hl := hl) (hS := hS) (hvc := hvc)
    (s := s) (ρ₀ := ρ₀) (hp := hp)

/-- **Soundness of the reflective generator for functions.** Valid conditions give the every-run
specification `fspec`: at every profile and for every host relation, a call with arguments
satisfying the precondition returns results satisfying the postcondition, without trapping and
leaving the store unchanged. -/
theorem genFunc_sound {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {fuel a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hps : S.params.length = ps.length) (hrs : S.results.length = rs.length)
    (hvc : AllValid F (genFunc S code fuel)) :
    FSpecValid P host a (fspec F S a fi) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.genFunc_sound (H := H) (P := P) (host := host) (F := F) (S := S)
    (fuel := fuel) (a := a) (fi := fi) (code := code) (ps := ps) (rs := rs) (hcode := hcode)
    (he := he) (hps := hps) (hrs := hrs) (hvc := hvc)

end

section
-- from Silmaril/Proofs/Wasm/Auto/VCGen/Sound.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp)
open Silmaril.Wasm.Logic.VC (ctl labelQ loopQ enterVC hwp_block hwp_loop ctl_block ctl_loop ctl_if ctl_br
  ctl_brIf ctl_select ctl_ret PlainCtl)

theorem Rel.pc {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) : ∀ φ ∈ σ.pc, φ.den F ρ ρ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Rel.pc (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀)
    (m := m) (ρ := ρ) (σ := σ) (s := s) (f := f) (rs := rs) (h := h)

theorem Rel.update {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {ρ : Env} {σ σ' : SSt} {s : Store H} {f : Frame} {rs rs' : List Val}
    (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hl : σ'.locals = σ.locals)
    (hrs : rs' = dens F ρ σ'.stack) (hpc : ∀ φ ∈ σ'.pc, φ.den F ρ ρ) :
    Rel F S lt ρ₀ s₀ m ρ σ' s f rs' :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Rel.update (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀)
    (s₀ := s₀) (m := m) (ρ := ρ) (σ := σ) (σ' := σ') (s := s) (f := f) (rs := rs) (rs' := rs')
    (h := h) (hl := hl) (hrs := hrs) (hpc := hpc)

theorem Rel.pcCons {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val} {st : List SV}
    {φ : Fm} (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hφ : φ.den F ρ ρ) :
    Rel F S lt ρ₀ s₀ m ρ { σ with stack := st, pc := φ :: σ.pc } s f (dens F ρ st) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.Rel.pcCons (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀)
    (s₀ := s₀) (m := m) (ρ := ρ) (σ := σ) (s := s) (f := f) (rs := rs) (st := st) (φ := φ) (h := h)
    (hφ := hφ)

theorem scoped_inv {S : FnSpec} (hS : S.wellScoped = true) (j : Nat) :
    (S.inv.getD j .tt).scoped S.params = true :=
  Silmaril.Proofs.Wasm.Auto.VCGen.scoped_inv (S := S) (hS := hS) (j := j)

theorem den_invAt {F : Fns} {S : FnSpec} (ρ : Env) (j : Nat) (ls : List SV) :
    (invAt S j ls).den F ρ ρ ↔ (S.inv.getD j .tt).den F ρ (valEnv (dens F ρ ls)) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.den_invAt (F := F) (S := S) (ρ := ρ) (j := j) (ls := ls)

/-- **Re-establishing a loop invariant** from its condition at the current locals. -/
theorem invC_of {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} (hS : S.wellScoped = true) {j : Nat} {ρ : Env} {σ : SSt} {s : Store H}
    {f : Frame} {rs : List Val} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hI : (invAt S j σ.locals).den F ρ ρ) : InvC F S lt ρ₀ s₀ m j s f [] :=
  Silmaril.Proofs.Wasm.Auto.VCGen.invC_of (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀)
    (m := m) (hS := hS) (j := j) (ρ := ρ) (σ := σ) (s := s) (f := f) (rs := rs) (hR := hR)
    (hI := hI)

theorem postOf_blk {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {n : Nat} {K kont : SSt → List Fm} {L : List Lbl} {s : Store H} {f : Frame}
    {o : Outcome} (h : postOf F S lt ρ₀ s₀ m (.blk n K :: L) K s f o) :
    labelQ n [] (Kc F S lt ρ₀ s₀ m K) (postOf F S lt ρ₀ s₀ m L kont) s f o :=
  Silmaril.Proofs.Wasm.Auto.VCGen.postOf_blk (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀)
    (s₀ := s₀) (m := m) (n := n) (K := K) (kont := kont) (L := L) (s := s) (f := f) (o := o)
    (h := h)

theorem postOf_lp {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {j : Nat} {K kont : SSt → List Fm} {L : List Lbl} {f₀ : Frame}
    (hm : f₀.module = m) {s : Store H} {f : Frame} {o : Outcome}
    (h : postOf F S lt ρ₀ s₀ m (.lp j :: L) K s f o) :
    loopQ 0 [] (fun s' f' a' => InvC F S lt ρ₀ s₀ m j s' f' a' ∧ f'.module = f₀.module)
      (Kc F S lt ρ₀ s₀ m K) (postOf F S lt ρ₀ s₀ m L kont) s f o :=
  Silmaril.Proofs.Wasm.Auto.VCGen.postOf_lp (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀)
    (m := m) (j := j) (K := K) (kont := kont) (L := L) (f₀ := f₀) (hm := hm) (s := s) (f := f)
    (o := o) (h := h)

theorem enterVC_nil {f : Frame} {bt : BlockType} {n : Nat}
    {B : List Val → List Val → Nat → Nat → Prop} (hn : arity bt = some n) (h : B [] [] 0 n) :
    enterVC f bt [] B :=
  Silmaril.Proofs.Wasm.Auto.VCGen.enterVC_nil (f := f) (bt := bt) (n := n) (B := B) (hn := hn) (h := h)

/-- A block (of `block` or `if`) entered with an empty stack. -/
theorem sound_blockBody {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}
    {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType}
    {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm} {k k' : Nat} {σ : SSt}
    {ρ : Env} {s : Store H} {f : Frame} (hn : arity bt = some n)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f [])
    (hv : AllValid F (gen S lt fuel (.blk n (gen S lt fuel L kont k' r) :: L)
      (gen S lt fuel L kont k' r) k b σ)) :
    HWP P host s f (vals [] ++ .plain (.block bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.sound_blockBody (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (ih := ih) (bt := bt) (n := n) (b := b)
    (r := r) (L := L) (kont := kont) (k := k) (k' := k') (σ := σ) (ρ := ρ) (s := s) (f := f)
    (hn := hn) (hR := hR) (hv := hv)

/-- A branch to a block: the continuation on the top `n` values. -/
theorem brBlk_post {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {L : List Lbl} {kont : SSt → List Fm} {l n : Nat} {K : SSt → List Fm}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val} (hl : L[l]? = some (.blk n K))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hn : n ≤ σ.stack.length)
    (hv : AllValid F (K { σ with stack := σ.stack.take n })) :
    postOf F S lt ρ₀ s₀ m L kont s f (.br l rs.reverse) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.brBlk_post (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀)
    (s₀ := s₀) (m := m) (L := L) (kont := kont) (l := l) (n := n) (K := K) (σ := σ) (ρ := ρ)
    (s := s) (f := f) (rs := rs) (hl := hl) (hR := hR) (hn := hn) (hv := hv)

/-- A branch to label `l`. -/
theorem brTo_post {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} (hS : S.wellScoped = true) {L : List Lbl} {kont : SSt → List Fm} {l : Nat}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hv : AllValid F (brTo S L l σ)) :
    postOf F S lt ρ₀ s₀ m L kont s f (.br l rs.reverse) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.brTo_post (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀)
    (m := m) (hS := hS) (L := L) (kont := kont) (l := l) (σ := σ) (ρ := ρ) (s := s) (f := f)
    (rs := rs) (hR := hR) (hv := hv)

theorem rs_nil {H : Type} {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H}
    {m : ModuleInst} {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = []) : rs = [] :=
  Silmaril.Proofs.Wasm.Auto.VCGen.rs_nil (H := H) (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀)
    (m := m) (ρ := ρ) (σ := σ) (s := s) (f := f) (rs := rs) (hR := hR) (hst := hst)

theorem sound_loop {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}
    (hS : S.wellScoped = true) {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {bt : BlockType} {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k : Nat} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} (hn : arity bt = some n)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f [])
    (hv : AllValid F (vc σ (invAt S k σ.locals) ::
      gen S lt fuel (.lp k :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r) (k + 1) b
        (havoc S lt k))) :
    HWP P host s f (vals [] ++ .plain (.loop bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.sound_loop (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (hS := hS) (fuel := fuel) (ih := ih) (bt := bt)
    (n := n) (b := b) (r := r) (L := L) (kont := kont) (k := k) (σ := σ) (ρ := ρ) (s := s) (f := f)
    (hn := hn) (hR := hR) (hv := hv)

theorem cons_block {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val}
    (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType} {b : List Instr}
    (hc : ctl i = .block bt b) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_block (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (ih := ih) (bt := bt) (b := b)
    (hc := hc) (hR := hR) (hv := hv)

theorem cons_loop {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (hS : S.wellScoped = true) (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_loop (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (hS := hS) (ih := ih)
    (bt := bt) (b := b) (hc := hc) (hR := hR) (hv := hv)

theorem cons_if {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val}
    (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType} {b₁ b₂ : List Instr}
    (hc : ctl i = .if_ bt b₁ b₂) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_if (H := H) (P := P) (host := host) (F := F) (S := S) (lt := lt)
    (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k) (i := i) (r := r)
    (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (ih := ih) (bt := bt) (b₁ := b₁) (b₂ := b₂)
    (hc := hc) (hR := hR) (hv := hv)

theorem cons_br {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (hS : S.wellScoped = true) {l : LabelIdx} (hc : ctl i = .br l)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_br (H := H) (P := P) (host := host) (F := F) (S := S) (lt := lt)
    (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k) (i := i) (r := r)
    (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (hS := hS) (l := l) (hc := hc) (hR := hR)
    (hv := hv)

theorem cons_brIf {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (hS : S.wellScoped = true) (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {l : LabelIdx} (hc : ctl i = .brIf l) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_brIf (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (hS := hS) (ih := ih) (l := l)
    (hc := hc) (hR := hR) (hv := hv)

/-- `select` on the stack `c :: v₂ :: v₁ :: st` (top first). -/
theorem sound_select {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame}
    {rs : List Val} (ih : IH F S lt ρ₀ s₀ m P host fuel) {ts : Option (List ValType)}
    {c : Tm .i32} {v₁ v₂ v : SV} {st : List SV} (hst : σ.stack = .i32 c :: v₂ :: v₁ :: st)
    (hsel : selV c v₁ v₂ = some v) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt fuel L kont k r { σ with stack := v :: st })) :
    HWP P host s f (vals rs.reverse ++ .plain (.select ts) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.sound_select (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (ih := ih) (ts := ts) (c := c)
    (v₁ := v₁) (v₂ := v₂) (v := v) (st := st) (hst := hst) (hsel := hsel) (hR := hR) (hv := hv)

theorem cons_select {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (ih : IH F S lt ρ₀ s₀ m P host fuel) (hc : ctl i = .select)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_select (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (ih := ih) (hc := hc)
    (hR := hR) (hv := hv)

theorem cons_ret {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (hc : ctl i = .ret) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_ret (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (hc := hc) (hR := hR)
    (hv := hv)

theorem cons_plain {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {i : Instr} {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H}
    {f : Frame} {rs : List Val} (ih : IH F S lt ρ₀ s₀ m P host fuel) (hc : PlainCtl (ctl i))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.cons_plain (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (i := i) (r := r) (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (ih := ih) (hc := hc)
    (hR := hR) (hv := hv)

theorem sound_nil {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} {fuel : Nat} {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k [] σ)) :
    HWP P host s f (vals rs.reverse ++ expression []) (postOf F S lt ρ₀ s₀ m L kont) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.sound_nil (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (fuel := fuel) (L := L) (kont := kont) (k := k)
    (σ := σ) (ρ := ρ) (s := s) (f := f) (rs := rs) (hR := hR) (hv := hv)

/-- **Soundness of the generator**, at every `fuel`. -/
theorem gen_sound {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst} (hS : S.wellScoped = true) : ∀ fuel, IH F S lt ρ₀ s₀ m P host fuel :=
  Silmaril.Proofs.Wasm.Auto.VCGen.gen_sound (H := H) (P := P) (host := host) (F := F) (S := S)
    (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) (hS := hS)

end

section
-- from Silmaril/Proofs/Wasm/Auto/VCGen/Step.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec1 popInt popV localVal?)
open Silmaril.Wasm.Logic.Hoare (HWP)

theorem popInt_num (t : IntType) (x : BitVec t.width) (rs : List Val) :
    popInt t (.num ⟨.int t, x⟩ :: rs) = some (x, rs) :=
  Silmaril.Proofs.Wasm.Auto.VCGen.popInt_num (t := t) (x := x) (rs := rs)

/-- The frame a symbolic state denotes, from its locals. -/
theorem frame_eq {F : Fns} {σ : SSt} {ρ : Env} {f : Frame}
    (hf : f.locals = locs F ρ σ.locals) : f = ⟨locs F ρ σ.locals, f.module⟩ :=
  Silmaril.Proofs.Wasm.Auto.VCGen.frame_eq (F := F) (σ := σ) (ρ := ρ) (f := f) (hf := hf)

theorem wp_localGet {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {σ : SSt} {σ' : SSt}
    {side : List Fm} {ρ : Env} {s : Store H} {f : Frame} {rest : List Admin} {Q : Post H}
    {x : LocalIdx} (h : step1 (.localGet x) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.localGet x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.wp_localGet (H := H) (P := P) (host := host) (F := F) (σ := σ)
    (σ' := σ') (side := side) (ρ := ρ) (s := s) (f := f) (rest := rest) (Q := Q) (x := x) (h := h)
    (hf := hf) (hk := hk)

theorem localSet_inv {σ : SSt} {σ' : SSt} {side : List Fm}
    {x : LocalIdx} (h : step1 (.localSet x) σ = some (σ', side)) :
    ∃ v st, σ.stack = v :: st ∧ x.toNat < σ.locals.length ∧ [] = side ∧
      { σ with stack := st, locals := σ.locals.set x.toNat v } = σ' :=
  Silmaril.Proofs.Wasm.Auto.VCGen.localSet_inv (σ := σ) (σ' := σ') (side := side) (x := x) (h := h)

theorem localTee_inv {σ : SSt} {σ' : SSt} {side : List Fm}
    {x : LocalIdx} (h : step1 (.localTee x) σ = some (σ', side)) :
    ∃ v st, σ.stack = v :: st ∧ x.toNat < σ.locals.length ∧ [] = side ∧
      { σ with locals := σ.locals.set x.toNat v } = σ' :=
  Silmaril.Proofs.Wasm.Auto.VCGen.localTee_inv (σ := σ) (σ' := σ') (side := side) (x := x) (h := h)

theorem wp_localSet {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {σ : SSt} {σ' : SSt}
    {side : List Fm} {ρ : Env} {s : Store H} {f : Frame} {rest : List Admin} {Q : Post H}
    {x : LocalIdx} (h : step1 (.localSet x) σ = some (σ', side))
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.localSet x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.wp_localSet (H := H) (P := P) (host := host) (F := F) (σ := σ)
    (σ' := σ') (side := side) (ρ := ρ) (s := s) (f := f) (rest := rest) (Q := Q) (x := x) (h := h)
    (hf := hf) (hk := hk)

theorem wp_intBinOp {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {σ : SSt} {σ' : SSt}
    {side : List Fm} {ρ : Env} {s : Store H} {f : Frame} {rest : List Admin} {Q : Post H}
    {t : IntType} {op : IntBinOp} (h : step1 (.intBinOp t op) σ = some (σ', side))
    (hs : ∀ φ ∈ side, φ.den F ρ ρ) (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain (.intBinOp t op) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.wp_intBinOp (H := H) (P := P) (host := host) (F := F) (σ := σ)
    (σ' := σ') (side := side) (ρ := ρ) (s := s) (f := f) (rest := rest) (Q := Q) (t := t) (op := op)
    (h := h) (hs := hs) (hf := hf) (hk := hk)

/-- **A straight-line instruction**, every run. -/
theorem step1_wp {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns}
    {i : Instr} {σ σ' : SSt} {side : List Fm} {ρ : Env} {s : Store H} {f : Frame}
    {rest : List Admin} {Q : Post H}
    (h : step1 i σ = some (σ', side)) (hs : ∀ φ ∈ side, φ.den F ρ ρ)
    (hf : f.locals = locs F ρ σ.locals)
    (hk : HWP P host s ⟨locs F ρ σ'.locals, f.module⟩ (vals (dens F ρ σ'.stack).reverse ++ rest) Q) :
    HWP P host s f (vals (dens F ρ σ.stack).reverse ++ .plain i :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.VCGen.step1_wp (H := H) (P := P) (host := host) (F := F) (i := i) (σ := σ)
    (σ' := σ') (side := side) (ρ := ρ) (s := s) (f := f) (rest := rest) (Q := Q) (h := h) (hs := hs)
    (hf := hf) (hk := hk)

end

end Silmaril.Wasm.Auto.VCGen

namespace Silmaril.Wasm.Auto.VCGen

theorem ult_iff {n : Nat} (x y : BitVec n) : x.ult y = true ↔ x.toNat < y.toNat := by
  simp [BitVec.ult]

theorem ule_iff {n : Nat} (x y : BitVec n) : x.ule y = true ↔ x.toNat ≤ y.toNat := by
  simp [BitVec.ule]

theorem slt_iff {n : Nat} (x y : BitVec n) : x.slt y = true ↔ x.toInt < y.toInt := by
  simp [BitVec.slt]

theorem sle_iff {n : Nat} (x y : BitVec n) : x.sle y = true ↔ x.toInt ≤ y.toInt := by
  simp [BitVec.sle]

open Lean Elab Tactic Meta in
/-- Compute the conditions of a closed list `l` in a goal `AllValid F l` (see the module
docstring). -/
elab "vcgen_reduce" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (fns, e) := tgt.app2? ``AllValid
      | throwError "vcgen_reduce: the goal is not `AllValid F l`"
    if e.hasFVar || e.hasMVar then
      throwError "vcgen_reduce: the list of conditions must be closed"
    let e' ← withTransparency .all <| reduce e (skipTypes := true) (skipProofs := true)
    let eqTy ← mkEq e e'
    let lvls := (collectLevelParams {} eqTy).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter lvls.contains
    let n ← withOptions (Elab.async.set · false) do mkAuxLemma lemmaLevels eqTy (← mkEqRefl e')
    let pf := mkConst n (lemmaLevels.map .param)
    let g' ← g.replaceTargetEq (mkApp2 (mkConst ``AllValid) fns e')
      (← mkCongrArg (mkApp (mkConst ``AllValid) fns) pf)
    replaceMainGoal [g']

/-- Unfold the denotation of computed conditions (see the module docstring). -/
macro "vcgen_den" : tactic => `(tactic| (
  simp only [Silmaril.Wasm.Auto.VCGen.AllValid, Silmaril.Wasm.Auto.VCGen.Valid,
    Silmaril.Wasm.Auto.VCGen.Fm.den, Silmaril.Wasm.Auto.VCGen.Tm.den, Silmaril.Wasm.Auto.VCGen.Env.get,
    Silmaril.Wasm.Auto.VCGen.Fns.app1, Silmaril.Wasm.Auto.VCGen.Fns.app2,
    Silmaril.Wasm.Auto.VCGen.litT, Silmaril.Wasm.Auto.VCGen.unT, Silmaril.Wasm.Auto.VCGen.binT,
    Silmaril.Wasm.Auto.VCGen.relP, Silmaril.Wasm.Auto.VCGen.unW, Silmaril.Wasm.Auto.VCGen.binW,
    Silmaril.Wasm.Auto.VCGen.relW, Silmaril.Wasm.Auto.VCGen.relV_ne_zero,
    Silmaril.Wasm.Auto.VCGen.eqzV_ne_zero, Silmaril.Wasm.Auto.VCGen.relV, Silmaril.Wasm.Auto.VCGen.eqzV,
    Silmaril.Wasm.Auto.VCGen.bool32_bne_zero, Silmaril.Wasm.Auto.VCGen.relB, Bool.cond_decide,
    Silmaril.Wasm.Auto.VCGen.nz32, Silmaril.Wasm.Auto.VCGen.iteT, Silmaril.Wasm.Auto.VCGen.wrapW, Silmaril.Wasm.Auto.VCGen.extSW,
    Silmaril.Wasm.Auto.VCGen.extUW,
    cond_eq_ite, bne_iff_ne, beq_iff_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    and_true, true_implies, true_and]
  try simp only [cond_eq_ite, beq_iff_eq, bne_iff_ne, Silmaril.Wasm.Numerics.bool32,
    Silmaril.Wasm.Auto.VCGen.ult_iff, Silmaril.Wasm.Auto.VCGen.ule_iff, Silmaril.Wasm.Auto.VCGen.slt_iff,
    Silmaril.Wasm.Auto.VCGen.sle_iff]))

open Lean Meta in
/-- The index of an atom `ρ.e32 i` (`(false, i)`) or `ρ.e64 i` (`(true, i)`). -/
meta def envAtom? (ρ : Lean.Expr) (e : Lean.Expr) : Option (Bool × Nat) :=
  if e.isAppOfArity ``Env.e32 2 && e.appFn!.appArg! == ρ then
    (e.appArg!.rawNatLit? <|> e.appArg!.nat?).map ((false, ·))
  else if e.isAppOfArity ``Env.e64 2 && e.appFn!.appArg! == ρ then
    (e.appArg!.rawNatLit? <|> e.appArg!.nat?).map ((true, ·))
  else none

open Lean Meta in
/-- The atoms of an expression, one per index, with a representative. -/
meta partial def envAtoms (ρ : Lean.Expr) (e : Lean.Expr)
    (acc : Array ((Bool × Nat) × Lean.Expr)) :
    Array ((Bool × Nat) × Lean.Expr) :=
  match envAtom? ρ e with
  | some k => if acc.any (·.1 == k) then acc else acc.push (k, e)
  | none =>
    match e with
    | .app f a => envAtoms ρ a (envAtoms ρ f acc)
    | .lam _ t b _ | .forallE _ t b _ => envAtoms ρ b (envAtoms ρ t acc)
    | .letE _ t v b _ => envAtoms ρ b (envAtoms ρ v (envAtoms ρ t acc))
    | .mdata _ b => envAtoms ρ b acc
    | .proj _ _ b => envAtoms ρ b acc
    | _ => acc

open Lean Elab Tactic Meta in
/-- On a goal `∀ ρ : Env, P`, name each value `ρ.e32 i` as `vi` and `ρ.e64 i` as `wi`: the goal
becomes `∀ vi … wj, P'` with the values replaced syntactically (no unification), then the names
are introduced. -/
elab "vcgen_vars" : tactic => do
  liftMetaTactic fun g => do
    let (ρ, g) ← g.intro `ρ
    g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let atoms := envAtoms (.fvar ρ) tgt #[]
      let names := atoms.map fun ((b, i), _) =>
        Name.mkSimple (if b then s!"w{i}" else s!"v{i}")
      let decls := (atoms.zip names).map fun ((_, e), n) => (n, fun _ => inferType e)
      let tgt' ← withLocalDeclsD decls fun xs => do
        let body := tgt.replace fun e =>
          match envAtom? (.fvar ρ) e with
          | some k => (atoms.findIdx? (·.1 == k)).map (xs[·]!)
          | none => none
        mkForallFVars xs body
      let g' ← mkFreshExprSyntheticOpaqueMVar tgt' (← g.getTag)
      g.assign (mkAppN g' (atoms.map (·.2)))
      let (_, g'') ← g'.mvarId!.introN atoms.size names.toList
      let g'' ← g''.tryClear ρ
      return [g'']

/-- Compute the conditions and state each as a goal (see the module docstring). -/
macro "vcgen" : tactic =>
  `(tactic| (vcgen_reduce; vcgen_den; (try and_intros); all_goals try vcgen_vars))

end Silmaril.Wasm.Auto.VCGen
