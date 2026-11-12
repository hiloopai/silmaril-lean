module

public import Silmaril.Proofs.Wasm.Auto.VCGen.Step
public import Silmaril.Wasm.Logic.VC.Thms

/-!
# Soundness of the reflective VC generator

`gen_sound`: if every condition of `gen S lt fuel L kont k is σ` is valid, then the code `is`,
run from any concrete configuration that `σ` denotes (`Rel`: same store `s₀`, module `m`,
locals and stack the symbolic ones denote in some environment `ρ` agreeing with `ρ₀` on the
parameters and satisfying the path condition), satisfies the every-run weakest precondition
`HWP` with the postcondition `postOf L kont`: a fall-through or branch continues with a
continuation whose conditions are valid (`Kc`), a branch back to loop `j` re-establishes its
concrete invariant `InvC j`, a `return` satisfies `retVC`, and nothing traps or throws.

By induction on `fuel`, one lemma per construct; `block`, `loop`, `if` reuse the rules
`Silmaril.Wasm.Logic.VC.hwp_block`/`hwp_loop` of the existing (non-reflective) generator. The loop
invariant `InvC j` is the set of configurations denoted by the loop-head state `havoc S lt j`;
`invC_of` re-establishes it from the condition `invAt S j σ.locals` by overriding the fresh
variables (`ovr`), which needs the annotations to mention parameters only (`FnSpec.wellScoped`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp)
open Silmaril.Wasm.Logic.VC (ctl labelQ loopQ enterVC hwp_block hwp_loop ctl_block ctl_loop ctl_if ctl_br
  ctl_brIf ctl_select ctl_ret PlainCtl)

variable {H : Type} {P : Profile} {host : HostSemantics H}

variable {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

/-! ## The relation -/

theorem Rel.pc {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) : ∀ φ ∈ σ.pc, φ.den F ρ ρ := h.2.2.2.2.2.2

theorem Rel.update {ρ : Env} {σ σ' : SSt} {s : Store H} {f : Frame} {rs rs' : List Val}
    (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hl : σ'.locals = σ.locals)
    (hrs : rs' = dens F ρ σ'.stack) (hpc : ∀ φ ∈ σ'.pc, φ.den F ρ ρ) :
    Rel F S lt ρ₀ s₀ m ρ σ' s f rs' := by
  obtain ⟨h₁, h₂, h₃, -, h₅, h₆, -⟩ := h
  exact ⟨h₁, h₂, hl ▸ h₃, hrs, hl ▸ h₅, h₆, hpc⟩

theorem Rel.pcCons {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val} {st : List SV}
    {φ : Fm} (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hφ : φ.den F ρ ρ) :
    Rel F S lt ρ₀ s₀ m ρ { σ with stack := st, pc := φ :: σ.pc } s f (dens F ρ st) :=
  (Rel.update h) rfl rfl fun ψ hψ => by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact (Rel.pc h) ψ hψ

/-! ## Loop invariants -/

theorem agree_ovr {ps : List IntType} {ρ : Env} {ls : List SV} :
    Agree ps (ovr F ps.length ρ ls) ρ := by
  intro i t hi
  have hlt : ¬ ps.length ≤ i := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  cases t <;> simp [Env.get, ovr, hlt] <;> rfl

theorem dens_havoc {p : Nat} {ρ : Env} {ls : List SV} :
    dens F (ovr F p ρ ls) (havocLocals p (ls.map SV.ty)) = dens F ρ ls := by
  apply List.ext_getElem
  · simp [havocLocals]
  · intro j h₁ h₂
    have hj : j < ls.length := by simpa using h₂
    simp only [dens, havocLocals, List.getElem_map, List.getElem_mapIdx]
    rw [SV.den_of]
    simp only [Tm.den]
    rw [List.getElem_map]
    rcases hv : ls[j] with a | a
    · have hget : ls[j]? = some (.i32 a) := by rw [List.getElem?_eq_getElem hj, hv]
      simp [SV.ty, SV.den, Env.get, ovr, hget]
    · have hget : ls[j]? = some (.i64 a) := by rw [List.getElem?_eq_getElem hj, hv]
      simp [SV.ty, SV.den, Env.get, ovr, hget]

theorem havocLocals_ty (p : Nat) (lt : List IntType) : (havocLocals p lt).map SV.ty = lt := by
  apply List.ext_getElem
  · simp [havocLocals]
  · intro j h₁ h₂
    simp [havocLocals, SV.ty_of]

theorem scoped_inv (hS : S.wellScoped = true) (j : Nat) :
    (S.inv.getD j .tt).scoped S.params = true := by
  simp only [FnSpec.wellScoped, Bool.and_eq_true, List.all_eq_true] at hS
  rw [List.getD_eq_getElem?_getD]
  rcases h : S.inv[j]? with _ | φ
  · rfl
  · exact hS.2 φ (List.mem_of_getElem? h)

theorem den_invAt (ρ : Env) (j : Nat) (ls : List SV) :
    (invAt S j ls).den F ρ ρ ↔ (S.inv.getD j .tt).den F ρ (valEnv (dens F ρ ls)) := by
  rw [invAt, Fm.den_subst, locEnv_eq_valEnv]

/-- **Re-establishing a loop invariant** from its condition at the current locals. -/
theorem invC_of (hS : S.wellScoped = true) {j : Nat} {ρ : Env} {σ : SSt} {s : Store H}
    {f : Frame} {rs : List Val} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hI : (invAt S j σ.locals).den F ρ ρ) : InvC F S lt ρ₀ s₀ m j s f [] := by
  obtain ⟨h₁, h₂, h₃, -, h₅, h₆, -⟩ := hR
  refine ⟨rfl, ovr F S.params.length ρ σ.locals, h₁, h₂, ?_, rfl, havocLocals_ty _ _,
    Agree.trans agree_ovr h₆, ?_⟩
  · rw [h₃, ← h₅]
    have := congrArg (List.map some) (dens_havoc (F := F) (p := S.params.length) (ρ := ρ)
      (ls := σ.locals))
    simpa [locs, dens, havoc, Function.comp_def] using this.symm
  · intro φ hφ
    simp only [havoc, List.mem_singleton] at hφ
    subst hφ
    rw [den_invAt, ← h₅, dens_havoc]
    exact (Fm.den_scoped agree_ovr _ _ (scoped_inv hS j)).mpr ((den_invAt ρ j σ.locals).mp hI)

/-! ## Labels -/

theorem kc_hwp {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m P host fuel) {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {r : List Instr} :
    ∀ s f vs, Kc F S lt ρ₀ s₀ m (gen S lt fuel L kont k r) s f vs →
      HWP P host s f (vals vs ++ expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  rintro s f vs ⟨ρ, σ, hR, hv⟩
  simpa using ih L kont k r σ ρ s f vs.reverse hR hv

theorem postOf_blk {n : Nat} {K kont : SSt → List Fm} {L : List Lbl} {s : Store H} {f : Frame}
    {o : Outcome} (h : postOf F S lt ρ₀ s₀ m (.blk n K :: L) K s f o) :
    labelQ n [] (Kc F S lt ρ₀ s₀ m K) (postOf F S lt ρ₀ s₀ m L kont) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  all_goals exact h.elim

theorem postOf_lp {j : Nat} {K kont : SSt → List Fm} {L : List Lbl} {f₀ : Frame}
    (hm : f₀.module = m) {s : Store H} {f : Frame} {o : Outcome}
    (h : postOf F S lt ρ₀ s₀ m (.lp j :: L) K s f o) :
    loopQ 0 [] (fun s' f' a' => InvC F S lt ρ₀ s₀ m j s' f' a' ∧ f'.module = f₀.module)
      (Kc F S lt ρ₀ s₀ m K) (postOf F S lt ρ₀ s₀ m L kont) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · simpa [loopQ, postOf] using h
  · obtain ⟨-, ρ, hR⟩ := (h : InvC F S lt ρ₀ s₀ m j s f [])
    refine ⟨Nat.zero_le _, ⟨by simp, ρ, hR⟩, ?_⟩
    rw [hR.2.1, hm]
  · simpa [loopQ, postOf] using h
  · simpa [loopQ, postOf] using h
  all_goals exact h.elim

theorem enterVC_nil {f : Frame} {bt : BlockType} {n : Nat}
    {B : List Val → List Val → Nat → Nat → Prop} (hn : arity bt = some n) (h : B [] [] 0 n) :
    enterVC f bt [] B := by
  cases bt <;> simp only [arity, Option.some.injEq, reduceCtorEq] at hn <;> subst hn <;>
    simpa [enterVC, ModuleInst.blockType?] using h

/-- A block (of `block` or `if`) entered with an empty stack. -/
theorem sound_blockBody {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType}
    {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm} {k k' : Nat} {σ : SSt}
    {ρ : Env} {s : Store H} {f : Frame} (hn : arity bt = some n)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f [])
    (hv : AllValid F (gen S lt fuel (.blk n (gen S lt fuel L kont k' r) :: L)
      (gen S lt fuel L kont k' r) k b σ)) :
    HWP P host s f (vals [] ++ .plain (.block bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) := by
  refine hwp_block (kc_hwp (k := k') ih) (enterVC_nil hn ?_)
  exact (ih _ _ k b σ ρ s f [] hR hv).mono fun _ _ _ h => postOf_blk h

/-- A branch to a block: the continuation on the top `n` values. -/
theorem brBlk_post {L : List Lbl} {kont : SSt → List Fm} {l n : Nat} {K : SSt → List Fm}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val} (hl : L[l]? = some (.blk n K))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hn : n ≤ σ.stack.length)
    (hv : AllValid F (K { σ with stack := σ.stack.take n })) :
    postOf F S lt ρ₀ s₀ m L kont s f (.br l rs.reverse) := by
  have hrs : rs = dens F ρ σ.stack := hR.2.2.2.1
  have hlen : rs.length = σ.stack.length := by rw [hrs, List.length_map]
  have htake : (rs.reverse.drop (rs.reverse.length - n)).reverse = dens F ρ (σ.stack.take n) := by
    rw [List.reverse_drop, List.reverse_reverse, List.length_reverse,
      Nat.sub_sub_self (by rw [hlen]; exact hn), hrs]
    simp [dens, List.map_take]
  show (match L[l]? with
    | some (.blk n K) => n ≤ rs.reverse.length ∧ Kc F S lt ρ₀ s₀ m K s f (rs.reverse.drop _)
    | some (.lp j) => InvC F S lt ρ₀ s₀ m j s f []
    | none => False)
  rw [hl]
  exact ⟨by rw [List.length_reverse, hlen]; exact hn, ρ, _,
    Rel.update (σ' := { σ with stack := σ.stack.take n }) hR rfl htake (Rel.pc (σ := σ) hR), hv⟩

/-- A branch to label `l`. -/
theorem brTo_post (hS : S.wellScoped = true) {L : List Lbl} {kont : SSt → List Fm} {l : Nat}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hv : AllValid F (brTo S L l σ)) :
    postOf F S lt ρ₀ s₀ m L kont s f (.br l rs.reverse) := by
  unfold brTo at hv
  split at hv
  next n K hl =>
    split at hv
    next hn => exact brBlk_post hl hR hn hv
    next => exact (not_bad hv (Rel.pc hR)).elim
  next j hl =>
    show (match L[l]? with
      | some (.blk n K) => n ≤ rs.reverse.length ∧ Kc F S lt ρ₀ s₀ m K s f (rs.reverse.drop _)
      | some (.lp j) => InvC F S lt ρ₀ s₀ m j s f []
      | none => False)
    rw [hl]
    exact invC_of hS hR (vc_holds hv.1 (Rel.pc hR))
  next => exact (not_bad hv (Rel.pc hR)).elim

/-! ## The generator -/

theorem rs_nil {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = []) : rs = [] := by
  rw [hR.2.2.2.1, hst]
  rfl

theorem sound_loop (hS : S.wellScoped = true) {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {bt : BlockType} {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k : Nat} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} (hn : arity bt = some n)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f [])
    (hv : AllValid F (vc σ (invAt S k σ.locals) ::
      gen S lt fuel (.lp k :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r) (k + 1) b
        (havoc S lt k))) :
    HWP P host s f (vals [] ++ .plain (.loop bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) := by
  refine hwp_loop (I := InvC F S lt ρ₀ s₀ m k) (kc_hwp (k := k + 1 + nloops fuel b) ih)
    (enterVC_nil hn ⟨invC_of hS hR (vc_holds hv.1 (Rel.pc hR)), ?_⟩)
  rintro s' f' a' ⟨rfl, ρ', hR'⟩ - -
  exact (ih _ _ _ b _ ρ' s' f' [] hR' hv.2).mono fun _ _ _ h => postOf_lp hR.2.1 h

section Cases

variable {fuel : Nat} {L : List Lbl} {kont : SSt → List Fm} {k : Nat} {i : Instr}
  {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}

theorem cons_block (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType} {b : List Instr}
    (hc : ctl i = .block bt b) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n hn hst =>
    rw [rs_nil hR hst, ctl_block hc]
    exact sound_blockBody ih hn (rs_nil hR hst ▸ hR) hv
  next => exact (not_bad hv (Rel.pc hR)).elim

theorem cons_loop (hS : S.wellScoped = true) (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n hn hst =>
    rw [rs_nil hR hst, ctl_loop hc]
    exact sound_loop hS ih hn (rs_nil hR hst ▸ hR) hv
  next => exact (not_bad hv (Rel.pc hR)).elim

theorem cons_if (ih : IH F S lt ρ₀ s₀ m P host fuel) {bt : BlockType} {b₁ b₂ : List Instr}
    (hc : ctl i = .if_ bt b₁ b₂) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n c hn hst =>
    have hv' := allValid_append.mp hv
    have hrs : rs.reverse = [] ++ [Val.i32 (c.den F ρ ρ)] := by
      rw [hR.2.2.2.1, hst]
      rfl
    rw [hrs, ctl_if hc]
    refine Silmaril.Wasm.Logic.Hoare.HWP.if_ (fun h₁ => ?_) (fun h₂ => ?_)
    · exact sound_blockBody ih hn ((Rel.pcCons hR) ((den_condF ρ ρ c).mpr h₁)) hv'.1
    · exact sound_blockBody ih hn ((Rel.pcCons hR) ((den_ncondF ρ ρ c).mpr h₂)) hv'.2
  next => exact (not_bad hv (Rel.pc hR)).elim

theorem cons_br (hS : S.wellScoped = true) {l : LabelIdx} (hc : ctl i = .br l)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  have hv' : AllValid F (brTo S L l.toNat σ) := by simpa only [gen, hc] using hv
  rw [ctl_br hc]
  exact Wp.br (m := .part) (brTo_post hS hR hv')

theorem cons_brIf (hS : S.wellScoped = true) (ih : IH F S lt ρ₀ s₀ m P host fuel)
    {l : LabelIdx} (hc : ctl i = .brIf l) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next c st hst =>
    have hv' := allValid_append.mp hv
    have hrs : rs.reverse = (dens F ρ st).reverse ++ [Val.i32 (c.den F ρ ρ)] := by
      rw [hR.2.2.2.1, hst]
      simp [dens, SV.den, Val.i32]
    rw [hrs, ctl_brIf hc]
    refine Silmaril.Wasm.Logic.Hoare.HWP.brIf (fun h₁ => ?_) (fun h₂ => ?_)
    · exact Wp.br (m := .part) (brTo_post hS ((Rel.pcCons hR) ((den_condF ρ ρ c).mpr h₁)) hv'.1)
    · exact ih _ _ _ r _ ρ s f _ ((Rel.pcCons hR) ((den_ncondF ρ ρ c).mpr h₂)) hv'.2
  next => exact (not_bad hv (Rel.pc hR)).elim

/-- `select` on the stack `c :: v₂ :: v₁ :: st` (top first). -/
theorem sound_select (ih : IH F S lt ρ₀ s₀ m P host fuel) {ts : Option (List ValType)}
    {c : Tm .i32} {v₁ v₂ v : SV} {st : List SV} (hst : σ.stack = .i32 c :: v₂ :: v₁ :: st)
    (hsel : selV c v₁ v₂ = some v) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt fuel L kont k r { σ with stack := v :: st })) :
    HWP P host s f (vals rs.reverse ++ .plain (.select ts) :: expression r)
      (postOf F S lt ρ₀ s₀ m L kont) := by
  have hrs : rs.reverse = (dens F ρ st).reverse ++
      [v₁.den F ρ ρ, v₂.den F ρ ρ, Val.i32 (c.den F ρ ρ)] := by
    rw [hR.2.2.2.1, hst]
    simp [dens, SV.den, Val.i32]
  have hk := ih _ _ _ r _ ρ s f _
    (Rel.update (σ' := { σ with stack := v :: st }) hR rfl rfl (Rel.pc (σ := σ) hR)) hv
  have hv' := selV_den (F := F) hsel ρ ρ
  rw [hrs]
  by_cases h₀ : c.den F ρ ρ = 0
  · have hv₂ : v.den F ρ ρ = v₂.den F ρ ρ := by
      rw [hv', show nz32 (c.den F ρ ρ) = false by unfold nz32; rw [h₀]; rfl]
      rfl
    rw [h₀]
    exact Wp.selectFalse (m := .part) (by simpa [dens, hv₂] using hk)
  · have hv₁ : v.den F ρ ρ = v₁.den F ρ ρ := by
      rw [hv', show nz32 (c.den F ρ ρ) = true from (nz32_iff _).mpr h₀]
      rfl
    exact Wp.selectTrue (m := .part) h₀ (by simpa [dens, hv₁] using hk)

theorem cons_select (ih : IH F S lt ρ₀ s₀ m P host fuel) (hc : ctl i = .select)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  obtain ⟨ts, rfl⟩ := ctl_select hc
  simp only [gen, hc] at hv
  split at hv
  next c v₂ v₁ st hst =>
    split at hv
    next v hsel => exact sound_select ih hst hsel hR hv
    next => exact (not_bad hv (Rel.pc hR)).elim
  next => exact (not_bad hv (Rel.pc hR)).elim

theorem cons_ret (hc : ctl i = .ret) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  have hv' : AllValid F (retVC S σ) := by simpa only [gen, hc] using hv
  rw [ctl_ret hc]
  exact Wp.of_exits (m := .part) (o := .ret rs.reverse) ⟨_, rfl⟩ ⟨ρ, σ, by simpa using hR, hv'⟩

theorem cons_plain (ih : IH F S lt ρ₀ s₀ m P host fuel) (hc : PlainCtl (ctl i))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    HWP P host s f (vals rs.reverse ++ .plain i :: expression r) (postOf F S lt ρ₀ s₀ m L kont) := by
  rcases hc with hc | ⟨_, _, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | hc <;> simp only [gen, hc] at hv
  all_goals
    split at hv
    next σ' side h₁ =>
      have hv' := allValid_append.mp hv
      obtain ⟨hpc, hty⟩ := step1_pc h₁
      obtain ⟨hs₀, hm, hf, hrs, h₅, h₆, h₇⟩ := hR
      subst hrs
      refine step1_wp h₁ (allValid_map_vc hv'.1 h₇) hf ?_
      exact ih _ _ _ r σ' ρ s _ _ ⟨hs₀, hm, rfl, rfl, hty.trans h₅, h₆, hpc ▸ h₇⟩ hv'.2
    next => exact (not_bad hv (Rel.pc hR)).elim

theorem sound_nil (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k [] σ)) :
    HWP P host s f (vals rs.reverse ++ expression []) (postOf F S lt ρ₀ s₀ m L kont) := by
  have hv' : AllValid F (kont σ) := by simpa only [gen] using hv
  have h := HWP.of_vals (P := P) (host := host) (s := s) (f := f) (vs := rs.reverse)
    (Q := postOf F S lt ρ₀ s₀ m L kont) ⟨ρ, σ, by simpa using hR, hv'⟩
  simpa [expression] using h

end Cases

/-- **Soundness of the generator**, at every `fuel`. -/
theorem gen_sound (hS : S.wellScoped = true) : ∀ fuel, IH F S lt ρ₀ s₀ m P host fuel := by
  intro fuel
  induction fuel with
  | zero => exact fun L kont k is σ ρ s f rs hR hv =>
      (not_bad (by simpa [gen] using hv) (Rel.pc hR)).elim
  | succ fuel ih =>
    intro L kont k is σ ρ s f rs hR hv
    cases is with
    | nil => exact sound_nil hR hv
    | cons i r =>
      cases hc : ctl i with
      | block bt b => exact cons_block ih hc hR hv
      | loop bt b => exact cons_loop hS ih hc hR hv
      | if_ bt b₁ b₂ => exact cons_if ih hc hR hv
      | br l => exact cons_br hS hc hR hv
      | brIf l => exact cons_brIf hS ih hc hR hv
      | select => exact cons_select ih hc hR hv
      | ret => exact cons_ret hc hR hv
      | brTable _ _ | call _ | cvt _ | trap | plain =>
        exact cons_plain ih (by simp [PlainCtl, hc]) hR hv

end Silmaril.Proofs.Wasm.Auto.VCGen