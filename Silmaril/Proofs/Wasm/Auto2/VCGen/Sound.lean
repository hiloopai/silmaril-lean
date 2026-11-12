module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Call
public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# Soundness of the VC generator with SSA names, memory and variants

`gen_sound c`: if every condition of `gen S lt fuel L kont k is σ` is valid, then the code `is`,
run from any concrete configuration related to `σ` (`Rel`) in an environment `ρ`, satisfies the
every-run weakest precondition `Wp c` (partial correctness `HWP` for `c = .part`, total
correctness `TWP` for `c = .total`, given `S.total`) with the postcondition `postOf c ρ σ.nv L
kont`. By induction on `fuel`, one lemma per construct, as `Silmaril.Proofs.Wasm.Auto.VCGen2.Sound`.

The postcondition depends on the environment `ρ` the code started in: continuations are run in
environments that agree with `ρ` below the state's next fresh variable (`Kc`), so the head
variables of the enclosing loops keep their values. That is what total correctness needs: a branch
back to loop `j` must make the loop's variant (`varAt S j`, read at the current locals) smaller
than its value at the head locals of the current iteration (read in `ρ`), and `TWP.loop` (with the
concrete variant `Vc`) closes the loop by induction on that value.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP Wp Corr TWP TSafe labelPostT seqPostT loopPostT)
open Silmaril.Wasm.Logic.VC (ctl labelQ loopQ enterVC hwp_block hwp_loop ctl_block ctl_loop ctl_if ctl_br
  ctl_brIf ctl_select ctl_ret PlainCtl)
open Silmaril.Wasm.Auto.VCGen (nz32 nz32_iff arity)

variable {H : Type} {P : Profile} {host : HostSemantics H} {c : Corr}

section Defs

variable (F : Fns) (S : FnSpec) (lt : List IntType) (ρ₀ : Env) (s₀ : Store H) (m : ModuleInst)

/-- A continuation whose conditions hold at a related state (`vs` bottom first), in an
environment that agrees with `ρ` below `N`. -/
def Kc (ρ : Env) (N : Nat) (K : SSt → List Fm) (s : Store H) (f : Frame) (vs : List Val) : Prop :=
  ∃ ρ' σ, Rel F S lt ρ₀ s₀ m ρ' σ s f vs.reverse ∧ EqBelow N ρ ρ' ∧ N ≤ σ.nv ∧ AllValid F (K σ)

/-- The concrete invariant of loop `j` with head variables from `b`, memory variable `hm` and
entry facts `E`, in an environment that agrees with `ρ` below `b`. -/
def InvC (ρ : Env) (j b hm : Nat) (hl : List SV) (E : List Fm) (s : Store H) (f : Frame)
    (a : List Val) : Prop :=
  a = [] ∧ ∃ ρ', Rel F S lt ρ₀ s₀ m ρ' (havoc S lt j b hm hl E) s f [] ∧ EqBelow b ρ ρ'

/-- The values of the globals `0, …, k - 1` of `m` in the store `s` (`k = S.globals.length`). -/
def gvalsOf (s : Store H) : List Val :=
  (List.range S.globals.length).map fun g =>
    match m.globals[g]? with
    | some a => match s.globals[a]? with
      | some gi => gi.value
      | none => .num ⟨.int .i32, 0⟩
    | none => .num ⟨.int .i32, 0⟩

/-- **The concrete variant** of loop `j`: variant `j` read at the frame's locals and the store's
globals (parameters, entry values of globals and the memory at entry from the entry environment
`ρ₀`). -/
def Vc (j : Nat) (s : Store H) (f : Frame) : Nat :=
  ((S.var.getD j (.lit .i32 0)).den F ρ₀
    (valEnv (f.locals.filterMap id ++ gvalsOf S m s) ByteArray.empty)).toNat

/-- The postcondition of code run under the labels `L` with the continuation `kont`, started in
the environment `ρ` with next fresh variable `N`, in reading `c`. A branch back to a loop
re-establishes its invariant and, for total correctness, decreases its variant below its value
at the head locals in `ρ`. -/
def postOf (c : Corr) (ρ : Env) (N : Nat) (L : List Lbl) (kont : SSt → List Fm) : Post H :=
  fun s f o =>
  match o with
  | .normal vs => Kc F S lt ρ₀ s₀ m ρ N kont s f vs
  | .br l vs =>
    match L[l]? with
    | some (.blk n K) => n ≤ vs.length ∧ Kc F S lt ρ₀ s₀ m ρ N K s f (vs.drop (vs.length - n))
    | some (.lp j b hm hl E) => InvC F S lt ρ₀ s₀ m ρ j b hm hl E s f [] ∧
        (c = .total → varOK S j = true ∧ Vc F S ρ₀ m j s f < ((varAt S lt j hl).den F ρ ρ).toNat)
    | none => False
  | .ret vs => Kc F S lt ρ₀ s₀ m ρ N (retVC S lt) s f vs
  | _ => False

/-- The loop labels of `L` have their head variables below `N`, and their entry facts are below
their first head variable and hold in `ρ`. -/
def LblsOK (L : List Lbl) (ρ : Env) (N : Nat) : Prop :=
  ∀ (l j b hm : Nat) (hl : List SV) (E : List Fm), L[l]? = some (Lbl.lp j b hm hl E) →
    S.ents.length < b ∧ b ≤ N ∧ (∀ v ∈ hl, v.vlt N = true) ∧
      ∀ φ ∈ E, φ.vlt b = true ∧ φ.den F ρ ρ

/-- The induction hypothesis: soundness of `gen` at `fuel`, in reading `c`. -/
def IH (c : Corr) (P : Profile) (host : HostSemantics H) (fuel : Nat) : Prop :=
  ∀ L kont k is σ ρ s f rs, Rel F S lt ρ₀ s₀ m ρ σ s f rs → LblsOK F S L ρ σ.nv →
    AllValid F (gen S lt fuel L kont k is σ) →
    Wp c P host s f (vals rs.reverse ++ expression is) (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont)

end Defs

variable {F : Fns} {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

/-! ## Either reading of the logic -/

theorem Wp.monoC {s : Store H} {f : Frame} {code : List Admin} {Q Q' : Post H}
    (h : Wp c P host s f code Q) (hq : ∀ s f o, Q s f o → Q' s f o) : Wp c P host s f code Q' := by
  cases c
  · exact HWP.mono hq h
  · exact TSafe.post_mono h hq

theorem Wp.ifC {s : Store H} {f : Frame} {us : List Val} {x : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H}
    (h₁ : x ≠ 0 → Wp c P host s f (vals us ++ .plain (.block bt b₁) :: rest) Q)
    (h₂ : x = 0 → Wp c P host s f (vals us ++ .plain (.block bt b₂) :: rest) Q) :
    Wp c P host s f (vals (us ++ [.i32 x]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q := by
  cases c
  · exact Silmaril.Wasm.Logic.Hoare.HWP.if_ h₁ h₂
  · refine Silmaril.Wasm.Logic.Hoare.TWP.if_ ?_
    by_cases hx : x = 0
    · have hb : (if x ≠ 0 then b₁ else b₂) = b₂ := by
        simp only [ne_eq, hx, not_true_eq_false, ↓reduceIte]
      rw [hb]
      exact h₂ hx
    · have hb : (if x ≠ 0 then b₁ else b₂) = b₁ := by
        simp only [ne_eq, hx, not_false_eq_true, ↓reduceIte]
      rw [hb]
      exact h₁ hx

theorem Wp.brIfC {s : Store H} {f : Frame} {us : List Val} {x : BitVec 32} {l : LabelIdx}
    {rest : List Admin} {Q : Post H}
    (h₁ : x ≠ 0 → Q s f (.br l.toNat us)) (h₂ : x = 0 → Wp c P host s f (vals us ++ rest) Q) :
    Wp c P host s f (vals (us ++ [.i32 x]) ++ .plain (.brIf l) :: rest) Q := by
  cases c
  · exact Silmaril.Wasm.Logic.Hoare.HWP.brIf (fun h => Silmaril.Wasm.Logic.Hoare.Wp.br (m := .part) (h₁ h))
      h₂
  · exact Silmaril.Wasm.Logic.Hoare.TWP.brIf h₁ h₂

/-! ## The relation -/

/-- A new stack and one more path condition below `nv`. -/
theorem Rel.pcCons {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val} {st : List SV}
    {φ : Fm} (h : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hφ : φ.den F ρ ρ) (hφb : φ.vlt σ.nv = true)
    (hst : ∀ v ∈ st, v.vlt σ.nv = true) :
    Rel F S lt ρ₀ s₀ m ρ { σ with stack := st, pc := φ :: σ.pc } s f (dens F ρ st) := by
  obtain ⟨hl, -, hp, hm⟩ := (fresh_iff σ).mp h.fresh
  refine { h with stack := rfl, pc := ?_, fresh := (fresh_iff _).mpr ⟨hl, hst, ?_, hm⟩ }
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact h.pc ψ hψ
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφb
    · exact hp ψ hψ

/-! ## Loop invariants -/

/-- `ρ` with the head variables `b + j` set to the values of the locals `ls` and memory variable
`b + |ls|` set to memory variable `cm`. -/
def ovr (F : Fns) (b : Nat) (ρ : Env) (ls : List SV) (cm : Nat) : Env where
  e32 i := if b ≤ i then
      (match ls[i - b]? with
        | some (.i32 a) => a.den F ρ ρ
        | _ => ρ.e32 i)
    else ρ.e32 i
  e64 i := if b ≤ i then
      (match ls[i - b]? with
        | some (.i64 a) => a.den F ρ ρ
        | _ => ρ.e64 i)
    else ρ.e64 i
  mem i := if i = b + ls.length then ρ.mem cm else ρ.mem i

theorem eqBelow_ovr {b : Nat} {ρ : Env} {ls : List SV} {cm : Nat} :
    EqBelow b ρ (ovr F b ρ ls cm) := by
  intro i hi
  have h₁ : ¬ b ≤ i := by omega
  have h₂ : i ≠ b + ls.length := by omega
  simp [ovr, h₁, h₂]

theorem SV.vlt_of_isVarAt {v : SV} {i n : Nat} (h : v.isVarAt i = true) (hi : i < n) :
    v.vlt n = true := by
  rcases v with (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) |
    (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    simp_all [SV.isVarAt, SV.vlt, Tm.vlt]

theorem headOK_ty {b : Nat} {lt : List IntType} {hl : List SV} (h : headOK b lt hl = true) :
    hl.map SV.ty = lt := by
  simp only [headOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem headOK_get {b : Nat} {lt : List IntType} {hl : List SV} (h : headOK b lt hl = true)
    (j : Nat) (hj : j < hl.length) : hl[j].isVarAt (b + j) = true ∨ hl[j].vlt b = true := by
  simp only [headOK, Bool.and_eq_true, List.all_eq_true, id_eq] at h
  have := h.2 _ (List.mem_mapIdx.mpr ⟨j, hj, rfl⟩)
  simpa using this

theorem eqSV_den {v w : SV} {ρ : Env} (hty : v.ty = w.ty) (h : (eqSV v w).den F ρ ρ) :
    v.den F ρ ρ = w.den F ρ ρ := by
  rcases v with a | a <;> rcases w with c | c <;>
    simp_all [eqSV, SV.ty, SV.den, Fm.den, Silmaril.Wasm.Auto.VCGen.relP,
      Silmaril.Wasm.Auto.VCGen.relW]

/-- The kept locals' equations. -/
theorem keepEqs_spec {b : Nat} {ρ : Env} : ∀ (j₀ : Nat) (hl ls : List SV),
    hl.map SV.ty = ls.map SV.ty → (∀ φ ∈ keepEqs b j₀ hl ls, φ.den F ρ ρ) →
    ∀ (i : Nat) (h₁ : i < hl.length) (h₂ : i < ls.length), hl[i].isVarAt (b + (j₀ + i)) = false →
      hl[i].den F ρ ρ = ls[i].den F ρ ρ
  | _, [], _, _, _, _, h₁, _, _ => absurd h₁ (Nat.not_lt_zero _)
  | _, _ :: _, [], _, _, _, _, h₂, _ => absurd h₂ (Nat.not_lt_zero _)
  | j₀, h :: hs, v :: vs, hty, hk, i, h₁, h₂, hv => by
    simp only [List.map_cons, List.cons.injEq] at hty
    simp only [keepEqs, List.mem_append] at hk
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hv ⊢
      have hφ := hk (eqSV v h) (.inl (by simp [hv]))
      exact (eqSV_den hty.1.symm hφ).symm
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact keepEqs_spec (j₀ + 1) hs vs hty.2 (fun φ hφ => hk φ (.inr hφ)) i
        (by simpa using h₁) (by simpa using h₂) (by rw [← hv]; simp only [List.getElem_cons_succ]; congr 1; omega)

/-- A head local that is its fresh variable `b + j` denotes, after the override, local `j`. -/
theorem den_ovr_var {b j cm : Nat} {ρ : Env} {ls : List SV} {v w : SV}
    (hv : v.isVarAt (b + j) = true) (hty : v.ty = w.ty) (hget : ls[j]? = some w) :
    v.den F (ovr F b ρ ls cm) (ovr F b ρ ls cm) = w.den F ρ ρ := by
  rcases v with (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) |
    (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    simp only [SV.isVarAt, beq_iff_eq, Bool.false_eq_true] at hv <;> subst hv <;>
    rcases w with a | a <;> simp only [SV.ty, reduceCtorEq] at hty <;>
    simp [SV.den, Tm.den, Env.get, ovr, hget]

/-- A value below `b` is not the variable `b + j`. -/
theorem isVarAt_of_vlt {v : SV} {b j : Nat} (h : v.vlt b = true) : v.isVarAt (b + j) = false := by
  rcases v with (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) |
    (_ | ⟨_, k⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    simp_all [SV.isVarAt, SV.vlt, Tm.vlt] <;> omega

/-- The head locals denote, in the overridden environment, the current locals. -/
theorem dens_head {b cm : Nat} {lt : List IntType} {ρ : Env} {ls hl : List SV}
    (hok : headOK b lt hl = true) (hls : ls.map SV.ty = lt)
    (hk : ∀ φ ∈ keepEqs b 0 hl ls, φ.den F ρ ρ) :
    dens F (ovr F b ρ ls cm) hl = dens F ρ ls := by
  have hty : hl.map SV.ty = ls.map SV.ty := (headOK_ty hok).trans hls.symm
  have hlen : hl.length = ls.length := by simpa using congrArg List.length hty
  refine List.ext_getElem (by simp [hlen]) fun j h₁ h₂ => ?_
  have hj₁ : j < hl.length := by simpa using h₁
  have hj₂ : j < ls.length := by simpa using h₂
  have htj : hl[j].ty = ls[j].ty := by
    simpa [List.getElem?_eq_getElem hj₁, List.getElem?_eq_getElem hj₂] using congrArg (·[j]?) hty
  rw [List.getElem_map, List.getElem_map]
  rcases headOK_get hok j hj₁ with hv | hv
  · exact den_ovr_var hv htj (List.getElem?_eq_getElem hj₂)
  · have hE : EqBelow b ρ (ovr F b ρ ls cm) := eqBelow_ovr
    rw [← SV.den_eqBelow hE hE _ hv]
    exact keepEqs_spec 0 hl ls hty hk j hj₁ hj₂ (isVarAt_of_vlt hv)

theorem head_vlt {b n : Nat} {lt : List IntType} {hl : List SV} (hok : headOK b lt hl = true)
    (h : b + lt.length ≤ n) : ∀ v ∈ hl, v.vlt n = true := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : hl.length = lt.length := by simpa using congrArg List.length (headOK_ty hok)
  rcases headOK_get hok j hj with h' | h'
  · exact SV.vlt_of_isVarAt h' (by omega)
  · exact SV.vlt_mono (by omega) _ h'

theorem scoped_inv (hS : S.wellScoped = true) (j : Nat) :
    (S.inv.getD j .tt).scoped S.ents = true := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : S.inv[j]? with _ | φ
  · rfl
  · exact wellScoped_inv hS φ (List.mem_of_getElem? h)

theorem scoped_preF (hS : S.wellScoped = true) : S.preF.scoped S.ents = true :=
  Fm.scoped_subst_nil _ (wellScoped_pre hS)

theorem den_invAt (ρ : Env) (j : Nat) (ls : List SV) (cm : Nat) :
    (invAt S j ls cm).den F ρ ρ ↔
      (S.inv.getD j .tt).den F ρ (valEnv (dens F ρ ls) (ρ.mem cm)) := by
  rw [invAt, Fm.den_subst, locEnv_eq_valEnv]

/-- The head state of a loop is fresh. -/
theorem havoc_fresh (hS : S.wellScoped = true) {j b hm : Nat} {hl : List SV} {E : List Fm}
    (hok : headOK b lt hl = true) (hp : S.ents.length < b) (hEb : ∀ φ ∈ E, φ.vlt b = true) :
    (havoc S lt j b hm hl E).fresh = true := by
  have hnv : b + lt.length ≤ (havoc S lt j b hm hl E).nv := by simp only [havoc]; omega
  have hpc : ∀ φ ∈ (havoc S lt j b hm hl E).pc, φ.vlt (havoc S lt j b hm hl E).nv = true := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Fm.vlt_subst (by simp only [havoc]; omega) (by simp only [havoc]; omega)
        (by simp only [havoc]; omega) (head_vlt hok hnv) _ (scoped_inv hS j)
    · exact Fm.vlt_mono (by simp only [havoc]; omega) φ (hEb φ hφ)
  exact (fresh_iff _).mpr ⟨head_vlt hok hnv, by simp [havoc], hpc, by simp only [havoc]; omega⟩

/-- The memory variable of a loop head, after the override, is the current memory. -/
theorem ovr_mem_hm {b hm : Nat} {ρ : Env} {ls : List SV} {cm : Nat}
    (hc : hm = b + ls.length ∨ hm = cm) : (ovr F b ρ ls cm).mem hm = ρ.mem cm := by
  rcases hc with rfl | rfl
  · simp [ovr]
  · by_cases h : hm = b + ls.length
    · simp [ovr, h]
    · simp [ovr, h]

/-- The conditions `lpVC` gives at a state related in `ρ`. -/
theorem lpVC_holds {j b hm : Nat} {hl : List SV} {ρ : Env} {σ : SSt}
    (hpc : ∀ φ ∈ σ.pc, φ.den F ρ ρ) (hv : AllValid F (lpVC S lt j b hm hl σ)) :
    ((hm = b + lt.length ∨ hm = σ.mem) ∧ S.ents.length < b ∧ headOK b lt hl = true) ∧
      (invAt S j σ.locals σ.mem).den F ρ ρ ∧ ∀ φ ∈ keepEqs b 0 hl σ.locals, φ.den F ρ ρ := by
  unfold lpVC at hv
  split at hv
  case isFalse => exact (not_bad hv hpc).elim
  rename_i hc
  have hall : ∀ φ ∈ invAt S j σ.locals σ.mem :: keepEqs b 0 hl σ.locals, φ.den F ρ ρ :=
    (Fm.den_conj ρ ρ _).mp (vc_holds hv.1 hpc)
  exact ⟨hc, hall _ List.mem_cons_self, fun φ h => hall φ (List.mem_cons_of_mem _ h)⟩

/-- **Re-establishing a loop invariant** from its condition (`lpVC`) at the current locals and
memory. -/
theorem invC_of (hS : S.wellScoped = true) {j b hm : Nat} {hl : List SV} {E : List Fm} {ρ : Env}
    {σ : SSt} {s : Store H} {f : Frame} {rs : List Val} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hEf : ∀ φ ∈ E, φ.vlt b = true ∧ φ.den F ρ ρ)
    (hv : AllValid F (lpVC S lt j b hm hl σ)) : InvC F S lt ρ₀ s₀ m ρ j b hm hl E s f [] := by
  obtain ⟨⟨hc₁, hc₂, hok⟩, hI, hk⟩ := lpVC_holds hR.pc hv
  have hlen : σ.locals.length = lt.length := by rw [← hR.types, List.length_map]
  have hE : EqBelow b ρ (ovr F b ρ σ.locals σ.mem) := eqBelow_ovr
  have hag : Agree S.ents ρ (ovr F b ρ σ.locals σ.mem) := agree_of_eqBelow hE hc₂
  have hmem : (ovr F b ρ σ.locals σ.mem).mem hm = ρ.mem σ.mem := ovr_mem_hm (by rwa [hlen])
  have hd : dens F (ovr F b ρ σ.locals σ.mem) hl = dens F ρ σ.locals := dens_head hok hR.types hk
  have hpc : ∀ φ ∈ (havoc S lt j b hm hl E).pc, φ.den F (ovr F b ρ σ.locals σ.mem)
      (ovr F b ρ σ.locals σ.mem) := by
    intro φ hφ
    rcases List.mem_cons.mp hφ with rfl | hφ
    · rw [den_invAt, hd, hmem]
      exact (Fm.den_scoped hag _ _ (scoped_inv hS j)).mp ((den_invAt ρ j σ.locals σ.mem).mp hI)
    · exact (Fm.den_eqBelow hE hE φ (hEf φ hφ).1).mp (hEf φ hφ).2
  have hloc : f.locals = locs F (ovr F b ρ σ.locals σ.mem)
      ((havoc S lt j b hm hl E).locals.take (S.nl lt)) := by
    rw [hR.locals]
    simpa [locs, dens, havoc, Function.comp_def, ← List.map_take] using
      (congrArg (fun l => (List.map some l).take (S.nl lt)) hd).symm
  have hgl : globs F S lt (ovr F b ρ σ.locals σ.mem) (havoc S lt j b hm hl E) =
      globs F S lt ρ σ := by
    simp only [globs, havoc, dens, List.map_drop] at hd ⊢
    rw [hd]
  exact ⟨rfl, _, { store := by rw [hgl]; simp only [havoc]; rw [hmem]; exact hR.store
                   memOk := by rw [← (hE 0 (by omega)).2.2]; exact hR.memOk
                   globOk := hR.globOk, glen := hR.glen
                   modl := hR.modl, locals := hloc, stack := rfl, types := headOK_ty hok
                   agree := hag.symm.trans hR.agree, pc := hpc
                   fresh := havoc_fresh hS hok hc₂ fun φ hφ => (hEf φ hφ).1
                   pnv := by simp only [havoc]; omega, pre := hR.pre }, hE⟩

/-! ## Variants -/

/-- A term that does not read the current memory does not depend on the memories of the
placeholder environment. -/
theorem Tm.den_curFree {ρ ξ ξ' : Env} (h32 : ξ.e32 = ξ'.e32) (h64 : ξ.e64 = ξ'.e64) :
    ∀ {t : IntType} (a : Tm t), a.curFree = true → a.den F ρ ξ = a.den F ρ ξ'
  | _, .var _ _, _ => rfl
  | _, .loc .i32 j, _ => congrFun h32 j
  | _, .loc .i64 j, _ => congrFun h64 j
  | _, .lit _ _, _ => rfl
  | _, .un _ a, h => by
    simp only [Tm.curFree] at h
    simp only [Tm.den, Tm.den_curFree h32 h64 a h]
  | _, .bin _ a b, h => by
    simp only [Tm.curFree, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_curFree h32 h64 a h.1, Tm.den_curFree h32 h64 b h.2]
  | _, .rel _ a b, h => by
    simp only [Tm.curFree, Bool.and_eq_true] at h
    rw [Tm.den, Tm.den, Tm.den_curFree h32 h64 a h.1, Tm.den_curFree h32 h64 b h.2]
  | _, .eqz a, h => by
    simp only [Tm.curFree] at h
    rw [Tm.den, Tm.den, Tm.den_curFree h32 h64 a h]
  | _, .ite c a b, h => by
    simp only [Tm.curFree, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_curFree h32 h64 c h.1.1, Tm.den_curFree h32 h64 a h.1.2,
      Tm.den_curFree h32 h64 b h.2]
  | _, .wrap a, h => by
    simp only [Tm.curFree] at h
    rw [Tm.den, Tm.den, Tm.den_curFree h32 h64 a h]
  | _, .ext sx a, h => by
    simp only [Tm.curFree] at h
    cases sx <;> rw [Tm.den, Tm.den, Tm.den_curFree h32 h64 a h]
  | _, .fn _ a, h => by
    simp only [Tm.curFree] at h
    simp only [Tm.den, Tm.den_curFree h32 h64 a h]
  | _, .fn2 _ a b, h => by
    simp only [Tm.curFree, Bool.and_eq_true] at h
    simp only [Tm.den, Tm.den_curFree h32 h64 a h.1, Tm.den_curFree h32 h64 b h.2]
  | _, .load _ _ _ (.v _) a _, h => by
    simp only [Tm.curFree, MR.isVar, Bool.true_and] at h
    simp only [Tm.den, MR.den, Tm.den_curFree h32 h64 a h]
  | _, .load _ _ _ .cur _ _, h => by simp [Tm.curFree, MR.isVar] at h
  | _, .mfn _ (.v _) a b, h => by
    simp only [Tm.curFree, MR.isVar, Bool.true_and, Bool.and_eq_true] at h
    simp only [Tm.den, MR.den, Tm.den_curFree h32 h64 a h.1, Tm.den_curFree h32 h64 b h.2]; rfl
  | _, .mfn _ .cur _ _, h => by simp [Tm.curFree, MR.isVar] at h

theorem varOK_parts {j : Nat} (h : varOK S j = true) :
    (S.var.getD j (.lit .i32 0)).curFree = true ∧
      (S.var.getD j (.lit .i32 0)).scoped S.ents = true := by
  simpa [varOK] using h

/-- The globals read from a related store are the state's symbolic globals. -/
theorem gvalsOf_rel {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) : gvalsOf S m s = globs F S lt ρ σ := by
  refine List.ext_getElem (by rw [length_globs hR]; simp [gvalsOf]) fun g h₁ h₂ => ?_
  have hg : g < S.globals.length := by simpa [gvalsOf] using h₁
  obtain ⟨t, ht⟩ : ∃ t, S.globals[g]? = some t := ⟨_, List.getElem?_eq_getElem hg⟩
  obtain ⟨a, gi, ha, hs, -⟩ := hR.globOk.2 _ _ ht
  have hs' : (upd S s₀ m (ρ.mem σ.mem)).globals[a]? = some gi := by rw [globals_upd]; exact hs
  have hset := globals_setGs (s := upd S s₀ m (ρ.mem σ.mem)) (distinct_globs hR) h₂ ha hs'
  rw [← hR.store] at hset
  simp only [gvalsOf, List.getElem_map, List.getElem_range, ha, hset]

/-- The concrete variant of a related configuration is the variant at its symbolic locals. -/
theorem Vc_rel {j : Nat} {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hok : varOK S j = true) :
    Vc F S ρ₀ m j s f = ((varAt S lt j σ.locals).den F ρ ρ).toNat := by
  obtain ⟨hmf, hsc⟩ := varOK_parts hok
  have hfm : ∀ l : List SV, (locs F ρ l).filterMap id = dens F ρ l := by
    intro l
    induction l with
    | nil => rfl
    | cons v l ih => simp
  have hloc : f.locals.filterMap id ++ gvalsOf S m s = dens F ρ σ.locals := by
    rw [hR.locals, hfm, gvalsOf_rel hR, globs, ← List.map_append, List.take_append_drop]
  unfold Vc varAt
  rw [Tm.den_subst, locEnv_eq_valEnv, hloc, Tm.den_scoped hR.agree _ _ hsc]
  exact congrArg BitVec.toNat (Tm.den_curFree (F := F) (ρ := ρ₀)
    (ξ := valEnv (dens F ρ σ.locals) ByteArray.empty)
    (ξ' := valEnv (List.map (SV.den F ρ ρ) σ.locals) (ρ.mem 0)) rfl rfl _ hmf)

theorem varAt_vlt {j N : Nat} {hl : List SV} (hok : varOK S j = true) (hp : S.ents.length < N)
    (hhl : ∀ v ∈ hl, v.vlt N = true) : (varAt S lt j hl).vlt N = true :=
  Tm.vlt_subst (by omega) (by omega) (by omega) (fun v hv => hhl v hv) _ (varOK_parts hok).2

/-! ## The postcondition, under environment extension -/

theorem LblsOK.mono {L : List Lbl} {ρ ρ' : Env} {N N' : Nat} (h : LblsOK F S L ρ N)
    (hE : EqBelow N ρ ρ') (hN : N ≤ N') : LblsOK F S L ρ' N' := by
  unfold LblsOK at h ⊢
  intro l j b hm hl E hL
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h l j b hm hl E hL
  refine ⟨h₁, by omega, fun v hv => SV.vlt_mono hN v (h₃ v hv), fun φ hφ => ?_⟩
  obtain ⟨hb, hd⟩ := h₄ φ hφ
  exact ⟨hb, (Fm.den_eqBelow (hE.mono h₂) (hE.mono h₂) φ hb).mp hd⟩

theorem LblsOK.blk {L : List Lbl} {ρ : Env} {N n : Nat} {K : SSt → List Fm}
    (h : LblsOK F S L ρ N) : LblsOK F S (.blk n K :: L) ρ N := by
  unfold LblsOK at h ⊢
  intro l j b hm hl E hL
  cases l with
  | zero => simp at hL
  | succ l => exact h l j b hm hl E (by simpa using hL)

theorem Kc.mono {K : SSt → List Fm} {ρ ρ' : Env} {N N' : Nat} (hE : EqBelow N ρ ρ')
    (hN : N ≤ N') {s : Store H} {f : Frame} {vs : List Val}
    (h : Kc F S lt ρ₀ s₀ m ρ' N' K s f vs) : Kc F S lt ρ₀ s₀ m ρ N K s f vs := by
  obtain ⟨ρ'', σ, hR, hE', hN', hv⟩ := h
  exact ⟨ρ'', σ, hR, hE.trans (hE'.mono hN), hN.trans hN', hv⟩

theorem InvC.mono {ρ ρ' : Env} {j b hm : Nat} {hl : List SV} {E : List Fm} (hE : EqBelow b ρ ρ')
    {s : Store H} {f : Frame} {a : List Val} (h : InvC F S lt ρ₀ s₀ m ρ' j b hm hl E s f a) :
    InvC F S lt ρ₀ s₀ m ρ j b hm hl E s f a := by
  obtain ⟨ha, ρ'', hR, hE'⟩ := h
  exact ⟨ha, ρ'', hR, hE.trans hE'⟩

/-- **The postcondition is stable** under extending the environment above `N`. -/
theorem postOf_mono {L : List Lbl} {kont : SSt → List Fm} {ρ ρ' : Env} {N N' : Nat}
    (hE : EqBelow N ρ ρ') (hN : N ≤ N') (hL : LblsOK F S L ρ N) {s : Store H} {f : Frame}
    {o : Outcome} (h : postOf F S lt ρ₀ s₀ m c ρ' N' L kont s f o) :
    postOf F S lt ρ₀ s₀ m c ρ N L kont s f o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · exact Kc.mono hE hN h
  · simp only [postOf] at h ⊢
    cases hl : L[l]? with
    | none => simp only [hl] at h
    | some lb =>
      cases lb with
      | blk n K =>
        simp only [hl] at h ⊢
        exact ⟨h.1, Kc.mono hE hN h.2⟩
      | lp j b hm hl' E =>
        simp only [hl] at h ⊢
        obtain ⟨hp, hb, hhl, -⟩ := hL l j b hm hl' E hl
        refine ⟨InvC.mono (hE.mono hb) h.1, fun hc => ?_⟩
        obtain ⟨hok, hlt⟩ := h.2 hc
        refine ⟨hok, ?_⟩
        rwa [Tm.den_eqBelow hE hE _ (varAt_vlt hok (by omega) hhl)]
  · exact Kc.mono hE hN h
  all_goals exact h

/-! ## Labels -/

theorem kc_wp {fuel N : Nat} {ρ : Env} (ih : IH F S lt ρ₀ s₀ m c P host fuel) {L : List Lbl}
    {kont : SSt → List Fm} {k : Nat} {r : List Instr} (hL : LblsOK F S L ρ N) :
    ∀ s f vs, Kc F S lt ρ₀ s₀ m ρ N (gen S lt fuel L kont k r) s f vs →
      Wp c P host s f (vals vs ++ expression r) (postOf F S lt ρ₀ s₀ m c ρ N L kont) := by
  rintro s f vs ⟨ρ', σ, hR, hE, hN, hv⟩
  have h := ih L kont k r σ ρ' s f vs.reverse hR (hL.mono hE hN) hv
  rw [List.reverse_reverse] at h
  exact Wp.monoC h fun _ _ _ h' => postOf_mono hE hN hL h'

theorem postOf_blk {n N : Nat} {ρ : Env} {K kont : SSt → List Fm} {L : List Lbl} {s : Store H}
    {f : Frame} {o : Outcome} (h : postOf F S lt ρ₀ s₀ m c ρ N (.blk n K :: L) K s f o) :
    labelQ n [] (Kc F S lt ρ₀ s₀ m ρ N K) (postOf F S lt ρ₀ s₀ m c ρ N L kont) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  · simpa [labelQ, postOf] using h
  all_goals exact h.elim

theorem enterVC_nil {f : Frame} {bt : BlockType} {n : Nat}
    {B : List Val → List Val → Nat → Nat → Prop} (hn : arity bt = some n) (h : B [] [] 0 n) :
    enterVC f bt [] B := by
  cases bt <;> simp only [arity, Option.some.injEq, reduceCtorEq] at hn <;> subst hn <;>
    simpa [enterVC, ModuleInst.blockType?] using h

theorem blockType_nil {bt : BlockType} {n : Nat} (hn : arity bt = some n) (mi : ModuleInst) :
    ∃ t₂ : List Silmaril.Wasm.Validation.CValType, mi.blockType? bt = some ([], t₂) ∧ t₂.length = n := by
  cases bt <;> simp only [arity, Option.some.injEq, reduceCtorEq] at hn <;> subst hn <;>
    simp [ModuleInst.blockType?]

/-- A block body's outcomes, for total correctness. -/
theorem labelQ_postT {n : Nat} {K : Store H → Frame → List Val → Prop} {Q : Post H}
    {rest : List Admin} (hK : ∀ s f vs, K s f vs → TWP P host s f (vals vs ++ rest) Q)
    {s : Store H} {f : Frame} {o : Outcome} (h : labelQ n [] K Q s f o) :
    labelPostT P host n [] [] (seqPostT P host rest Q) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · simpa [labelPostT, Silmaril.Wasm.Logic.Hoare.labelPostK, seqPostT, TWP] using hK s f vs h
  · obtain ⟨hn, hk⟩ := h
    refine ⟨vs.take (vs.length - n), vs.drop (vs.length - n), (List.take_append_drop _ _).symm,
      by simp only [List.length_drop]; omega, ?_⟩
    refine .exit (.normal (vs.drop (vs.length - n))) (by simp [expression, vals,
      Silmaril.Wasm.Logic.Hoare.Exits]) ?_
    simpa [seqPostT, TWP] using hK s f _ (by simpa using hk)
  all_goals simpa [labelQ, labelPostT, Silmaril.Wasm.Logic.Hoare.labelPostK, seqPostT] using h

/-- **A block** entered with an empty stack, in either reading. -/
theorem Wp.block0 {s : Store H} {f : Frame} {bt : BlockType} {n : Nat} {b : List Instr}
    {rest : List Admin} {Q : Post H} {K : Store H → Frame → List Val → Prop}
    (hn : arity bt = some n) (hK : ∀ s f vs, K s f vs → Wp c P host s f (vals vs ++ rest) Q)
    (h : Wp c P host s f (expression b) (labelQ n [] K Q)) :
    Wp c P host s f (vals [] ++ .plain (.block bt b) :: rest) Q := by
  cases c
  · exact hwp_block hK (enterVC_nil hn (by simpa using h))
  · obtain ⟨t₂, hbt, hlen⟩ := blockType_nil hn f.module
    have h' := Silmaril.Wasm.Logic.Hoare.TWP.block (us := []) (vs := []) (rest := rest) (Q := Q)
      (P := P) (host := host) (s := s) (f := f) (body := b) hbt rfl
      (TSafe.post_mono (by simpa [TWP] using h) fun _ _ _ hq => hlen ▸ labelQ_postT hK hq)
    simpa using h'

/-- A block (of `block` or `if`) entered with an empty stack. -/
theorem sound_blockBody {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m c P host fuel) {bt : BlockType}
    {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm} {k k' : Nat} {σ : SSt}
    {ρ : Env} {s : Store H} {f : Frame} (hn : arity bt = some n)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f []) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt fuel (.blk n (gen S lt fuel L kont k' r) :: L)
      (gen S lt fuel L kont k' r) k b σ)) :
    Wp c P host s f (vals [] ++ .plain (.block bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  refine Wp.block0 hn (kc_wp (k := k') ih hL) ?_
  have h := ih _ _ k b σ ρ s f [] hR hL.blk hv
  simp only [List.reverse_nil, vals, List.map_nil, List.nil_append] at h
  exact Wp.monoC h fun _ _ _ h => postOf_blk h

/-- A branch to a block: the continuation on the top `n` values. -/
theorem brBlk_post {L : List Lbl} {kont : SSt → List Fm} {l n : Nat} {K : SSt → List Fm}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val} (hl : L[l]? = some (.blk n K))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hn : n ≤ σ.stack.length)
    (hv : AllValid F (K { σ with stack := σ.stack.take n })) :
    postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont s f (.br l rs.reverse) := by
  have hrs : rs = dens F ρ σ.stack := hR.stack
  have hlen : rs.length = σ.stack.length := by rw [hrs, List.length_map]
  have htake : (rs.reverse.drop (rs.reverse.length - n)).reverse = dens F ρ (σ.stack.take n) := by
    rw [List.reverse_drop, List.reverse_reverse, List.length_reverse,
      Nat.sub_sub_self (by rw [hlen]; exact hn), hrs]
    simp [dens, List.map_take]
  simp only [postOf, hl]
  refine ⟨by rw [List.length_reverse, hlen]; exact hn, ρ, { σ with stack := σ.stack.take n }, ?_,
    EqBelow.refl _ _, le_rfl, hv⟩
  rw [htake]
  exact hR.withStack fun v hv => stack_vlt hR v (List.mem_of_mem_take hv)

theorem ult_of_valid {a b : Tm .i32} {ρ : Env} (h : (Fm.rel (.lt .unsigned) a b).den F ρ ρ) :
    (a.den F ρ ρ).toNat < (b.den F ρ ρ).toNat := h

/-- A branch to label `l`. -/
theorem brTo_post (hS : S.wellScoped = true) (hT : c = .total → S.total = true) {L : List Lbl}
    {kont : SSt → List Fm} {l : Nat}
    {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (brTo S lt L l σ)) :
    postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont s f (.br l rs.reverse) := by
  unfold brTo at hv
  split at hv
  next n K hl =>
    split at hv
    next hn => exact brBlk_post hl hR hn hv
    next => exact (not_bad hv hR.pc).elim
  next j b hm hl' E hl =>
    have hv' := allValid_append.mp hv
    simp only [postOf, hl]
    refine ⟨invC_of hS hR (hL l j b hm hl' E hl).2.2.2 hv'.1, fun hc => ?_⟩
    have hv₂ := hv'.2
    simp only [varVC, hT hc, ↓reduceIte] at hv₂
    split at hv₂
    next hok =>
      refine ⟨hok, ?_⟩
      rw [Vc_rel hR hok]
      exact ult_of_valid (vc_holds hv₂.1 hR.pc)
    next => exact (not_bad hv₂ hR.pc).elim
  next => exact (not_bad hv hR.pc).elim

/-! ## The generator -/

theorem rs_nil {ρ : Env} {σ : SSt} {s : Store H} {f : Frame} {rs : List Val}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = []) : rs = [] := by
  rw [hR.stack, hst]
  rfl

/-- The head label of a loop is well formed. -/
theorem lblsOK_lp {L : List Lbl} {σ : SSt} {ρ ρ' : Env} {s s' : Store H}
    {f f' : Frame} {rs : List Val} {j hm : Nat} {hl : List SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hL : LblsOK F S L ρ σ.nv) (hok : headOK σ.nv lt hl = true)
    (hR' : Rel F S lt ρ₀ s₀ m ρ' (havoc S lt j σ.nv hm hl σ.pc) s' f' []) (hE : EqBelow σ.nv ρ ρ') :
    LblsOK F S (.lp j σ.nv hm hl σ.pc :: L) ρ' (havoc S lt j σ.nv hm hl σ.pc).nv := by
  have hnv : σ.nv + lt.length ≤ (havoc S lt j σ.nv hm hl σ.pc).nv := by simp only [havoc]; omega
  have hL₁ := hL.mono hE (show σ.nv ≤ (havoc S lt j σ.nv hm hl σ.pc).nv by omega)
  unfold LblsOK at hL₁ ⊢
  intro l j' b' hm' hl' E' hL'
  cases l with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Lbl.lp.injEq] at hL'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hL'
    refine ⟨hR.pnv, by omega, head_vlt hok hnv, fun φ hφ => ⟨?_, hR'.pc φ (by simp [havoc, hφ])⟩⟩
    exact ((fresh_iff σ).mp hR.fresh).2.2.1 φ hφ
  | succ l => exact hL₁ l j' b' hm' hl' E' (by simpa using hL')

/-- The outcomes of a loop body (partial correctness): the iteration's environment `ρ'` agrees
with the loop's entry environment `ρ` below the head variables. -/
theorem postOf_lp {j b hm N : Nat} {hl : List SV} {E : List Fm} {K kont : SSt → List Fm} {L : List Lbl}
    {ρ ρ' : Env} {f₀ : Frame} (hm' : f₀.module = m) (hE : EqBelow b ρ ρ') (hN : b ≤ N)
    (hL : LblsOK F S L ρ b) {s : Store H} {f : Frame} {o : Outcome}
    (h : postOf F S lt ρ₀ s₀ m c ρ' N (.lp j b hm hl E :: L) K s f o) :
    loopQ 0 [] (fun s' f' a' => InvC F S lt ρ₀ s₀ m ρ j b hm hl E s' f' a' ∧ f'.module = f₀.module)
      (Kc F S lt ρ₀ s₀ m ρ b K) (postOf F S lt ρ₀ s₀ m c ρ b L kont) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · simpa [loopQ] using Kc.mono hE hN h
  · have h' : InvC F S lt ρ₀ s₀ m ρ' j b hm hl E s f [] := by simpa [postOf] using h.1
    obtain ⟨-, ρ'', hR, hE'⟩ := h'
    refine ⟨Nat.zero_le _, ⟨by simp, ρ'', hR, hE.trans hE'⟩, ?_⟩
    rw [hR.modl, hm']
  · have h' : postOf F S lt ρ₀ s₀ m c ρ' N L kont s f (.br l vs) := by simpa [postOf] using h
    simpa [loopQ] using postOf_mono hE hN hL h'
  · have h' : postOf F S lt ρ₀ s₀ m c ρ' N L kont s f (.ret vs) := h
    simpa [loopQ] using postOf_mono hE hN hL h'
  all_goals exact h.elim

/-- The outcomes of a loop body (total correctness), at the iteration whose head configuration
has the variant `v`. -/
theorem postOf_lpT {j b hm N : Nat} {hl : List SV} {E : List Fm} {K kont : SSt → List Fm} {L : List Lbl}
    {ρ ρ' : Env} {rest : List Admin} {Q : Post H} (hE : EqBelow b ρ ρ') (hN : b ≤ N)
    (hL : LblsOK F S L ρ b)
    (hK : ∀ s f vs, Kc F S lt ρ₀ s₀ m ρ b K s f vs → TWP P host s f (vals vs ++ rest) Q)
    (hQ : ∀ s f o, postOf F S lt ρ₀ s₀ m .total ρ b L kont s f o → Q s f o)
    {s : Store H} {f : Frame} {o : Outcome}
    (h : postOf F S lt ρ₀ s₀ m .total ρ' N (.lp j b hm hl E :: L) K s f o) :
    loopPostT 0 [] (fun s' f' a' => a' = [] ∧ InvC F S lt ρ₀ s₀ m ρ j b hm hl E s' f' [] ∧
        f'.module = m)
      (fun s' f' _ => Vc F S ρ₀ m j s' f') ((varAt S lt j hl).den F ρ' ρ').toNat
      (seqPostT P host rest Q) s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c'⟩
  · simpa [loopPostT, seqPostT, TWP] using hK s f vs (Kc.mono hE hN h)
  · have h' : InvC F S lt ρ₀ s₀ m ρ' j b hm hl E s f [] ∧
        (Corr.total = .total → varOK S j = true ∧
          Vc F S ρ₀ m j s f < ((varAt S lt j hl).den F ρ' ρ').toNat) := by simpa [postOf] using h
    obtain ⟨-, ρ'', hR, hE'⟩ := h'.1
    exact ⟨vs, [], by simp, rfl, ⟨rfl, ⟨rfl, ρ'', hR, hE.trans hE'⟩, hR.modl⟩, (h'.2 rfl).2⟩
  · have h' : postOf F S lt ρ₀ s₀ m .total ρ' N L kont s f (.br l vs) := by simpa [postOf] using h
    simpa [loopPostT, seqPostT] using hQ s f _ (postOf_mono hE hN hL h')
  · have h' : postOf F S lt ρ₀ s₀ m .total ρ' N L kont s f (.ret vs) := h
    simpa [loopPostT, seqPostT] using hQ s f _ (postOf_mono hE hN hL h')
  all_goals exact h.elim

/-- The loop body from any head configuration, by the induction hypothesis. -/
abbrev BodyOK (c : Corr) (P : Profile) (host : HostSemantics H) (L : List Lbl)
    (kont : SSt → List Fm) (k hm b₀ : Nat) (hl : List SV) (E : List Fm) (ρ : Env)
    (b r : List Instr) (fuel : Nat) : Prop :=
  ∀ s' f' ρ', Rel F S lt ρ₀ s₀ m ρ' (havoc S lt k b₀ hm hl E) s' f' [] → EqBelow b₀ ρ ρ' →
    Wp c P host s' f' (expression b) (postOf F S lt ρ₀ s₀ m c ρ' (havoc S lt k b₀ hm hl E).nv
      (.lp k b₀ hm hl E :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r))

/-- A loop, partial correctness. -/
theorem sound_loopP {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m .part P host fuel)
    {bt : BlockType} {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k hm : Nat} {hl : List SV} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame}
    (hn : arity bt = some n) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f []) (hL : LblsOK F S L ρ σ.nv)
    (hinv : InvC F S lt ρ₀ s₀ m ρ k σ.nv hm hl σ.pc s f [])
    (hN : σ.nv ≤ (havoc S lt k σ.nv hm hl σ.pc).nv)
    (hbody : BodyOK (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) .part P host L
      kont k hm σ.nv hl σ.pc ρ b r fuel) :
    Wp .part P host s f (vals [] ++ .plain (.loop bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m .part ρ σ.nv L kont) := by
  refine hwp_loop (I := InvC F S lt ρ₀ s₀ m ρ k σ.nv hm hl σ.pc)
    (kc_wp (k := k + 1 + nloops fuel b) ih hL) (enterVC_nil hn ⟨hinv, ?_⟩)
  rintro s' f' a' ⟨rfl, ρ', hR', hE⟩ - -
  exact HWP.mono (fun _ _ _ h => postOf_lp hR.modl hE hN hL h) (hbody s' f' ρ' hR' hE)

/-- The variant at the head of an iteration, when the loop has a usable variant. -/
theorem head_variant {k hm b₀ : Nat} {hl : List SV} {E : List Fm} {ρ' : Env} {s' : Store H} {f' : Frame}
    (hR' : Rel F S lt ρ₀ s₀ m ρ' (havoc S lt k b₀ hm hl E) s' f' []) :
    Vc F S ρ₀ m k s' f' = ((varAt S lt k hl).den F ρ' ρ').toNat ∨ varOK S k = false := by
  rcases h : varOK S k with _ | _
  · exact .inr rfl
  · exact .inl (by simpa [havoc] using Vc_rel hR' h)

/-- One iteration of a loop, total correctness: the body's outcomes as `TWP.loop` needs them. -/
theorem loop_iterT {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m .total P host fuel)
    {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k hm : Nat} {hl : List SV} {σ : SSt} {ρ ρ' : Env} {s' : Store H} {f' : Frame}
    (hL : LblsOK F S L ρ σ.nv) (hN : σ.nv ≤ (havoc S lt k σ.nv hm hl σ.pc).nv)
    (hR' : Rel F S lt ρ₀ s₀ m ρ' (havoc S lt k σ.nv hm hl σ.pc) s' f' []) (hE : EqBelow σ.nv ρ ρ')
    (hbody : BodyOK (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) .total P host L
      kont k hm σ.nv hl σ.pc ρ b r fuel) :
    TWP P host s' f' (vals [] ++ expression b)
      (loopPostT 0 [] (fun s f a => a = [] ∧ InvC F S lt ρ₀ s₀ m ρ k σ.nv hm hl σ.pc s f [] ∧
        f.module = m) (fun s f _ => Vc F S ρ₀ m k s f) (Vc F S ρ₀ m k s' f')
        (seqPostT P host (expression r) (postOf F S lt ρ₀ s₀ m .total ρ σ.nv L kont))) := by
  refine TSafe.post_mono (by simpa [TWP] using hbody s' f' ρ' hR' hE) fun s'' f'' o h => ?_
  have h' := postOf_lpT (rest := expression r) (Q := postOf F S lt ρ₀ s₀ m .total ρ σ.nv L kont)
    hE hN hL (kc_wp (k := k + 1 + nloops fuel b) ih hL) (fun _ _ _ hq => hq) h
  rcases o with vs' | ⟨_ | l, vs'⟩ | vs' | _ | a | ⟨vs', a, c'⟩
  · exact h'
  · obtain ⟨vs₁, vs₂, h₁, h₂, h₃, h₄⟩ := h'
    refine ⟨vs₁, vs₂, h₁, h₂, h₃, ?_⟩
    rcases head_variant hR' with hV | hV
    · rw [hV]; exact h₄
    · have hok : varOK S k = true := by
        simp only [postOf, List.getElem?_cons_zero] at h
        exact (h.2 trivial).1
      simp [hok] at hV
  all_goals exact h'

/-- A loop, total correctness: `TWP.loop` with the invariant `InvC` and the concrete variant. -/
theorem sound_loopT {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m .total P host fuel)
    {bt : BlockType} {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k hm : Nat} {hl : List SV} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame}
    (hn : arity bt = some n) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f []) (hL : LblsOK F S L ρ σ.nv)
    (hinv : InvC F S lt ρ₀ s₀ m ρ k σ.nv hm hl σ.pc s f [])
    (hN : σ.nv ≤ (havoc S lt k σ.nv hm hl σ.pc).nv)
    (hbody : BodyOK (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) .total P host L
      kont k hm σ.nv hl σ.pc ρ b r fuel) :
    Wp .total P host s f (vals [] ++ .plain (.loop bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m .total ρ σ.nv L kont) := by
  obtain ⟨t₂, hbt, -⟩ := blockType_nil hn m
  have hcode : vals [] ++ Admin.plain (.loop bt b) :: expression r =
      (vals ([] ++ []) ++ [Admin.plain (.loop bt b)]) ++ expression r := by simp
  rw [hcode]
  refine Silmaril.Wasm.Logic.Hoare.TWP.seq (Silmaril.Wasm.Logic.Hoare.TWP.loop
    (Inv := fun s' f' a' => a' = [] ∧ InvC F S lt ρ₀ s₀ m ρ k σ.nv hm hl σ.pc s' f' [] ∧
      f'.module = m)
    (V := fun s' f' _ => Vc F S ρ₀ m k s' f') (t₁ := []) (t₂ := t₂) (fun _ f' _ hi => ?_)
    (fun _ _ vs hi => by rw [hi.1]; rfl) ?_ ⟨rfl, hinv, hR.modl⟩)
  · rw [hi.2.2]
    exact hbt
  · rintro s' f' vs ⟨rfl, ⟨-, ρ', hR', hE⟩, -⟩
    exact loop_iterT ih hL hN hR' hE hbody

theorem sound_loop (hS : S.wellScoped = true) {fuel : Nat} (ih : IH F S lt ρ₀ s₀ m c P host fuel)
    {bt : BlockType} {n : Nat} {b r : List Instr} {L : List Lbl} {kont : SSt → List Fm}
    {k hm : Nat} {hl : List SV} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame}
    (hn : arity bt = some n) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f []) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (lpVC S lt k σ.nv hm hl σ ++
      gen S lt fuel (.lp k σ.nv hm hl σ.pc :: L) (gen S lt fuel L kont (k + 1 + nloops fuel b) r)
        (k + 1) b (havoc S lt k σ.nv hm hl σ.pc))) :
    Wp c P host s f (vals [] ++ .plain (.loop bt b) :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hv' := allValid_append.mp hv
  have hok : headOK σ.nv lt hl = true := (lpVC_holds hR.pc hv'.1).1.2.2
  have hN : σ.nv ≤ (havoc S lt k σ.nv hm hl σ.pc).nv := by simp only [havoc]; omega
  have hbody : BodyOK (F := F) (S := S) (lt := lt) (ρ₀ := ρ₀) (s₀ := s₀) (m := m) c P host L
      kont k hm σ.nv hl σ.pc ρ b r fuel := fun s' f' ρ' hR' hE => by
    simpa using ih _ _ _ b _ ρ' s' f' [] hR' (lblsOK_lp hR hL hok hR' hE) hv'.2
  have hinv := invC_of (E := σ.pc) hS hR
    (fun φ hφ => ⟨((fresh_iff σ).mp hR.fresh).2.2.1 φ hφ, hR.pc φ hφ⟩) hv'.1
  cases c with
  | part => exact sound_loopP ih hn hR hL hinv hN hbody
  | total => exact sound_loopT ih hn hR hL hinv hN hbody

section Cases

variable {fuel : Nat} {L : List Lbl} {kont : SSt → List Fm} {k : Nat} {i : Instr}
  {r : List Instr} {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}

theorem cons_block (ih : IH F S lt ρ₀ s₀ m c P host fuel) {bt : BlockType} {b : List Instr}
    (hc : ctl i = .block bt b) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n hn hst =>
    rw [rs_nil hR hst, ctl_block hc]
    exact sound_blockBody ih hn (rs_nil hR hst ▸ hR) hL hv
  next => exact (not_bad hv hR.pc).elim

theorem cons_loop (hS : S.wellScoped = true) (ih : IH F S lt ρ₀ s₀ m c P host fuel)
    {bt : BlockType} {b : List Instr} (hc : ctl i = .loop bt b)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n hn hst =>
    rw [rs_nil hR hst, ctl_loop hc]
    exact sound_loop hS ih hn (rs_nil hR hst ▸ hR) hL hv
  next => exact (not_bad hv hR.pc).elim

theorem cons_if (ih : IH F S lt ρ₀ s₀ m c P host fuel) {bt : BlockType} {b₁ b₂ : List Instr}
    (hc : ctl i = .if_ bt b₁ b₂) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next n x hn hst =>
    have hv' := allValid_append.mp hv
    have hrs : rs.reverse = [] ++ [Val.i32 (x.den F ρ ρ)] := by
      rw [hR.stack, hst]
      rfl
    have hcb : x.vlt σ.nv = true := by
      have := stack_vlt hR
      rw [hst] at this
      exact this _ List.mem_cons_self
    rw [hrs, ctl_if hc]
    refine Wp.ifC (fun h₁ => ?_) (fun h₂ => ?_)
    · exact sound_blockBody (σ := { σ with stack := [], pc := condF x :: σ.pc }) ih hn
        (hR.pcCons ((den_condF ρ ρ x).mpr h₁) (condF_vlt hcb) (by simp)) hL hv'.1
    · exact sound_blockBody (σ := { σ with stack := [], pc := ncondF x :: σ.pc }) ih hn
        (hR.pcCons ((den_ncondF ρ ρ x).mpr h₂) (ncondF_vlt hcb) (by simp)) hL hv'.2
  next => exact (not_bad hv hR.pc).elim

theorem cons_br (hS : S.wellScoped = true) (hT : c = .total → S.total = true) {l : LabelIdx}
    (hc : ctl i = .br l) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hv' : AllValid F (brTo S lt L l.toNat σ) := by simpa only [gen, hc] using hv
  rw [ctl_br hc]
  exact Silmaril.Wasm.Logic.Hoare.Wp.br (m := c) (brTo_post hS hT hR hL hv')

theorem cons_brIf (hS : S.wellScoped = true) (hT : c = .total → S.total = true)
    (ih : IH F S lt ρ₀ s₀ m c P host fuel)
    {l : LabelIdx} (hc : ctl i = .brIf l) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hL : LblsOK F S L ρ σ.nv) (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  simp only [gen, hc] at hv
  split at hv
  next x st hst =>
    have hv' := allValid_append.mp hv
    have hrs : rs.reverse = (dens F ρ st).reverse ++ [Val.i32 (x.den F ρ ρ)] := by
      rw [hR.stack, hst]
      simp [dens, SV.den, Val.i32]
    have hall := stack_vlt hR
    rw [hst] at hall
    have hcb : x.vlt σ.nv = true := hall _ List.mem_cons_self
    have hstb : ∀ v ∈ st, v.vlt σ.nv = true := fun v hv => hall v (List.mem_cons_of_mem _ hv)
    rw [hrs, ctl_brIf hc]
    refine Wp.brIfC (fun h₁ => ?_) (fun h₂ => ?_)
    · exact brTo_post (σ := { σ with stack := st, pc := condF x :: σ.pc }) hS hT
        (hR.pcCons ((den_condF ρ ρ x).mpr h₁) (condF_vlt hcb) hstb) hL hv'.1
    · exact ih _ _ _ r { σ with stack := st, pc := ncondF x :: σ.pc } ρ s f _
        (hR.pcCons ((den_ncondF ρ ρ x).mpr h₂) (ncondF_vlt hcb) hstb) hL hv'.2
  next => exact (not_bad hv hR.pc).elim

/-- `select` on the stack `x :: v₂ :: v₁ :: st` (top first). -/
theorem sound_select (ih : IH F S lt ρ₀ s₀ m c P host fuel) {ts : Option (List ValType)}
    {x : Tm .i32} {v₁ v₂ v : SV} {st : List SV} (hst : σ.stack = .i32 x :: v₂ :: v₁ :: st)
    (hsel : selV x v₁ v₂ = some v) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt fuel L kont k r { σ with stack := v :: st })) :
    Wp c P host s f (vals rs.reverse ++ .plain (.select ts) :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hrs : rs.reverse = (dens F ρ st).reverse ++
      [v₁.den F ρ ρ, v₂.den F ρ ρ, Val.i32 (x.den F ρ ρ)] := by
    rw [hR.stack, hst]
    simp [dens, SV.den, Val.i32]
  have hall := stack_vlt hR
  rw [hst] at hall
  have hvb : v.vlt σ.nv = true := selV_vlt hsel (hall _ List.mem_cons_self)
    (hall _ (by simp)) (hall _ (by simp))
  have hk := ih _ _ _ r { σ with stack := v :: st } ρ s f _ (hR.withStack (st := v :: st) (cons_vlt hvb
    fun u hu => hall u (by simp [hu]))) hL hv
  have hv' := selV_den (F := F) hsel ρ ρ
  rw [hrs]
  by_cases h₀ : x.den F ρ ρ = 0
  · have hv₂ : v.den F ρ ρ = v₂.den F ρ ρ := by
      rw [hv', show nz32 (x.den F ρ ρ) = false by unfold nz32; rw [h₀]; rfl]
      rfl
    rw [h₀]
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectFalse (m := c) (by simpa [dens, hv₂] using hk)
  · have hv₁ : v.den F ρ ρ = v₁.den F ρ ρ := by
      rw [hv', show nz32 (x.den F ρ ρ) = true from (nz32_iff _).mpr h₀]
      rfl
    exact Silmaril.Wasm.Logic.Hoare.Wp.selectTrue (m := c) h₀ (by simpa [dens, hv₁] using hk)

theorem cons_select (ih : IH F S lt ρ₀ s₀ m c P host fuel) (hc : ctl i = .select)
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  obtain ⟨ts, rfl⟩ := ctl_select hc
  simp only [gen, hc] at hv
  split at hv
  next x v₂ v₁ st hst =>
    split at hv
    next v hsel => exact sound_select ih hst hsel hR hL hv
    next => exact (not_bad hv hR.pc).elim
  next => exact (not_bad hv hR.pc).elim

theorem cons_ret (hc : ctl i = .ret) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hv' : AllValid F (retVC S lt σ) := by simpa only [gen, hc] using hv
  rw [ctl_ret hc]
  exact Silmaril.Wasm.Logic.Hoare.Wp.of_exits (m := c) (o := .ret rs.reverse) ⟨_, rfl⟩
    ⟨ρ, σ, by simpa using hR, EqBelow.refl _ _, le_rfl, hv'⟩

theorem bindV_nv (σ : SSt) (v : SV) : σ.nv ≤ (bindV σ v).2.nv := by
  unfold bindV
  split <;> simp

theorem bindV_nvS (σ : SSt) (st : List SV) (v : SV) :
    σ.nv ≤ (bindV { σ with stack := st } v).2.nv := bindV_nv { σ with stack := st } v

set_option linter.unusedTactic false in
/-- Straight-line instructions do not decrease the next fresh variable. -/
theorem step1_nv {S : FnSpec} {lt : List IntType} {i : Instr} {σ σ' : SSt} {side : List Fm}
    (h : step1 S lt i σ = some (σ', side)) : σ.nv ≤ σ'.nv := by
  cases i <;> simp only [step1] at h
  all_goals (repeat' split at h)
  all_goals (try simp only [Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff,
    reduceCtorEq] at h)
  all_goals first
    | done
    | (obtain ⟨rfl, -⟩ := h; first | exact bindV_nvS _ _ _ | (simp; done))
    | (obtain ⟨_, -, rfl, -⟩ := h; simp; done)

theorem plain_call (hS : S.wellScoped = true) (hC : CallsOK c P host F S s₀ m)
    (ih : IH F S lt ρ₀ s₀ m c P host fuel) {x : FuncIdx} {σ₁ σ₂ : SSt} {pre : Fm}
    (h₁ : callStep S lt x.toNat σ = some (σ₁, pre, σ₂))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (vc σ₁ pre :: gen S lt fuel L kont k r σ₂)) :
    Wp c P host s f (vals rs.reverse ++ .plain (.call x) :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hN : σ.nv ≤ σ₂.nv := by
    obtain ⟨C, code, args, st, -, -, -, -, -, -, -, rfl, -, rfl⟩ := callStep_inv h₁
    simp only [callSt₂]
    omega
  exact sound_call hS hC h₁ hR hv.1 fun ρ' s' f' hR' hE =>
    Wp.monoC (ih _ _ _ r σ₂ ρ' s' f' _ hR' (hL.mono hE hN) hv.2) fun _ _ _ h =>
      postOf_mono hE hN hL h

theorem plain_step (ih : IH F S lt ρ₀ s₀ m c P host fuel) {σ' : SSt} {side : List Fm}
    (h₁ : step1 S lt i σ = some (σ', side))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (side.map (vc σ) ++ gen S lt fuel L kont k r σ')) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hv' := allValid_append.mp hv
  have hN : σ.nv ≤ σ'.nv := step1_nv h₁
  exact step1_sound h₁ hR (allValid_map_vc hv'.1 hR.pc) fun ρ' s' f' hR' hE =>
    Wp.monoC (ih _ _ _ r σ' ρ' s' f' _ hR' (hL.mono hE hN) hv'.2) fun _ _ _ h =>
      postOf_mono hE hN hL h

theorem cons_plain (hS : S.wellScoped = true) (hC : CallsOK c P host F S s₀ m)
    (ih : IH F S lt ρ₀ s₀ m c P host fuel) (hc : PlainCtl (ctl i))
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hL : LblsOK F S L ρ σ.nv)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k (i :: r) σ)) :
    Wp c P host s f (vals rs.reverse ++ .plain i :: expression r)
      (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  rcases hc with hc | ⟨_, _, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | hc <;> simp only [gen, hc] at hv
  all_goals
    split at hv
    next x =>
      split at hv
      next σ₁ pre σ₂ h₁ => exact plain_call hS hC ih h₁ hR hL hv
      next => exact (not_bad hv hR.pc).elim
    next =>
      split at hv
      next σ' side h₁ => exact plain_step ih h₁ hR hL hv
      next => exact (not_bad hv hR.pc).elim

theorem sound_nil (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hv : AllValid F (gen S lt (fuel + 1) L kont k [] σ)) :
    Wp c P host s f (vals rs.reverse ++ expression []) (postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont) := by
  have hv' : AllValid F (kont σ) := by simpa only [gen] using hv
  have h := Silmaril.Wasm.Logic.Hoare.Wp.of_vals (m := c) (P := P) (host := host) (s := s) (f := f)
    (vs := rs.reverse) (Q := postOf F S lt ρ₀ s₀ m c ρ σ.nv L kont)
    ⟨ρ, σ, by simpa using hR, EqBelow.refl _ _, le_rfl, hv'⟩
  simpa [expression] using h

end Cases

/-- **Soundness of the generator**, at every `fuel`, in either reading (total correctness needs
the variant conditions, `S.total`). -/
theorem gen_sound (hS : S.wellScoped = true) (hT : c = .total → S.total = true)
    (hC : CallsOK c P host F S s₀ m) : ∀ fuel, IH F S lt ρ₀ s₀ m c P host fuel := by
  intro fuel
  induction fuel with
  | zero => exact fun L kont k is σ ρ s f rs hR _ hv =>
      (not_bad (by simpa [gen] using hv) hR.pc).elim
  | succ fuel ih =>
    intro L kont k is σ ρ s f rs hR hL hv
    cases is with
    | nil => exact sound_nil hR hv
    | cons i r =>
      cases hc : ctl i with
      | block bt b => exact cons_block ih hc hR hL hv
      | loop bt b => exact cons_loop hS ih hc hR hL hv
      | if_ bt b₁ b₂ => exact cons_if ih hc hR hL hv
      | br l => exact cons_br hS hT hc hR hL hv
      | brIf l => exact cons_brIf hS hT ih hc hR hL hv
      | select => exact cons_select ih hc hR hL hv
      | ret => exact cons_ret hc hR hv
      | brTable _ _ | call _ | cvt _ | trap | plain =>
        exact cons_plain hS hC ih (by simp [PlainCtl, hc]) hR hL hv

end Silmaril.Wasm.Auto2.VCGen
