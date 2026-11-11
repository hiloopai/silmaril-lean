module

public import Silmaril.Proofs.Wasm.Auto.VCGen2.Step
public import Silmaril.Proofs.Wasm.Auto.VCGen2.Ren
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# The VC generator with SSA names and memory: calls

`sound_call`: a `call x` to a callee of `S.calls` whose every-run specification holds
(`CallsOK`: the callee is in the entry store, of the same module, and meets
`fspec F S' a' fi'`), run from a configuration related to `σ`, continues in every run with a
configuration related to the generator's state after the call, if the callee's precondition
holds at the call (the condition `callStep` emits). By the call rule
`Silmaril.Wasm.Logic.Hoare.Safe.callIdx`; the arguments and results are fresh variables (`Env.put`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.VCGen2

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.VCGen2
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Safe FSpecValid callPost seqPostK seqPostT Wp Corr TFSpecAt TSafe)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {c : Corr}

/-! ## Putting values into an environment -/

theorem put_eqBelow (ρ : Env) (n : Nat) (vs : List Val) : EqBelow n ρ (ρ.put n vs) := by
  intro i hi
  have : ¬ n ≤ i := by omega
  simp [Env.put, this]

theorem valTy_den (ρ ξ : Env) : ∀ v : SV, valTy (v.den F ρ ξ) = some v.ty
  | .i32 _ => rfl
  | .i64 _ => rfl

theorem valTy_eq_some {v : Val} {t : IntType} (h : valTy v = some t) :
    ∃ x, v = .num ⟨.int t, x⟩ := by
  rcases v with ((u | _) | _) | _ | _ <;> simp only [valTy, reduceCtorEq, Option.some.injEq] at h
  all_goals (cases h; exact ⟨_, rfl⟩)

theorem put_get {ρ : Env} {n j : Nat} {vs : List Val} {t : IntType} {x : BitVec t.width}
    (h : vs[j]? = some (.num ⟨.int t, x⟩)) : (ρ.put n vs).get t (n + j) = x := by
  cases t <;> simp [Env.get, Env.put, h]

theorem getElem_valTy {ts : List IntType} {vs : List Val} (hty : vs.map valTy = ts.map some)
    {j : Nat} (h₁ : j < vs.length) (h₂ : j < ts.length) : valTy vs[j] = some ts[j] := by
  simpa [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] using congrArg (·[j]?) hty

/-- The fresh variables of types `ts` denote the values `vs` they were set to. -/
theorem dens_put_vars {ρ : Env} {n : Nat} {ts : List IntType} {vs : List Val}
    (hty : vs.map valTy = ts.map some) :
    dens F (ρ.put n vs) (varsFrom n ts) = vs := by
  have hlen : vs.length = ts.length := by simpa using congrArg List.length hty
  refine List.ext_getElem (by simp [varsFrom, hlen]) fun j h₁ h₂ => ?_
  have hj : j < ts.length := by simpa [varsFrom] using h₁
  obtain ⟨x, hx⟩ := valTy_eq_some (getElem_valTy hty h₂ hj)
  have hget : vs[j]? = some (.num ⟨.int ts[j], x⟩) := by rw [List.getElem?_eq_getElem h₂, hx]
  simp only [dens, varsFrom, List.getElem_map, List.getElem_mapIdx, SV.den_of, Tm.den,
    put_get hget, hx]

/-- The arguments of a callee, read in its renamed environment, are the values put there. -/
theorem argsOf_put {ρ : Env} {n m : Nat} {C : FnSpec} {vs : List Val}
    (hty : vs.map valTy = C.params.map some) :
    argsOf C (renEnv (ρ.put n vs) n m) = vs := by
  have hlen : vs.length = C.params.length := by simpa using congrArg List.length hty
  refine List.ext_getElem (by simp [argsOf, hlen]) fun j h₁ h₂ => ?_
  have hj : j < C.params.length := by simpa [argsOf] using h₁
  obtain ⟨x, hx⟩ := valTy_eq_some (getElem_valTy hty h₂ hj)
  have hget : vs[j]? = some (.num ⟨.int C.params[j], x⟩) := by
    rw [List.getElem?_eq_getElem h₂, hx]
  simp only [argsOf, List.getElem_mapIdx, renEnv_get, put_get hget, hx]

/-! ## Inverting `callStep` -/

/-- The parts of a call step. -/
theorem callStep_inv {S : FnSpec} {x : Nat} {σ σ₁ σ₂ : SSt} {pre : Fm}
    (h : callStep S x σ = some (σ₁, pre, σ₂)) :
    ∃ C code args st, (x, C, code) ∈ S.calls ∧ (C.mem = true → S.mem = true) ∧ C.calls = [] ∧
      σ.stack = args.reverse ++ st ∧ args.map SV.ty = C.params ∧
      σ₁ = { σ with
        stack := st
        pc := argDefs σ.nv args ++ σ.pc
        nv := σ.nv + C.params.length + C.results.length + 2 } ∧
      pre = C.preF.ren σ.nv (if C.mem then σ.mem else σ.nv + C.params.length + C.results.length) ∧
      σ₂ = { σ₁ with
        stack := (varsFrom (σ.nv + C.params.length) C.results).reverse ++ st
        mem := if C.mem then σ.nv + C.params.length + C.results.length + 1 else σ.mem
        pc := (C.post.ren σ.nv (if C.mem then σ.mem else
            σ.nv + C.params.length + C.results.length)).subst
          (varsFrom (σ.nv + C.params.length) C.results)
          (σ.nv + C.params.length + C.results.length + 1) :: σ₁.pc } := by
  unfold callStep at h
  split at h
  next x' C code hf =>
    have hmem := List.mem_of_find?_eq_some hf
    have hx : x' = x := by simpa using List.find?_some hf
    subst hx
    split at h
    · simp at h
    next hc =>
      split at h
      next args st hp =>
        simp only [popArgs] at hp
        split at hp
        next hp' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hp h
          obtain ⟨rfl, rfl⟩ := hp
          have hc' : (C.mem = true → S.mem = true) ∧ C.calls = [] := by simpa using hc
          refine ⟨C, code, _, _, hmem, hc'.1, hc'.2, ?_, by simpa using hp'.2, h.1.symm,
            h.2.1.symm, ?_⟩
          · rw [List.reverse_reverse, List.take_append_drop]
          · rw [← h.1]
            exact h.2.2.symm
        next => simp at hp
      next => simp at h
  next => simp at h

/-! ## The call -/

section Call

variable {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

theorem EqBelow.trans {n : Nat} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : EqBelow n ρ₁ ρ₂) (h₂ : EqBelow n ρ₂ ρ₃) :
    EqBelow n ρ₁ ρ₃ := fun i hi =>
  ⟨(h₁ i hi).1.trans (h₂ i hi).1, (h₁ i hi).2.1.trans (h₂ i hi).2.1,
    (h₁ i hi).2.2.trans (h₂ i hi).2.2⟩

theorem funcs_setM (s : Store H) (mi : ModuleInst) (B : ByteArray) : (setM s mi B).funcs = s.funcs := by
  unfold setM
  split
  · split
    · rfl
    · rfl
  · rfl

theorem funcs_upd (C : FnSpec) (s : Store H) (mi : ModuleInst) (B : ByteArray) :
    (upd C s mi B).funcs = s.funcs := by
  unfold upd
  split
  · exact funcs_setM s mi B
  · rfl

variable {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val}

/-- Memory `0` of a related configuration. -/
theorem Rel.mem0 (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : S.mem = true) :
    ∃ ma mi, m.mems[0]? = some ma ∧ s.mems[ma]? = some mi ∧ mi.bytes = ρ.mem σ.mem ∧
      ∀ B, s.setMem ma { mi with bytes := B } = upd S s₀ m B := by
  have hok : ∃ ma mi, m.mems[0]? = some ma ∧ s₀.mems[ma]? = some mi ∧ mi.bytes = ρ.mem 0 := by
    simpa only [MemOk, hmem, ↓reduceIte] using hR.memOk
  obtain ⟨ma, mi₀, hm, hs, -⟩ := hok
  have hst : s = s₀.setMem ma { mi₀ with bytes := ρ.mem σ.mem } := by
    simpa only [upd, hmem, ↓reduceIte, setM_some hm hs] using hR.store
  refine ⟨ma, { mi₀ with bytes := ρ.mem σ.mem }, hm, by rw [hst]; exact mems_setMem hs, rfl,
    fun B => ?_⟩
  simp [upd, hmem, setM_some hm hs, hst, setMem_setMem]

/-- The memory of a related configuration, as a callee's memory at entry. -/
theorem Rel.memOk_cur {C : FnSpec} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : S.mem = true)
    (hC : C.mem = true) : MemOk C s m (ρ.mem σ.mem) := by
  obtain ⟨ma, mi, hm, hs, hb, -⟩ := Rel.mem0 hR hmem
  simp only [MemOk, hC, ↓reduceIte]
  exact ⟨ma, mi, hm, hs, hb⟩

/-- The store after the call, if the callee uses memory. -/
theorem upd_call {C : FnSpec} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hmem : S.mem = true) (hC : C.mem = true) : upd C s m B' = upd S s₀ m B' := by
  obtain ⟨ma, mi, hm, hs, -, hupd⟩ := Rel.mem0 hR hmem
  rw [← hupd B']
  simp only [upd, hC, ↓reduceIte, setM_some hm hs]

/-! ### Environments of a call -/

section Env

variable {n e : Nat} {args : List SV} {C : FnSpec}

theorem eqBelow_put_setM {k : Nat} (ρ : Env) (vs : List Val) (B : ByteArray) (hk : k ≤ e) :
    EqBelow k ρ ((ρ.put k vs).setM e B) :=
  EqBelow.trans (put_eqBelow ρ k vs) (EqBelow.mono (eqBelow_setM _ e B) hk)

theorem argsOf_eqBelow {ρ ρ' : Env} {m m' : Nat} (h : EqBelow (n + C.params.length) ρ ρ') :
    argsOf C (renEnv ρ n m) = argsOf C (renEnv ρ' n m') := by
  refine List.ext_getElem (by simp [argsOf]) fun j h₁ _ => ?_
  have hj : j < C.params.length := by simpa [argsOf] using h₁
  simp only [argsOf, List.getElem_mapIdx, renEnv_get,
    EqBelow.get h (show n + j < n + C.params.length by omega)]

theorem argsOf_setM {ρ : Env} {m k : Nat} {B : ByteArray} :
    argsOf C (renEnv (ρ.setM k B) n m) = argsOf C (renEnv ρ n m) := by
  simp [argsOf, renEnv, Env.setM, Env.get]

/-- The definitions of the arguments hold once they are put at `n`. -/
theorem argDefs_den {ρ ρ₁ : Env} (hE : EqBelow n ρ ρ₁)
    (hput : ∀ i (hi : i < args.length), ρ₁.get args[i].ty (n + i) =
      match args[i] with
      | .i32 a => (a.den F ρ ρ : BitVec 32)
      | .i64 a => (a.den F ρ ρ : BitVec 64))
    (hvlt : ∀ v ∈ args, v.vlt n = true) : ∀ φ ∈ argDefs n args, φ.den F ρ₁ ρ₁ := by
  intro φ hφ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hφ
  have hi' : i < args.length := by simpa [argDefs] using hi
  have hv := hvlt _ (List.getElem_mem hi')
  have hp := hput i hi'
  simp only [argDefs, List.getElem_mapIdx]
  rcases h : args[i] with a | a <;> rw [h] at hv hp <;>
    simp only [defF, Fm.den, Silmaril.Wasm.Auto.VCGen.relP, Silmaril.Wasm.Auto.VCGen.relW, Tm.den,
      SV.ty] at hp ⊢ <;> rw [hp, Tm.den_eqBelow hE hE a hv]

theorem argDefs_vlt {N : Nat} (hN : n + args.length ≤ N) (hvlt : ∀ v ∈ args, v.vlt n = true) :
    ∀ φ ∈ argDefs n args, φ.vlt N = true := by
  intro φ hφ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hφ
  have hi' : i < args.length := by simpa [argDefs] using hi
  have := defF_vlt (SV.vlt_mono (show n ≤ n + i by omega) _ (hvlt _ (List.getElem_mem hi')))
  simp only [argDefs, List.getElem_mapIdx]
  exact Fm.vlt_mono (by omega) _ this

theorem varsFrom_vlt {k N : Nat} {ts : List IntType} (h : k + ts.length ≤ N) :
    ∀ v ∈ varsFrom k ts, v.vlt N = true := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hj' : j < ts.length := by simpa [varsFrom] using hj
  simp only [varsFrom, List.getElem_mapIdx, SV.vlt_of, Tm.vlt, decide_eq_true_eq]
  omega

end Env

/-! ### Before and after the call -/

section Main

variable {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}
  {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val} {C : FnSpec} {args st : List SV}

theorem dens_valTy (ρ : Env) (hty : args.map SV.ty = C.params) :
    (dens F ρ args).map valTy = C.params.map some := by
  rw [← hty, dens, List.map_map, List.map_map]
  exact List.map_congr_left fun v _ => valTy_den ρ ρ v

theorem callEnv₁_get (ρ : Env) (n p r : Nat) (i : Nat) (hi : i < args.length) :
    (callEnv₁ F ρ n p r args).get args[i].ty (n + i) =
      match args[i] with
      | .i32 a => (a.den F ρ ρ : BitVec 32)
      | .i64 a => (a.den F ρ ρ : BitVec 64) := by
  have hgi : args[i]? = some args[i] := List.getElem?_eq_getElem hi
  rcases h : args[i] with a | a <;> rw [h] at hgi <;>
    simp [callEnv₁, Env.setM, Env.get, Env.put, SV.ty, hgi, SV.den, dens]

/-- The path condition at the call holds in `callEnv₁`. -/
theorem pc_call₁ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    {p r : Nat} : ∀ φ ∈ argDefs σ.nv args ++ σ.pc,
      φ.den F (callEnv₁ F ρ σ.nv p r args) (callEnv₁ F ρ σ.nv p r args) := by
  have hE : EqBelow σ.nv ρ (callEnv₁ F ρ σ.nv p r args) := eqBelow_put_setM ρ _ _ (by omega)
  obtain ⟨-, hall, hpcb, -⟩ := (fresh_iff σ).mp hR.fresh
  have hargs : ∀ v ∈ args, v.vlt σ.nv = true := fun v hv => hall v (by simp [hst, hv])
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact argDefs_den hE (fun i hi => callEnv₁_get ρ _ _ _ i hi) hargs φ hφ
  · exact (Fm.den_eqBelow hE hE φ (hpcb φ hφ)).mp (hR.pc φ hφ)

/-- The memory of `callEnv₁` at the callee's memory variable at entry. -/
theorem callEnv₁_mem (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) {p r : Nat} :
    (callEnv₁ F ρ σ.nv p r args).mem (if C.mem then σ.mem else σ.nv + p + r) =
      if C.mem then ρ.mem σ.mem else ByteArray.empty := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  by_cases hc : C.mem = true
  · simp [hc, callEnv₁, Env.setM, Env.put, show σ.mem ≠ σ.nv + p + r by omega]
  · simp [hc, callEnv₁, Env.setM]

/-- The callee's memory at entry is the memory it is called with. -/
theorem memOk_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : C.mem = true → S.mem = true)
    {p r : Nat} : MemOk C s m ((callEnv₁ F ρ σ.nv p r args).mem
      (if C.mem then σ.mem else σ.nv + p + r)) := by
  rw [callEnv₁_mem hR]
  by_cases hc : C.mem = true
  · simp only [hc, ↓reduceIte]
    exact Rel.memOk_cur hR (hmem hc) hc
  · simp [MemOk, hc]

/-- **The callee's precondition** at the call. -/
theorem pre_call {a' : Nat} {fi' : FuncInst H} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hty : args.map SV.ty = C.params)
    (hfi : s₀.funcs[a']? = some fi') (hmod : fi'.module = m) (hcalls : C.calls = [])
    (hmem : C.mem = true → S.mem = true) (hsc : C.pre.scoped C.params = true)
    (hpre : (C.preF.ren σ.nv (if C.mem then σ.mem else σ.nv + C.params.length +
      C.results.length)).den F (callEnv₁ F ρ σ.nv C.params.length C.results.length args)
      (callEnv₁ F ρ σ.nv C.params.length C.results.length args)) :
    (fspec F C a' fi').pre s (dens F ρ args) := by
  have hfs : s.funcs = s₀.funcs := by rw [hR.store]; exact funcs_upd S s₀ m _
  refine ⟨by rw [hfs]; exact hfi, fun c hc => by simp [hcalls] at hc,
    renEnv (callEnv₁ F ρ σ.nv C.params.length C.results.length args) σ.nv
      (if C.mem then σ.mem else σ.nv + C.params.length + C.results.length), ?_,
    hmod ▸ memOk_call hR hmem, ?_⟩
  · rw [callEnv₁, argsOf_setM, argsOf_put (dens_valTy ρ hty)]
  · exact (preF_den_iff _ _ _).mp ((Fm.den_ren _ _ _ _ _ (Fm.scoped_subst_nil _ hsc)).mp hpre)

theorem dens_callEnv₂ {ρ₁ : Env} {n p : Nat} {res : List Val} {B' : ByteArray}
    (hres : res.map valTy = C.results.map some) :
    dens F (callEnv₂ ρ₁ n p C.results.length res B') (varsFrom (n + p) C.results) = res := by
  have hE : EqBelow (n + p + C.results.length + 1) (ρ₁.put (n + p) res)
      (callEnv₂ ρ₁ n p C.results.length res B') := eqBelow_setM _ _ _
  refine (List.map_congr_left fun v hv => ?_).trans (dens_put_vars (F := F) (ρ := ρ₁) hres)
  exact (SV.den_eqBelow hE hE v (varsFrom_vlt (by omega) v hv)).symm

/-- The callee's postcondition, as the path condition after the call. -/
theorem post_call {ρ₁ : Env} {n m₀ : Nat} {res : List Val} {B' : ByteArray}
    (hsc : C.post.scoped C.params = true) (hres : res.map valTy = C.results.map some)
    (hpost : C.post.den F (renEnv (callEnv₂ ρ₁ n C.params.length C.results.length res B') n m₀)
      (valEnv res B')) :
    ((C.post.ren n m₀).subst (varsFrom (n + C.params.length) C.results)
      (n + C.params.length + C.results.length + 1)).den F
      (callEnv₂ ρ₁ n C.params.length C.results.length res B')
      (callEnv₂ ρ₁ n C.params.length C.results.length res B') := by
  have hd : List.map (SV.den F (callEnv₂ ρ₁ n C.params.length C.results.length res B')
      (callEnv₂ ρ₁ n C.params.length C.results.length res B'))
      (varsFrom (n + C.params.length) C.results) = res := dens_callEnv₂ hres
  rw [Fm.den_subst, Fm.den_ren _ _ _ _ _ hsc, locEnv_eq_valEnv, hd]
  simpa [callEnv₂, Env.setM] using hpost

theorem callM₀_lt (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    callM₀ σ C < σ.nv + C.params.length + C.results.length + 1 := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  unfold callM₀
  split <;> omega

/-- The state after the call is fresh. -/
theorem fresh_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params) (hsc : C.post.scoped C.params = true) :
    (callSt₂ σ C args st).fresh = true := by
  obtain ⟨hl, hall, hpcb, hm⟩ := (fresh_iff σ).mp hR.fresh
  have hlen : args.length = C.params.length := by simpa using congrArg List.length hty
  have hargs : ∀ v ∈ args, v.vlt σ.nv = true := fun v hv => hall v (by simp [hst, hv])
  have hst' : ∀ v ∈ st, v.vlt σ.nv = true := fun v hv => hall v (by simp [hst, hv])
  have hN : σ.nv ≤ (callSt₂ σ C args st).nv := by simp only [callSt₂]; omega
  have hres := varsFrom_vlt (N := (callSt₂ σ C args st).nv) (k := σ.nv + C.params.length)
    (ts := C.results) (by simp only [callSt₂]; omega)
  have hφ := Fm.vlt_ren_subst (N := (callSt₂ σ C args st).nv) (n := σ.nv) (m := callM₀ σ C)
    (cm := σ.nv + C.params.length + C.results.length + 1) (ls := varsFrom (σ.nv +
      C.params.length) C.results) (by simp only [callSt₂]; omega)
    (by have := callM₀_lt (C := C) hR; simp only [callSt₂]; omega)
    (by simp only [callSt₂]; omega) hres C.post hsc
  refine (fresh_iff _).mpr ⟨fun v hv => SV.vlt_mono hN v (hl v hv), ?_, ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hres v (List.mem_reverse.mp hv)
    · exact SV.vlt_mono hN v (hst' v hv)
  · refine vlt_ext le_rfl (fun ψ hψ => ?_) hφ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact argDefs_vlt (by simp only [callSt₂]; omega) hargs ψ hψ
    · exact Fm.vlt_mono hN ψ (hpcb ψ hψ)
  · simp only [callSt₂]
    split <;> omega

theorem eqBelow_call₁₂ (ρ : Env) (res : List Val) (B' : ByteArray) :
    EqBelow (σ.nv + C.params.length) (callEnv₁ F ρ σ.nv C.params.length C.results.length args)
      (callEnv F ρ σ C args res B') :=
  eqBelow_put_setM _ _ _ (by omega)

theorem eqBelow_call (ρ : Env) (res : List Val) (B' : ByteArray) :
    EqBelow σ.nv ρ (callEnv F ρ σ C args res B') :=
  EqBelow.trans (eqBelow_put_setM ρ _ _ (by omega))
    (EqBelow.mono (eqBelow_call₁₂ ρ res B') (by omega))

/-- The store after the call is the one related to the state after the call. -/
theorem store_call {res : List Val} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hmem : C.mem = true → S.mem = true) :
    upd C s m B' = upd S s₀ m ((callEnv F ρ σ C args res B').mem (callSt₂ σ C args st).mem) := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  by_cases hc : C.mem = true
  · rw [upd_call hR (hmem hc) hc]
    simp [callSt₂, hc, callEnv, callEnv₂, Env.setM]
  · have hE := eqBelow_call (F := F) (σ := σ) (C := C) (args := args) ρ res B'
    simp only [callSt₂, hc, Bool.false_eq_true, ↓reduceIte, ← (hE σ.mem hm).2.2]
    simpa [upd, hc] using hR.store

/-- **The configuration after the call** is related to the state after the call. -/
theorem rel_call₂ {res : List Val} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hst : σ.stack = args.reverse ++ st) (hty : args.map SV.ty = C.params)
    (hmem : C.mem = true → S.mem = true) (hsc : C.post.scoped C.params = true)
    (hres : res.map valTy = C.results.map some)
    (hpost : C.post.den F (renEnv (callEnv F ρ σ C args res B') σ.nv (callM₀ σ C))
      (valEnv res B')) :
    Rel F S lt ρ₀ s₀ m (callEnv F ρ σ C args res B') (callSt₂ σ C args st) (upd C s m B') f
      (dens F (callEnv F ρ σ C args res B') (callSt₂ σ C args st).stack) := by
  obtain ⟨hl, -, hpcb, -⟩ := (fresh_iff σ).mp hR.fresh
  have hE := eqBelow_call (F := F) (σ := σ) (C := C) (args := args) ρ res B'
  have hE₁₂ := eqBelow_call₁₂ (F := F) (σ := σ) (C := C) (args := args) ρ res B'
  have hlen : args.length = C.params.length := by simpa using congrArg List.length hty
  have hargs : ∀ v ∈ args, v.vlt σ.nv = true :=
    fun v hv => ((fresh_iff σ).mp hR.fresh).2.1 v (by simp [hst, hv])
  have hpc₁ := pc_call₁ (F := F) (p := C.params.length) (r := C.results.length) hR hst
  have hold : ∀ φ ∈ argDefs σ.nv args ++ σ.pc, φ.vlt (σ.nv + C.params.length) = true := by
    intro φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact argDefs_vlt (by omega) hargs φ hφ
    · exact Fm.vlt_mono (by omega) φ (hpcb φ hφ)
  exact { store := store_call hR hmem
          memOk := by rw [← (hE 0 (by have := hR.pnv; omega)).2.2]; exact hR.memOk
          modl := hR.modl
          locals := by
            rw [hR.locals]
            exact List.map_congr_left fun w hw => congrArg some (SV.den_eqBelow hE hE w (hl w hw))
          stack := rfl
          types := hR.types
          agree := Agree.trans (Agree.symm (agree_of_eqBelow hE hR.pnv)) hR.agree
          pc := pc_ext hE₁₂ hpc₁ hold (post_call hsc hres hpost)
          fresh := fresh_call₂ hR hst hty hsc
          pnv := by simp only [callSt₂]; have := hR.pnv; omega
          pre := hR.pre }

/-- The arguments, read in the callee's environment after the call. -/
theorem argsOf_call (hty : args.map SV.ty = C.params) (ρ : Env) (res : List Val)
    (B' : ByteArray) :
    argsOf C (renEnv (callEnv F ρ σ C args res B') σ.nv (callM₀ σ C)) = dens F ρ args := by
  rw [← argsOf_eqBelow (m := callM₀ σ C) (eqBelow_call₁₂ ρ res B'), callEnv₁, argsOf_setM,
    argsOf_put (dens_valTy ρ hty)]

/-- The callee's memory at entry, read after the call. -/
theorem memOk_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : C.mem = true → S.mem = true)
    (res : List Val) (B' : ByteArray) :
    MemOk C s m ((renEnv (callEnv F ρ σ C args res B') σ.nv (callM₀ σ C)).mem 0) := by
  have hlt := callM₀_lt (C := C) hR
  have h : (callEnv F ρ σ C args res B').mem (callM₀ σ C) =
      (callEnv₁ F ρ σ.nv C.params.length C.results.length args).mem (callM₀ σ C) := by
    simp [callEnv, callEnv₂, Env.setM, Env.put, show callM₀ σ C ≠
      σ.nv + C.params.length + C.results.length + 1 by omega]
  simp only [renEnv, h]
  exact memOk_call hR hmem

/-- The stack after the call. -/
theorem stack_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    {res : List Val} {B' : ByteArray} (hres : res.map valTy = C.results.map some) :
    (dens F (callEnv F ρ σ C args res B') (callSt₂ σ C args st).stack).reverse =
      (dens F ρ st).reverse ++ res := by
  have hE := eqBelow_call (F := F) (σ := σ) (C := C) (args := args) ρ res B'
  have hst' : dens F (callEnv F ρ σ C args res B') st = dens F ρ st :=
    List.map_congr_left fun v hv =>
      (SV.den_eqBelow hE hE v (((fresh_iff σ).mp hR.fresh).2.1 v (by simp [hst, hv]))).symm
  have hd : dens F (callEnv F ρ σ C args res B') (varsFrom (σ.nv + C.params.length) C.results) =
      res := dens_callEnv₂ hres
  simp only [callSt₂, dens, List.map_append, List.map_reverse, List.reverse_append,
    List.reverse_reverse] at hst' hd ⊢
  rw [hst', hd]

/-- The callee's normal outcomes, seen after the call: the continuation from the state after
the call. -/
theorem seqPost_call {a' : Nat} {fi' : FuncInst H} {rest : List Admin} {Q : Post H}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params) (hmem : C.mem = true → S.mem = true)
    (hqsc : C.post.scoped C.params = true) (hmod : fi'.module = m)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv (callSt₂ σ C args st) rest Q) :
    ∀ s' o, callPost f (dens F ρ st).reverse ((fspec F C a' fi').post s (dens F ρ args)) s' f o →
      ∃ res, o = .normal ((dens F ρ st).reverse ++ res) ∧
        Wp c P host s' f (vals ((dens F ρ st).reverse ++ res) ++ rest) Q := by
  rintro s' o ⟨-, ⟨res, rfl, B', hs', res', hres', hlen, htys, hp⟩ | ⟨rfl, B', -, res', h', -⟩ |
    ⟨a, rfl, B', -, res', h', -⟩⟩
  · obtain rfl : res = res' := Outcome.normal.inj hres'
    have hrel := rel_call₂ (st := st) hR hst hty hmem hqsc htys
      (hp _ (argsOf_call hty ρ res B').symm (hmod ▸ memOk_call₂ hR hmem res B'))
    have hk' : Wp c P host s' f (vals (dens F (callEnv F ρ σ C args res B')
        (callSt₂ σ C args st).stack).reverse ++ rest) Q :=
      hk _ s' f (by rw [hs', hmod]; exact hrel) (eqBelow_call ρ res B')
    rw [stack_call hR hst htys] at hk'
    exact ⟨res, rfl, hk'⟩
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)

/-- The call rule in either reading: the callee's specification (`SpecOK c`) and the
continuation after each normal outcome. -/
theorem callIdx_wp {x : FuncIdx} {a' : Nat} {fi' : FuncInst H} {Sp : Silmaril.Wasm.Logic.Hoare.FSpec H}
    {vs₀ args : List Val} {rest : List Admin} {Q : Post H} (hx : f.module.funcs[x.toNat]? = some a')
    (hf : s.funcs[a']? = some fi') (hval : SpecOK c P host a' Sp) (hpre : Sp.pre s args)
    (hq : ∀ s' o, callPost f vs₀ (Sp.post s args) s' f o →
      ∃ res, o = .normal (vs₀ ++ res) ∧ Wp c P host s' f (vals (vs₀ ++ res) ++ rest) Q) :
    Wp c P host s f (vals (vs₀ ++ args) ++ .plain (.call x) :: rest) Q := by
  cases c with
  | part =>
    intro N
    cases N with
    | zero => trivial
    | succ N =>
      refine Silmaril.Wasm.Logic.Hoare.Safe.callIdx hx hf (hval N) hpre fun s' o ho => ?_
      obtain ⟨res, rfl, hw⟩ := hq s' o ho
      exact hw N
  | total =>
    refine Silmaril.Wasm.Logic.Hoare.TSafe.callIdx hx hf hval hpre fun s' o ho => ?_
    obtain ⟨res, rfl, hw⟩ := hq s' o ho
    exact hw

/-- **A call**, every run: the callee's precondition holds at the call, and its every-run
specification gives the configurations after the call, related to the generator's state. -/
theorem sound_call {x : FuncIdx} {σ₁ σ₂ : SSt} {pre : Fm} {rest : List Admin} {Q : Post H}
    (hS : S.wellScoped = true) (hC : CallsOK c P host F S s₀ m)
    (h : callStep S x.toNat σ = some (σ₁, pre, σ₂)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hpre : Valid F (vc σ₁ pre)) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ₂ rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.call x) :: rest) Q := by
  obtain ⟨C, code, args, st, hmemC, hmem, hcalls, hst, hty, rfl, rfl, rfl⟩ := callStep_inv h
  obtain ⟨a', fi', hx, hfi, hmod, hval⟩ := hC _ hmemC
  have hsc : C.pre.scoped C.params = true ∧ C.post.scoped C.params = true :=
    wellScoped_calls hS _ hmemC
  have hpreC : (fspec F C a' fi').pre s (dens F ρ args) :=
    pre_call hR hty hfi hmod hcalls hmem hsc.1 (vc_holds hpre (pc_call₁ hR hst))
  have hrs : rs.reverse = (dens F ρ st).reverse ++ dens F ρ args := by
    rw [hR.stack, hst]
    simp [dens, List.map_reverse]
  have hx' : f.module.funcs[x.toNat]? = some a' := by rw [hR.modl]; exact hx
  have hf : s.funcs[a']? = some fi' := by rw [hR.store, funcs_upd]; exact hfi
  rw [hrs]
  exact callIdx_wp hx' hf hval hpreC (seqPost_call (a' := a') (fi' := fi') hR hst hty hmem hsc.2
    hmod hk)

end Main

end Call

end Silmaril.Proofs.Wasm.Auto.VCGen2