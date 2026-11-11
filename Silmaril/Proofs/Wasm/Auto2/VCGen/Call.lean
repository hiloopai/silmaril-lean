module

public import Silmaril.Proofs.Wasm.Auto2.VCGen.Step
public import Silmaril.Proofs.Wasm.Auto2.VCGen.Ren
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

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Logic.Hoare (HWP Safe FSpecValid callPost seqPostK seqPostT Wp Corr TFSpecAt TSafe)

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : Fns} {c : Corr}

/-! ## Putting values into an environment -/

/-- `ρ` with the variables `n + j` set to the integer values `vs[j]`. -/
def Env.put (ρ : Env) (n : Nat) (vs : List Val) : Env where
  e32 i := if n ≤ i then
      (match vs[i - n]? with
        | some (.num ⟨.int .i32, x⟩) => x
        | _ => ρ.e32 i)
    else ρ.e32 i
  e64 i := if n ≤ i then
      (match vs[i - n]? with
        | some (.num ⟨.int .i64, x⟩) => x
        | _ => ρ.e64 i)
    else ρ.e64 i
  mem := ρ.mem

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

/-- The values a call binds at `σ.nv`: the arguments, then the current values of the callee's
globals (the caller's symbolic locals from `S.nl lt` on). -/
def callIns (S : FnSpec) (lt : List IntType) (σ : SSt) (C : FnSpec) (args : List SV) : List SV :=
  args ++ (σ.locals.drop (S.nl lt)).take C.globals.length

/-- The number of outputs of a call: its results, then its final globals. -/
abbrev callR (C : FnSpec) : Nat := C.results.length + C.globals.length

/-- The outputs of a call: fresh variables for its results, then for its final globals. -/
def callOuts (σ : SSt) (C : FnSpec) : List SV :=
  varsFrom (σ.nv + C.ents.length) (C.results ++ C.globals)

/-- The callee's memory variable at entry at a call from `σ`. -/
def callM₀ (σ : SSt) (C : FnSpec) : Nat :=
  if C.mem then σ.mem else σ.nv + C.ents.length + callR C

/-- The state after a call (`callStep`'s third component). -/
def callSt₂ (S : FnSpec) (lt : List IntType) (σ : SSt) (C : FnSpec) (args st : List SV) : SSt :=
  { locals := σ.locals.take (S.nl lt) ++ (callOuts σ C).drop C.results.length ++
      σ.locals.drop (S.nl lt + C.globals.length)
    stack := ((callOuts σ C).take C.results.length).reverse ++ st
    pc := (C.post.ren σ.nv (callM₀ σ C)).subst (callOuts σ C)
        (σ.nv + C.ents.length + callR C + 1) :: (argDefs σ.nv (callIns S lt σ C args) ++ σ.pc)
    nv := σ.nv + C.ents.length + callR C + 2
    mem := if C.mem then σ.nv + C.ents.length + callR C + 1 else σ.mem }

/-- The parts of a call step. -/
theorem callStep_inv {S : FnSpec} {lt : List IntType} {x : Nat} {σ σ₁ σ₂ : SSt} {pre : Fm}
    (h : callStep S lt x σ = some (σ₁, pre, σ₂)) :
    ∃ C code args st, (x, C, code) ∈ S.calls ∧ (C.mem = true → S.mem = true) ∧ C.calls = [] ∧
      C.globals <+: S.globals ∧ σ.stack = args.reverse ++ st ∧ args.map SV.ty = C.params ∧
      ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals ∧
      σ₁ = { σ with
        stack := st
        pc := argDefs σ.nv (callIns S lt σ C args) ++ σ.pc
        nv := σ.nv + C.ents.length + callR C + 2 } ∧
      pre = C.preF.ren σ.nv (callM₀ σ C) ∧ σ₂ = callSt₂ S lt σ C args st := by
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
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          split at h
          next hg =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            have hc' : (C.mem = true → S.mem = true) ∧ C.calls = [] ∧ C.globals <+: S.globals := by
              simpa [and_assoc, List.isPrefixOf_iff_prefix] using hc
            refine ⟨C, code, _, _, hmem, hc'.1, hc'.2.1, hc'.2.2, ?_, by simpa using hp'.2, hg,
              h.1.symm, h.2.1.symm, ?_⟩
            · rw [List.reverse_reverse, List.take_append_drop]
            · rw [← h.2.2]
              rfl
          next => simp at h
        next => simp at hp
      next => simp at h
  next => simp at h

/-! ## The call -/

section Call

variable {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}

/-- A function specification holds in reading `c`: every-run partial correctness
(`FSpecValid`) or total correctness (`TFSpecAt`). -/
def SpecOK (c : Corr) (P : Profile) (host : HostSemantics H) (a : Nat)
    (S : Silmaril.Wasm.Logic.Hoare.FSpec H) : Prop :=
  match c with
  | .part => FSpecValid P host a S
  | .total => TFSpecAt P host a S

/-- `fspec` for calls from a store with the functions of `s₀` (round 2, pass 3: what a call
needs of its callee, so that a function can be its own callee, `genFunc_tsound_rec`). -/
def fspecIn (F : Fns) (S : FnSpec) (a : Nat) (fi : FuncInst H) (s₀ : Store H) :
    Silmaril.Wasm.Logic.Hoare.FSpec H where
  pre s args := (fspec F S a fi).pre s args ∧ s.funcs = s₀.funcs
  post := (fspec F S a fi).post

/-- A specification for every store gives it for the stores with the functions of `s₀`. -/
theorem SpecOK.fspecIn {c : Corr} {P : Profile} {host : HostSemantics H} {F : Fns} {S : FnSpec}
    {a : Nat} {fi : FuncInst H} (h : SpecOK c P host a (fspec F S a fi)) (s₀ : Store H) :
    SpecOK c P host a (fspecIn F S a fi s₀) := by
  cases c
  · exact fun n s args hp => h n s args hp.1
  · exact fun s args hp => h s args hp.1

/-- The callees of `S` meet their specifications (in reading `c`, for calls from a store with the
functions of `s₀`) and are in the entry store `s₀`. -/
def CallsOK (c : Corr) (P : Profile) (host : HostSemantics H) (F : Fns) (S : FnSpec)
    (s₀ : Store H) (m : ModuleInst) : Prop :=
  ∀ e ∈ S.calls, ∃ a' fi', m.funcs[e.1]? = some a' ∧ s₀.funcs[a']? = some fi' ∧
    fi'.module = m ∧ SpecOK c P host a' (fspecIn F e.2.1 a' fi' s₀)

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
      ∀ B, s.setMem ma { mi with bytes := B } = setGs (upd S s₀ m B) m (globs F S lt ρ σ) := by
  have hok : ∃ ma mi, m.mems[0]? = some ma ∧ s₀.mems[ma]? = some mi ∧ mi.bytes = ρ.mem 0 := by
    simpa only [MemOk, hmem, ↓reduceIte] using hR.memOk
  obtain ⟨ma, mi₀, hm, hs, -⟩ := hok
  have hst : s = setGs (s₀.setMem ma { mi₀ with bytes := ρ.mem σ.mem }) m (globs F S lt ρ σ) := by
    simpa only [upd, hmem, ↓reduceIte, setM_some hm hs] using hR.store
  refine ⟨ma, { mi₀ with bytes := ρ.mem σ.mem }, hm, by rw [hst, setGs_mems]; exact mems_setMem hs,
    rfl, fun B => ?_⟩
  simp [upd, hmem, setM_some hm hs, hst, setGs_setMem, setMem_setMem]

/-- The memory of a related configuration, as a callee's memory at entry. -/
theorem Rel.memOk_cur {C : FnSpec} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : S.mem = true)
    (hC : C.mem = true) : MemOk C s m (ρ.mem σ.mem) := by
  obtain ⟨ma, mi, hm, hs, hb, -⟩ := hR.mem0 hmem
  simp only [MemOk, hC, ↓reduceIte]
  exact ⟨ma, mi, hm, hs, hb⟩

/-- The store after the call, if the callee uses memory. -/
theorem upd_call {C : FnSpec} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hmem : S.mem = true) (hC : C.mem = true) :
    upd C s m B' = setGs (upd S s₀ m B') m (globs F S lt ρ σ) := by
  obtain ⟨ma, mi, hm, hs, -, hupd⟩ := hR.mem0 hmem
  rw [← hupd B']
  simp only [upd, hC, ↓reduceIte, setM_some hm hs]

/-- Global `g` of a related configuration holds its symbolic value. -/
theorem Rel.globalAt {g : Nat} {v : SV} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hg : g < S.globals.length) (hv : σ.locals[S.nl lt + g]? = some v) :
    ∃ a gi, m.globals[g]? = some a ∧ s.globals[a]? = some gi ∧ gi.value = v.den F ρ ρ := by
  obtain ⟨t, ht⟩ : ∃ t, S.globals[g]? = some t := ⟨_, List.getElem?_eq_getElem hg⟩
  obtain ⟨a, gi, ha, hs, -⟩ := hR.globOk.2 _ _ ht
  have hg' : g < (globs F S lt ρ σ).length := by rw [length_globs hR]; exact hg
  have hs' : (upd S s₀ m (ρ.mem σ.mem)).globals[a]? = some gi := by rw [globals_upd]; exact hs
  have hG : (globs F S lt ρ σ)[g] = v.den F ρ ρ := by
    have h₁ : (globs F S lt ρ σ)[g]? = some (v.den F ρ ρ) := by
      simp [globs, dens, List.getElem?_drop, hv]
    exact Option.some.inj ((List.getElem?_eq_getElem hg').symm.trans h₁)
  have hset := globals_setGs (s := upd S s₀ m (ρ.mem σ.mem)) (distinct_globs hR) hg' ha hs'
  rw [hG, ← hR.store] at hset
  exact ⟨a, _, ha, hset, rfl⟩

/-! ### Environments of a call -/

section Env

variable {n e : Nat} {args : List SV} {C : FnSpec}

theorem eqBelow_put_setM {k : Nat} (ρ : Env) (vs : List Val) (B : ByteArray) (hk : k ≤ e) :
    EqBelow k ρ ((ρ.put k vs).setM e B) :=
  (put_eqBelow ρ k vs).trans ((eqBelow_setM _ e B).mono hk)

theorem argsOf_eqBelow {ρ ρ' : Env} {m m' : Nat} (h : EqBelow (n + C.params.length) ρ ρ') :
    argsOf C (renEnv ρ n m) = argsOf C (renEnv ρ' n m') := by
  refine List.ext_getElem (by simp [argsOf]) fun j h₁ _ => ?_
  have hj : j < C.params.length := by simpa [argsOf] using h₁
  simp only [argsOf, List.getElem_mapIdx, renEnv_get, h.get (show n + j < n + C.params.length by
    omega)]

theorem argsOf_setM {ρ : Env} {m k : Nat} {B : ByteArray} :
    argsOf C (renEnv (ρ.setM k B) n m) = argsOf C (renEnv ρ n m) := by
  simp [argsOf, renEnv, Env.setM, Env.get]

/-- The arguments of a callee, read in its renamed environment, are the first values put
there (the others are the entry values of its globals). -/
theorem argsOf_put' {ρ : Env} {m : Nat} {vs : List Val} (hty : vs.map valTy = C.ents.map some) :
    argsOf C (renEnv (ρ.put n vs) n m) = vs.take C.params.length := by
  have hlen : vs.length = C.ents.length := by simpa using congrArg List.length hty
  have hpe : C.params.length ≤ C.ents.length := by simp [FnSpec.ents]
  refine List.ext_getElem (by simp [argsOf]; omega) fun j h₁ h₂ => ?_
  have hj : j < C.params.length := by simpa [argsOf] using h₁
  have hjv : j < vs.length := by omega
  have hje : j < C.ents.length := by omega
  have hent : C.ents[j] = C.params[j] := by
    simp only [FnSpec.ents]
    exact List.getElem_append_left hj
  have hv : valTy vs[j] = some C.params[j] := (getElem_valTy hty hjv hje).trans (by rw [hent])
  obtain ⟨x, hx⟩ := valTy_eq_some hv
  have hget : vs[j]? = some (.num ⟨.int C.params[j], x⟩) := by
    rw [List.getElem?_eq_getElem hjv, hx]
  simp only [argsOf, List.getElem_mapIdx, renEnv_get, put_get hget, List.getElem_take, hx]

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

theorem varsFrom_ty {k : Nat} {ts : List IntType} : (varsFrom k ts).map SV.ty = ts := by
  refine List.ext_getElem (by simp [varsFrom]) fun j h₁ h₂ => ?_
  simp [varsFrom, SV.ty_of]

end Env

/-! ### Before and after the call -/

section Main

variable {S : FnSpec} {lt : List IntType} {ρ₀ : Env} {s₀ : Store H} {m : ModuleInst}
  {σ : SSt} {ρ : Env} {s : Store H} {f : Frame} {rs : List Val} {C : FnSpec} {args st : List SV}

/-- The environment at the call: the values bound at `σ.nv`, the callee's memory at entry (when
it does not use memory) empty. -/
def callEnv₁ (F : Fns) (ρ : Env) (n p r : Nat) (args : List SV) : Env :=
  (ρ.put n (dens F ρ args)).setM (n + p + r) ByteArray.empty

theorem dens_valTy {ts : List IntType} (ρ : Env) (hty : args.map SV.ty = ts) :
    (dens F ρ args).map valTy = ts.map some := by
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

/-- The values a call binds are fresh-free: below `σ.nv`. -/
theorem callIns_vlt (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st) :
    ∀ v ∈ callIns S lt σ C args, v.vlt σ.nv = true := by
  obtain ⟨hl, hall, -, -⟩ := (fresh_iff σ).mp hR.fresh
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hall v (by simp [hst, hv])
  · exact hl v (List.mem_of_mem_drop (List.mem_of_mem_take hv))

theorem callIns_ty (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals) :
    (callIns S lt σ C args).map SV.ty = C.ents := by
  simp only [callIns, List.map_append, hty, hgty, FnSpec.ents]

theorem callIns_length (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals) :
    (callIns S lt σ C args).length = C.ents.length := by
  simpa using congrArg List.length (callIns_ty hty hgty)

/-- The path condition at the call holds in `callEnv₁`. -/
theorem pc_call₁ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) {ins : List SV}
    (hins : ∀ v ∈ ins, v.vlt σ.nv = true) {p r : Nat} : ∀ φ ∈ argDefs σ.nv ins ++ σ.pc,
      φ.den F (callEnv₁ F ρ σ.nv p r ins) (callEnv₁ F ρ σ.nv p r ins) := by
  have hE : EqBelow σ.nv ρ (callEnv₁ F ρ σ.nv p r ins) := eqBelow_put_setM ρ _ _ (by omega)
  obtain ⟨-, -, hpcb, -⟩ := (fresh_iff σ).mp hR.fresh
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact argDefs_den hE (fun i hi => callEnv₁_get ρ _ _ _ i hi) hins φ hφ
  · exact (Fm.den_eqBelow hE hE φ (hpcb φ hφ)).mp (hR.pc φ hφ)

/-- The memory of `callEnv₁` at the callee's memory variable at entry. -/
theorem callEnv₁_mem (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) {p r : Nat} {ins : List SV} :
    (callEnv₁ F ρ σ.nv p r ins).mem (if C.mem then σ.mem else σ.nv + p + r) =
      if C.mem then ρ.mem σ.mem else ByteArray.empty := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  by_cases hc : C.mem = true
  · simp [hc, callEnv₁, Env.setM, Env.put, show σ.mem ≠ σ.nv + p + r by omega]
  · simp [hc, callEnv₁, Env.setM]

/-- The callee's memory at entry is the memory it is called with. -/
theorem memOk_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : C.mem = true → S.mem = true)
    {p r : Nat} {ins : List SV} : MemOk C s m ((callEnv₁ F ρ σ.nv p r ins).mem
      (if C.mem then σ.mem else σ.nv + p + r)) := by
  rw [callEnv₁_mem hR]
  by_cases hc : C.mem = true
  · simp only [hc, ↓reduceIte]
    exact hR.memOk_cur (hmem hc) hc
  · simp [MemOk, hc]

theorem env_get_setM (ρ : Env) (k : Nat) (B : ByteArray) (t : IntType) (i : Nat) :
    (ρ.setM k B).get t i = ρ.get t i := by
  cases t <;> rfl

/-- **The callee's globals at the call**: distinct (the caller's), holding the values bound at
`σ.nv + C.params.length + g`, in any environment agreeing with `callEnv₁` below the bound
values. -/
theorem globOk_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hpre : C.globals <+: S.globals) {r m' : Nat} {ρ' : Env}
    (hE : EqBelow (σ.nv + C.ents.length)
      (callEnv₁ F ρ σ.nv C.ents.length r (callIns S lt σ C args)) ρ') :
    GlobOk C s m (renEnv ρ' σ.nv m') := by
  have hk : C.globals.length ≤ S.globals.length := hpre.length_le
  have hlen : args.length = C.params.length := by simpa using congrArg List.length hty
  refine ⟨fun g g' a hg hg' ha ha' => hR.globOk.1 g g' a (by omega) (by omega) ha ha', ?_⟩
  intro g t ht
  have hg : g < C.globals.length := (List.getElem?_eq_some_iff.mp ht).1
  have hlocs : σ.locals.length = lt.length := by simpa using congrArg List.length hR.types
  have hnl : S.nl lt + g < σ.locals.length := by
    have := hR.glen
    simp only [FnSpec.nl]
    omega
  obtain ⟨a, gi, ha, hs, hval⟩ := hR.globalAt (v := σ.locals[S.nl lt + g]) (by omega)
    (List.getElem?_eq_getElem hnl)
  have hgt : σ.locals[S.nl lt + g].ty = t := by
    have h₁ := congrArg (·[g]?) hgty
    simp only [List.getElem?_map, List.getElem?_take, hg, ↓reduceIte, List.getElem?_drop,
      List.getElem?_eq_getElem hnl, Option.map_some, ht, Option.some.injEq] at h₁
    exact h₁
  obtain ⟨x, hx⟩ := valTy_eq_some ((valTy_den (F := F) ρ ρ σ.locals[S.nl lt + g]).trans
    (congrArg some hgt))
  have hins : (dens F ρ (callIns S lt σ C args))[C.params.length + g]? =
      some (.num ⟨.int t, x⟩) := by
    simp only [callIns, dens, List.getElem?_map, List.getElem?_append_right (by omega : args.length
      ≤ C.params.length + g), hlen, Nat.add_sub_cancel_left, List.getElem?_take, hg, ↓reduceIte,
      List.getElem?_drop, List.getElem?_eq_getElem hnl, Option.map_some, hx]
  have hget : (renEnv ρ' σ.nv m').get t (C.params.length + g) = x := by
    rw [renEnv_get, ← hE.get (by simp [FnSpec.ents]; omega) t, callEnv₁, env_get_setM]
    exact put_get hins
  exact ⟨a, gi, ha, hs, by rw [hval, hx, hget]⟩

/-- **The callee's precondition** at the call. -/
theorem pre_call {a' : Nat} {fi' : FuncInst H} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hpg : C.globals <+: S.globals)
    (hfi : s₀.funcs[a']? = some fi') (hmod : fi'.module = m) (hcalls : C.calls = [])
    (hmem : C.mem = true → S.mem = true) (hsc : C.pre.scoped C.ents = true)
    (hpre : (C.preF.ren σ.nv (callM₀ σ C)).den F
      (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args))
      (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args))) :
    (fspecIn F C a' fi' s₀).pre s (dens F ρ args) := by
  have hfs : s.funcs = s₀.funcs := by rw [hR.store, setGs_funcs]; exact funcs_upd S s₀ m _
  have hlen : args.length = C.params.length := by simpa using congrArg List.length hty
  have hargs : argsOf C (renEnv (callEnv₁ F ρ σ.nv C.ents.length (callR C)
      (callIns S lt σ C args)) σ.nv (callM₀ σ C)) = dens F ρ args := by
    rw [callEnv₁, argsOf_setM, argsOf_put' (dens_valTy ρ (callIns_ty hty hgty))]
    simp [callIns, dens, hlen]
  refine ⟨⟨by rw [hfs]; exact hfi, fun c hc => by simp [hcalls] at hc,
    renEnv (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args)) σ.nv (callM₀ σ C),
    hargs.symm, hmod ▸ memOk_call hR hmem, hmod ▸ globOk_call hR hty hgty hpg (EqBelow.refl _ _),
    ?_⟩, hfs⟩
  exact (preF_den_iff _ _ _).mp ((Fm.den_ren _ _ _ _ _ (Fm.scoped_subst_nil _ hsc)).mp hpre)

/-- The environment after the call: the outputs at `n + p`, the callee's final memory at
`n + p + r + 1`. -/
def callEnv₂ (ρ₁ : Env) (n p r : Nat) (res : List Val) (B' : ByteArray) : Env :=
  (ρ₁.put (n + p) res).setM (n + p + r + 1) B'

theorem dens_callEnv₂ {ρ₁ : Env} {n p r : Nat} {ts : List IntType} {res : List Val}
    {B' : ByteArray} (hr : ts.length = r) (hres : res.map valTy = ts.map some) :
    dens F (callEnv₂ ρ₁ n p r res B') (varsFrom (n + p) ts) = res := by
  have hE : EqBelow (n + p + r + 1) (ρ₁.put (n + p) res) (callEnv₂ ρ₁ n p r res B') :=
    eqBelow_setM _ _ _
  refine (List.map_congr_left fun v hv => ?_).trans (dens_put_vars (F := F) (ρ := ρ₁) hres)
  exact (SV.den_eqBelow hE hE v (varsFrom_vlt (by omega) v hv)).symm

/-- The callee's postcondition, as the path condition after the call. -/
theorem post_call {ρ₁ : Env} {n m₀ : Nat} {res : List Val} {B' : ByteArray}
    (hsc : C.post.scoped C.ents = true) (hres : res.map valTy = (C.results ++ C.globals).map some)
    (hpost : C.post.den F (renEnv (callEnv₂ ρ₁ n C.ents.length (callR C) res B') n m₀)
      (valEnv res B')) :
    ((C.post.ren n m₀).subst (varsFrom (n + C.ents.length) (C.results ++ C.globals))
      (n + C.ents.length + callR C + 1)).den F
      (callEnv₂ ρ₁ n C.ents.length (callR C) res B')
      (callEnv₂ ρ₁ n C.ents.length (callR C) res B') := by
  have hd : List.map (SV.den F (callEnv₂ ρ₁ n C.ents.length (callR C) res B')
      (callEnv₂ ρ₁ n C.ents.length (callR C) res B'))
      (varsFrom (n + C.ents.length) (C.results ++ C.globals)) = res :=
    dens_callEnv₂ (by simp) hres
  rw [Fm.den_subst, Fm.den_ren _ _ _ _ _ hsc, locEnv_eq_valEnv, hd]
  simpa [callEnv₂, Env.setM] using hpost

theorem callM₀_lt (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    callM₀ σ C < σ.nv + C.ents.length + callR C + 1 := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  unfold callM₀
  split <;> omega

theorem callOuts_vlt {N : Nat} (h : σ.nv + C.ents.length + callR C ≤ N) :
    ∀ v ∈ callOuts σ C, v.vlt N = true :=
  varsFrom_vlt (by simp; omega)

/-- The locals after the call are below its next fresh variable. -/
theorem locals_vlt_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    ∀ v ∈ (callSt₂ S lt σ C args st).locals, v.vlt (callSt₂ S lt σ C args st).nv = true := by
  have hl : ∀ v ∈ σ.locals, v.vlt σ.nv = true := ((fresh_iff σ).mp hR.fresh).1
  have hN : σ.nv ≤ (callSt₂ S lt σ C args st).nv := by simp only [callSt₂]; omega
  have hres : ∀ v ∈ callOuts σ C, v.vlt (callSt₂ S lt σ C args st).nv = true :=
    callOuts_vlt (by simp only [callSt₂]; omega)
  intro v hv
  simp only [callSt₂, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · exact SV.vlt_mono hN v (hl v (List.mem_of_mem_take hv))
  · exact hres v (List.mem_of_mem_drop hv)
  · exact SV.vlt_mono hN v (hl v (List.mem_of_mem_drop hv))

/-- The stack after the call is below its next fresh variable. -/
theorem stack_vlt_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st) :
    ∀ v ∈ (callSt₂ S lt σ C args st).stack, v.vlt (callSt₂ S lt σ C args st).nv = true := by
  have hall : ∀ v ∈ σ.stack, v.vlt σ.nv = true := ((fresh_iff σ).mp hR.fresh).2.1
  have hN : σ.nv ≤ (callSt₂ S lt σ C args st).nv := by simp only [callSt₂]; omega
  have hres : ∀ v ∈ callOuts σ C, v.vlt (callSt₂ S lt σ C args st).nv = true :=
    callOuts_vlt (by simp only [callSt₂]; omega)
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hres v (List.mem_of_mem_take (List.mem_reverse.mp hv))
  · exact SV.vlt_mono hN v (hall v (by simp [hst, hv]))

/-- The path condition after the call is below its next fresh variable. -/
theorem pc_vlt_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hsc : C.post.scoped C.ents = true) :
    ∀ ψ ∈ (callSt₂ S lt σ C args st).pc, ψ.vlt (callSt₂ S lt σ C args st).nv = true := by
  have hpcb : ∀ φ ∈ σ.pc, φ.vlt σ.nv = true := ((fresh_iff σ).mp hR.fresh).2.2.1
  have hins : ∀ v ∈ callIns S lt σ C args, v.vlt σ.nv = true := callIns_vlt hR hst
  have hlen : (callIns S lt σ C args).length = C.ents.length := callIns_length hty hgty
  have hN : σ.nv ≤ (callSt₂ S lt σ C args st).nv := by simp only [callSt₂]; omega
  have hφ : ((C.post.ren σ.nv (callM₀ σ C)).subst (callOuts σ C)
      (σ.nv + C.ents.length + callR C + 1)).vlt (callSt₂ S lt σ C args st).nv = true :=
    Fm.vlt_ren_subst (by simp only [callSt₂]; omega)
      (by have := callM₀_lt (C := C) hR; simp only [callSt₂]; omega)
      (by simp only [callSt₂]; omega) (callOuts_vlt (by simp only [callSt₂]; omega)) C.post hsc
  refine vlt_ext le_rfl (fun ψ hψ => ?_) hφ
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact argDefs_vlt (by simp only [callSt₂]; omega) hins ψ hψ
  · exact Fm.vlt_mono hN ψ (hpcb ψ hψ)

/-- The state after the call is fresh. -/
theorem fresh_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hsc : C.post.scoped C.ents = true) :
    (callSt₂ S lt σ C args st).fresh = true := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  refine (fresh_iff _).mpr ⟨locals_vlt_call₂ hR, stack_vlt_call₂ hR hst,
    pc_vlt_call₂ hR hst hty hgty hsc, ?_⟩
  simp only [callSt₂]
  split <;> omega

/-- The environment after a call from `σ` in `ρ`, with outputs `res` (results, then final
globals) and final memory `B'`. -/
def callEnv (F : Fns) (S : FnSpec) (lt : List IntType) (ρ : Env) (σ : SSt) (C : FnSpec)
    (args : List SV) (res : List Val) (B' : ByteArray) : Env :=
  callEnv₂ (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args)) σ.nv
    C.ents.length (callR C) res B'

theorem eqBelow_call₁₂ (ρ : Env) (res : List Val) (B' : ByteArray) :
    EqBelow (σ.nv + C.ents.length)
      (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args))
      (callEnv F S lt ρ σ C args res B') :=
  eqBelow_put_setM _ _ _ (by omega)

theorem eqBelow_call (ρ : Env) (res : List Val) (B' : ByteArray) :
    EqBelow σ.nv ρ (callEnv F S lt ρ σ C args res B') :=
  (eqBelow_put_setM ρ _ _ (by omega)).trans ((eqBelow_call₁₂ ρ res B').mono (by omega))

/-- The outputs, read after the call. -/
theorem dens_callOuts {res : List Val} {B' : ByteArray}
    (hres : res.map valTy = (C.results ++ C.globals).map some) :
    dens F (callEnv F S lt ρ σ C args res B') (callOuts σ C) = res :=
  dens_callEnv₂ (by simp) hres

/-- The locals of a related state: the first `nl`, then the globals. -/
theorem locals_len (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    S.nl lt + S.globals.length = σ.locals.length := by
  have hl : σ.locals.length = lt.length := by simpa using congrArg List.length hR.types
  have := hR.glen
  simp only [FnSpec.nl]
  omega

/-- The globals after the call: the callee's final ones, then the caller's others. -/
theorem globs_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hpg : C.globals <+: S.globals)
    {res : List Val} {B' : ByteArray}
    (hres : res.map valTy = (C.results ++ C.globals).map some) :
    globs F S lt (callEnv F S lt ρ σ C args res B') (callSt₂ S lt σ C args st) =
      res.drop C.results.length ++ (globs F S lt ρ σ).drop C.globals.length := by
  have hl := ((fresh_iff σ).mp hR.fresh).1
  have hE := eqBelow_call (F := F) (S := S) (lt := lt) (σ := σ) (C := C) (args := args) ρ res B'
  have hlen := locals_len hR
  have hk := hpg.length_le
  have hd := dens_callOuts (F := F) (S := S) (lt := lt) (σ := σ) (ρ := ρ) (args := args) (B' := B') hres
  have hdrop : (callSt₂ S lt σ C args st).locals.drop (S.nl lt) =
      (callOuts σ C).drop C.results.length ++ σ.locals.drop (S.nl lt + C.globals.length) := by
    simp only [callSt₂, List.append_assoc]
    rw [List.drop_append_of_le_length (by simp only [List.length_take]; omega),
      List.drop_of_length_le (by simp only [List.length_take]; omega), List.nil_append]
  simp only [globs, hdrop, dens, List.map_append, List.map_drop, List.drop_drop]
  rw [show List.map (SV.den F (callEnv F S lt ρ σ C args res B') (callEnv F S lt ρ σ C args res B'))
      (callOuts σ C) = res from hd]
  congr 1
  rw [← List.map_drop, ← List.map_drop]
  exact List.map_congr_left fun w hw =>
    (SV.den_eqBelow hE hE w (hl w (List.mem_of_mem_drop hw))).symm

/-- The store after the call is the one related to the state after the call. -/
theorem store_call {res : List Val} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hmem : C.mem = true → S.mem = true) (hpg : C.globals <+: S.globals)
    (hres : res.map valTy = (C.results ++ C.globals).map some) :
    setGs (upd C s m B') m (res.drop C.results.length) =
      setGs (upd S s₀ m ((callEnv F S lt ρ σ C args res B').mem (callSt₂ S lt σ C args st).mem))
        m (globs F S lt (callEnv F S lt ρ σ C args res B') (callSt₂ S lt σ C args st)) := by
  have hm : σ.mem < σ.nv := ((fresh_iff σ).mp hR.fresh).2.2.2
  have hlenG : (res.drop C.results.length).length ≤ (globs F S lt ρ σ).length := by
    have h₁ : res.length = C.results.length + C.globals.length := by
      simpa using congrArg List.length hres
    rw [length_globs hR, List.length_drop, h₁]
    have := hpg.length_le
    omega
  have hGk : (res.drop C.results.length).length = C.globals.length := by
    have h₁ : res.length = C.results.length + C.globals.length := by
      simpa using congrArg List.length hres
    simp [h₁]
  rw [globs_call hR hpg hres]
  have hupd : upd C s m B' = setGs (upd S s₀ m ((callEnv F S lt ρ σ C args res B').mem
      (callSt₂ S lt σ C args st).mem)) m (globs F S lt ρ σ) := by
    by_cases hc : C.mem = true
    · rw [upd_call hR (hmem hc) hc]
      simp [callSt₂, hc, callEnv, callEnv₂, Env.setM]
    · have hE := eqBelow_call (F := F) (S := S) (lt := lt) (σ := σ) (C := C) (args := args) ρ res B'
      simp only [callSt₂, hc, Bool.false_eq_true, ↓reduceIte, ← (hE σ.mem hm).2.2]
      simpa [upd, hc] using hR.store
  rw [hupd, setGs_setGs hlenG, hGk]

/-- The declared locals after the call are the ones before it. -/
theorem take_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) :
    (callSt₂ S lt σ C args st).locals.take (S.nl lt) = σ.locals.take (S.nl lt) := by
  have hlen : S.nl lt + S.globals.length = σ.locals.length := locals_len hR
  simp only [callSt₂, List.append_assoc]
  rw [List.take_append_of_le_length (by simp; omega)]
  simp

/-- The types of the locals after the call. -/
theorem types_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals) :
    (callSt₂ S lt σ C args st).locals.map SV.ty = lt := by
  have hout : ((callOuts σ C).drop C.results.length).map SV.ty = C.globals := by
    rw [callOuts, List.map_drop, varsFrom_ty, List.drop_left]
  have hsplit : σ.locals = σ.locals.take (S.nl lt) ++
      (σ.locals.drop (S.nl lt)).take C.globals.length ++
      σ.locals.drop (S.nl lt + C.globals.length) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have h₁ : (callSt₂ S lt σ C args st).locals.map SV.ty = σ.locals.map SV.ty := by
    conv_rhs => rw [hsplit]
    simp only [callSt₂, List.map_append, hout, hgty]
  exact h₁.trans hR.types

/-- The path condition before the call is below the bound values. -/
theorem old_vlt_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals) :
    ∀ φ ∈ argDefs σ.nv (callIns S lt σ C args) ++ σ.pc,
      φ.vlt (σ.nv + C.ents.length) = true := by
  have hpcb : ∀ φ ∈ σ.pc, φ.vlt σ.nv = true := ((fresh_iff σ).mp hR.fresh).2.2.1
  have hins : ∀ v ∈ callIns S lt σ C args, v.vlt σ.nv = true := callIns_vlt hR hst
  have hilen : (callIns S lt σ C args).length = C.ents.length := callIns_length hty hgty
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact argDefs_vlt (by omega) hins φ hφ
  · exact Fm.vlt_mono (by omega) φ (hpcb φ hφ)

/-- The declared locals after the call denote the frame's locals. -/
theorem locals_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) {res : List Val} {B' : ByteArray} :
    f.locals = locs F (callEnv F S lt ρ σ C args res B')
      ((callSt₂ S lt σ C args st).locals.take (S.nl lt)) := by
  have hl : ∀ v ∈ σ.locals, v.vlt σ.nv = true := ((fresh_iff σ).mp hR.fresh).1
  have hE : EqBelow σ.nv ρ (callEnv F S lt ρ σ C args res B') := eqBelow_call ρ res B'
  rw [hR.locals, take_call₂ hR]
  exact List.map_congr_left fun w hw =>
    congrArg some (SV.den_eqBelow hE hE w (hl w (List.mem_of_mem_take hw)))

/-- **The configuration after the call** is related to the state after the call. -/
theorem rel_call₂ {res : List Val} {B' : ByteArray} (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hst : σ.stack = args.reverse ++ st) (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hpg : C.globals <+: S.globals)
    (hmem : C.mem = true → S.mem = true) (hsc : C.post.scoped C.ents = true)
    (hres : res.map valTy = (C.results ++ C.globals).map some)
    (hpost : C.post.den F (renEnv (callEnv F S lt ρ σ C args res B') σ.nv (callM₀ σ C))
      (valEnv res B')) :
    Rel F S lt ρ₀ s₀ m (callEnv F S lt ρ σ C args res B') (callSt₂ S lt σ C args st)
      (setGs (upd C s m B') m (res.drop C.results.length)) f
      (dens F (callEnv F S lt ρ σ C args res B') (callSt₂ S lt σ C args st).stack) := by
  have hE : EqBelow σ.nv ρ (callEnv F S lt ρ σ C args res B') := eqBelow_call ρ res B'
  have hE₁₂ : EqBelow (σ.nv + C.ents.length)
      (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args))
      (callEnv F S lt ρ σ C args res B') := eqBelow_call₁₂ ρ res B'
  have hpc₁ : ∀ φ ∈ argDefs σ.nv (callIns S lt σ C args) ++ σ.pc,
      φ.den F (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args))
        (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args)) :=
    pc_call₁ hR (callIns_vlt hR hst)
  exact { store := store_call hR hmem hpg hres
          memOk := by rw [← (hE 0 (by have := hR.pnv; omega)).2.2]; exact hR.memOk
          globOk := hR.globOk, glen := hR.glen
          modl := hR.modl
          locals := locals_call₂ hR
          stack := rfl
          types := types_call₂ hR hgty
          agree := (agree_of_eqBelow hE hR.pnv).symm.trans hR.agree
          pc := pc_ext hE₁₂ hpc₁ (old_vlt_call hR hst hty hgty) (post_call hsc hres hpost)
          fresh := fresh_call₂ hR hst hty hgty hsc
          pnv := by simp only [callSt₂]; have := hR.pnv; omega
          pre := hR.pre }

/-- The arguments, read in the callee's environment after the call. -/
theorem argsOf_call (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (ρ : Env) (res : List Val) (B' : ByteArray) :
    argsOf C (renEnv (callEnv F S lt ρ σ C args res B') σ.nv (callM₀ σ C)) = dens F ρ args := by
  have hlen : args.length = C.params.length := by simpa using congrArg List.length hty
  rw [← argsOf_eqBelow (m := callM₀ σ C) ((eqBelow_call₁₂ ρ res B').mono
      (by simp [FnSpec.ents])), callEnv₁, argsOf_setM,
    argsOf_put' (dens_valTy ρ (callIns_ty hty hgty))]
  simp [callIns, dens, hlen]

/-- The callee's memory at entry, read after the call. -/
theorem memOk_call₂ (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hmem : C.mem = true → S.mem = true)
    (res : List Val) (B' : ByteArray) :
    MemOk C s m ((renEnv (callEnv F S lt ρ σ C args res B') σ.nv (callM₀ σ C)).mem 0) := by
  have hlt := callM₀_lt (C := C) hR
  have h : (callEnv F S lt ρ σ C args res B').mem (callM₀ σ C) =
      (callEnv₁ F ρ σ.nv C.ents.length (callR C) (callIns S lt σ C args)).mem (callM₀ σ C) := by
    simp [callEnv, callEnv₂, Env.setM, Env.put, show callM₀ σ C ≠
      σ.nv + C.ents.length + callR C + 1 by omega]
  simp only [renEnv, h]
  exact memOk_call hR hmem

/-- The stack after the call. -/
theorem stack_call (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    {res : List Val} {B' : ByteArray} (hres : res.map valTy = (C.results ++ C.globals).map some) :
    (dens F (callEnv F S lt ρ σ C args res B') (callSt₂ S lt σ C args st).stack).reverse =
      (dens F ρ st).reverse ++ res.take C.results.length := by
  have hE := eqBelow_call (F := F) (S := S) (lt := lt) (σ := σ) (C := C) (args := args) ρ res B'
  have hst' : dens F (callEnv F S lt ρ σ C args res B') st = dens F ρ st :=
    List.map_congr_left fun v hv =>
      (SV.den_eqBelow hE hE v (((fresh_iff σ).mp hR.fresh).2.1 v (by simp [hst, hv]))).symm
  have hd := dens_callOuts (F := F) (S := S) (lt := lt) (σ := σ) (ρ := ρ) (args := args) (B' := B') hres
  have hd' : dens F (callEnv F S lt ρ σ C args res B') ((callOuts σ C).take C.results.length) =
      res.take C.results.length := by
    simp only [dens, List.map_take] at hd ⊢
    rw [hd]
  simp only [callSt₂, dens, List.map_append, List.map_reverse, List.reverse_append,
    List.reverse_reverse] at hst' hd' ⊢
  rw [hst', hd']

/-- The callee's postcondition, read after the call, relates the configuration after it. -/
theorem rel_after {fi' : FuncInst H} {s' : Store H} {res G : List Val} {B' : ByteArray}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hpg : C.globals <+: S.globals) (hmem : C.mem = true → S.mem = true)
    (hqsc : C.post.scoped C.ents = true) (hmod : fi'.module = m)
    (hs' : s' = setGs (upd C s fi'.module B') fi'.module G)
    (hout : (res ++ G).map valTy = (C.results ++ C.globals).map some)
    (hlen : res.length = C.results.length)
    (hp : ∀ ρ', dens F ρ args = argsOf C ρ' → MemOk C s fi'.module (ρ'.mem 0) →
      GlobOk C s fi'.module ρ' → C.post.den F ρ' (valEnv (res ++ G) B')) :
    Rel F S lt ρ₀ s₀ m (callEnv F S lt ρ σ C args (res ++ G) B') (callSt₂ S lt σ C args st) s' f
      (dens F (callEnv F S lt ρ σ C args (res ++ G) B') (callSt₂ S lt σ C args st).stack) := by
  have hgl : (res ++ G).drop C.results.length = G := by simp [← hlen]
  have hgo : GlobOk C s fi'.module
      (renEnv (callEnv F S lt ρ σ C args (res ++ G) B') σ.nv (callM₀ σ C)) :=
    hmod ▸ globOk_call hR hty hgty hpg (eqBelow_call₁₂ ρ (res ++ G) B')
  have hmo : MemOk C s fi'.module
      ((renEnv (callEnv F S lt ρ σ C args (res ++ G) B') σ.nv (callM₀ σ C)).mem 0) :=
    hmod ▸ memOk_call₂ hR hmem (res ++ G) B'
  have hpd := hp _ (argsOf_call hty hgty ρ (res ++ G) B').symm hmo hgo
  have hrel := rel_call₂ (st := st) hR hst hty hgty hpg hmem hqsc hout (by simpa using hpd)
  rw [hgl] at hrel
  rw [hs', hmod]
  exact hrel

/-- The callee's normal outcomes, seen after the call: the continuation from the state after
the call. -/
theorem seqPost_call {a' : Nat} {fi' : FuncInst H} {rest : List Admin} {Q : Post H}
    (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs) (hst : σ.stack = args.reverse ++ st)
    (hty : args.map SV.ty = C.params)
    (hgty : ((σ.locals.drop (S.nl lt)).take C.globals.length).map SV.ty = C.globals)
    (hpg : C.globals <+: S.globals) (hmem : C.mem = true → S.mem = true)
    (hqsc : C.post.scoped C.ents = true) (hmod : fi'.module = m)
    (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv (callSt₂ S lt σ C args st) rest Q) :
    ∀ s' o, callPost f (dens F ρ st).reverse ((fspecIn F C a' fi' s₀).post s (dens F ρ args)) s' f o →
      ∃ res, o = .normal ((dens F ρ st).reverse ++ res) ∧
        Wp c P host s' f (vals ((dens F ρ st).reverse ++ res) ++ rest) Q := by
  rintro s' o ⟨-, ⟨res, rfl, B', G, hs', hG, res', hres', hlen, htys, hp⟩ |
    ⟨rfl, B', -, -, -, res', h', -⟩ | ⟨a, rfl, B', -, -, -, res', h', -⟩⟩
  · obtain rfl : res = res' := Outcome.normal.inj hres'
    have hout : (res ++ G).map valTy = (C.results ++ C.globals).map some := by
      simp only [List.map_append, htys, hG]
    have hrl : (res ++ G).take C.results.length = res := by simp [← hlen]
    have hk' : Wp c P host s' f (vals (dens F (callEnv F S lt ρ σ C args (res ++ G) B')
        (callSt₂ S lt σ C args st).stack).reverse ++ rest) Q :=
      hk _ s' f (rel_after hR hst hty hgty hpg hmem hqsc hmod hs' hout hlen hp)
        (eqBelow_call ρ (res ++ G) B')
    rw [stack_call hR hst hout, hrl] at hk'
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
    (h : callStep S lt x.toNat σ = some (σ₁, pre, σ₂)) (hR : Rel F S lt ρ₀ s₀ m ρ σ s f rs)
    (hpre : Valid F (vc σ₁ pre)) (hk : Cont c F S lt ρ₀ s₀ m P host ρ σ.nv σ₂ rest Q) :
    Wp c P host s f (vals rs.reverse ++ .plain (.call x) :: rest) Q := by
  obtain ⟨C, code, args, st, hmemC, hmem, hcalls, hpg, hst, hty, hgty, rfl, rfl, rfl⟩ :=
    callStep_inv h
  obtain ⟨a', fi', hx, hfi, hmod, hval⟩ := hC _ hmemC
  have hsc : C.pre.scoped C.ents = true ∧ C.post.scoped C.ents = true :=
    wellScoped_calls hS _ hmemC
  have hpreC : (fspecIn F C a' fi' s₀).pre s (dens F ρ args) :=
    pre_call hR hty hgty hpg hfi hmod hcalls hmem hsc.1
      (vc_holds hpre (pc_call₁ hR (callIns_vlt hR hst)))
  have hrs : rs.reverse = (dens F ρ st).reverse ++ dens F ρ args := by
    rw [hR.stack, hst]
    simp [dens, List.map_reverse]
  have hx' : f.module.funcs[x.toNat]? = some a' := by rw [hR.modl]; exact hx
  have hf : s.funcs[a']? = some fi' := by rw [hR.store, setGs_funcs, funcs_upd]; exact hfi
  rw [hrs]
  exact callIdx_wp hx' hf hval hpreC (seqPost_call (a' := a') (fi' := fi') hR hst hty hgty hpg hmem
    hsc.2 hmod hk)

end Main

end Call

end Silmaril.Wasm.Auto2.VCGen
