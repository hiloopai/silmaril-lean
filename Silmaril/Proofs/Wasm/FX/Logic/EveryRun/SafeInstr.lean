module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Partial

/-!
# The step-indexed instruction rules of the every-run WasmFX logic

The rules for one instruction at the end of the code, for the step-indexed predicate `Safe`
(`Silmaril.Wasm.FX.Logic.EveryRun.Defs`, partial correctness), as the total rules of
`Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Total`: an instruction that takes one step is safe for
`n + 1` steps when every successor is safe for `n` steps.

* `safe_last`: the general rule, through the root steps (`Root`) of `fvals V ++ [a]`;
* stack switching: **`safe_contNew`**, **`safe_contBind`** (and the total rule
  `tsafe_contBind`, new), **`safe_resume`**, **`safe_resumeThrow`**, `safe_dropCont`; the
  stopping instructions **`safe_suspend`**, **`safe_switch`**, `safe_switch_nil` follow from
  the total ones (they do not step);
* Core and control: `safe_inert`, `safe_block`, `safe_invoke`;
* `hwp_*`: the same rules for the every-run weakest precondition `HWP`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont bindCont)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled suspCode switchCode Stops Safe TSafe HWP Inv seqPost
  totJ)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H} {s : Store H}
  {K : Conts} {f : Frame}

/-! ## The general rule -/

/-- **One instruction that cannot stop**: safe for `n + 1` steps if every root step leads to
code safe for `n` steps. -/
theorem safe_last {n : Nat} {V : List FVal} {a : AdminFX} (hn : NotStop a)
    (h : ∀ V₁ V₂ y', V = V₁ ++ V₂ → Root P fx s K f V₂ a y' →
      Safe P fx Q n ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals V ++ [a]⟩ := by
  refine ⟨stops_notStop hn, fun y hy => ?_⟩
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  exact h V₁ V₂ y' hV hroot

/-- The same for total safety. -/
theorem tsafe_last {V : List FVal} {a : AdminFX} (hn : NotStop a)
    (h : ∀ V₁ V₂ y', V = V₁ ++ V₂ → Root P fx s K f V₂ a y' →
      TSafe P fx Q ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ [a]⟩ := by
  refine .intro (stops_notStop hn) fun y hy => ?_
  obtain ⟨V₁, V₂, y', hV, hroot, rfl⟩ := lastRes_y hy hn.1
  exact h V₁ V₂ y' hV hroot

/-- **One instruction that cannot stop, then code**: safe for `n + 1` steps if every root step
of the instruction leads, followed by the code, to code safe for `n` steps. No `Inv` is needed:
the instruction takes exactly one step. -/
theorem safe_last_seq {n : Nat} {V : List FVal} {a : AdminFX} {rest : List AdminFX}
    (hn : NotStop a)
    (h : ∀ V₁ V₂ y', V = V₁ ++ V₂ → Root P fx s K f V₂ a y' →
      Safe P fx Q n ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code ++ rest⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals V ++ a :: rest⟩ := by
  refine ⟨stops_notStop hn, fun y hy => ?_⟩
  have hy' : StepFX' P noHost fx ⟨s, K, f, fvals V ++ a :: [] ++ rest⟩ y := by simpa using hy
  rcases step_split_app hn.1 hy' with ⟨c₁', hst, hcode⟩ | ⟨ha, -⟩ | ⟨ha, -⟩
  · obtain ⟨V₁, V₂, y', hV, hroot, hy1⟩ := lastRes_y hst hn.1
    obtain ⟨h1, h2, h3, h4⟩ := ConfigFX.mk.inj hy1
    obtain ⟨ys, yK, yf, yc⟩ := y
    simp only at h1 h2 h3 h4 hcode
    subst h1 h2 h3 hcode h4
    exact h V₁ V₂ y' hV hroot
  · exact absurd ha hn.2.2.2.2.1
  · exact absurd ha hn.2.2.2.2.2.1

/-- The same for total safety. -/
theorem tsafe_last_seq {V : List FVal} {a : AdminFX} {rest : List AdminFX} (hn : NotStop a)
    (h : ∀ V₁ V₂ y', V = V₁ ++ V₂ → Root P fx s K f V₂ a y' →
      TSafe P fx Q ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ a :: rest⟩ := by
  refine .intro (stops_notStop hn) fun y hy => ?_
  have hy' : StepFX' P noHost fx ⟨s, K, f, fvals V ++ a :: [] ++ rest⟩ y := by simpa using hy
  rcases step_split_app hn.1 hy' with ⟨c₁', hst, hcode⟩ | ⟨ha, -⟩ | ⟨ha, -⟩
  · obtain ⟨V₁, V₂, y', hV, hroot, hy1⟩ := lastRes_y hst hn.1
    obtain ⟨h1, h2, h3, h4⟩ := ConfigFX.mk.inj hy1
    obtain ⟨ys, yK, yf, yc⟩ := y
    simp only at h1 h2 h3 h4 hcode
    subst h1 h2 h3 hcode h4
    exact h V₁ V₂ y' hV hroot
  · exact absurd ha hn.2.2.2.2.1
  · exact absurd ha hn.2.2.2.2.2.1

/-! ## Stack switching -/

/-- **`cont.new`** (step-indexed). -/
theorem safe_contNew {n : Nat} {V : List FVal} {a : Nat} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi)
    (h : Safe P fx Q n ⟨s, K ++ [some (newCont a fi)], f, fvals V ++ [.contRef K.length]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ [.fx (.contNew ct)]⟩ := by
  refine safe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | @contNew a' fi' _ hf' =>
    obtain ⟨rfl, ha⟩ := List.append_inj' hV rfl
    obtain rfl : a' = a := by simpa using ha.symm
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    simpa [newCont] using h
  | contNewNull => exact absurd (List.append_inj' hV rfl).2 (by simp)

/-- **`cont.bind`** (total correctness), for every split of the values below the
continuation into the bound values and the values that stay. -/
theorem tsafe_contBind {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      TSafe P fx Q ⟨s, K.set k none ++ [some
          (bindCont C vs)], f, fvals V₁ ++ [.contRef K.length]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.contBind ct ct')]⟩ := by
  refine tsafe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | @contBind vs k' C' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    simpa [bindCont] using h V₁ vs hV₁
  | @contBindNull vs _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)
  | @contBindUsed vs k' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain rfl : k' = k := by simpa using (List.append_inj' hV' rfl).2.symm
    simp [hk] at hk'

/-- **`cont.bind`**, then code (total correctness), for every split. -/
theorem tsafe_contBind_seq (hQ : Inv Q) {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    {rest : List AdminFX} (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs → TSafe P fx Q ⟨s, K.set k none ++ [some (bindCont C vs)], f,
      fvals (V₁ ++ [.cont K.length]) ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ .fx (.contBind ct ct') :: rest⟩ :=
  tsafe_cons hQ (tsafe_contBind hk fun V₁ vs hV => by
    have e : fvals V₁ ++ [AdminFX.contRef K.length] = fvals (V₁ ++ [.cont K.length]) := by
      simp [FVal.toAdmin]
    rw [e]
    exact tsafe_vals_seq (h V₁ vs hV))

/-- **`local.get`**, then code (total correctness). -/
theorem tsafe_localGet (hQ : Inv Q) {V : List FVal} {x : LocalIdx} {v : Val}
    {rest : List AdminFX} (hv : f.local? x = some (some v))
    (h : TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val v]) ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain (.localGet x)) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_inert ⟨rfl, by simp, rfl⟩ (by simp) (by simp) (by simp) ?_)
  intro V₁ args c₀ hV hh
  obtain ⟨rfl, v', hv', rfl⟩ := Silmaril.Wasm.Logic.Hoare.head_localGet hh
  obtain rfl : v' = v := by simpa [hv] using hv'.symm
  have hV' : V = V₁ := by simpa [liftV] using hV
  have e : fvals V₁ ++ [v'.toAdmin].map AdminFX.core = fvals (V ++ [.val v']) := by
    rw [hV']; simp [fvals, FVal.toAdmin]
  show TSafe P fx _ ⟨s, K, f, fvals V₁ ++ [v'.toAdmin].map AdminFX.core⟩
  rw [e]
  exact tsafe_vals_seq h

/-- **`cont.bind`** (step-indexed), for every split. -/
theorem safe_contBind {n : Nat} {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      Safe P fx Q n ⟨s, K.set k none ++ [some
          (bindCont C vs)], f, fvals V₁ ++ [.contRef K.length]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.contBind ct ct')]⟩ := by
  refine safe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | @contBind vs k' C' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    simpa [bindCont] using h V₁ vs hV₁
  | @contBindNull vs _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)
  | @contBindUsed vs k' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain rfl : k' = k := by simpa using (List.append_inj' hV' rfl).2.symm
    simp [hk] at hk'

/-- **`resume`** (step-indexed), for every payload split. -/
theorem safe_resume {n : Nat} {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {hos : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      Safe P fx Q n ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ := by
  refine safe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | @resume vs k' C' _ _ hs'' hk' hr' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    obtain rfl : hs'' = hs' := by simpa [hr] using hr'.symm
    simpa using h V₁ vs hV₁
  | @resumeNull vs _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)
  | @resumeUsed vs k' _ _ hk' =>
    have hV' : V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] := by rw [hV]; simp
    obtain rfl : k' = k := by simpa using (List.append_inj' hV' rfl).2.symm
    simp [hk] at hk'

/-- **`resume_throw`** (step-indexed), for every split of the values into exception fields. -/
theorem safe_resumeThrow {n : Nat} {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {hos : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs →
      Safe P fx Q n ⟨s.addExn ⟨ta, vs⟩, K.set k none, f,
        fvals V₁ ++ [.handler hs' (C.plug (cthrowing s.exns.length))]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resumeThrow ct x hos)]⟩ := by
  refine safe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | @resumeThrow vs k' C' _ _ _ hs'' ta' ti' hk' ht' hr' =>
    have hV' : V ++ [.cont k] = (V₁ ++ liftV vs) ++ [.cont k'] := by rw [hV]; simp
    obtain ⟨hV₁, hkk⟩ := List.append_inj' hV' rfl
    obtain rfl : k' = k := by simpa using hkk.symm
    obtain rfl : C' = C := by simpa [hk] using hk'.symm
    obtain rfl : hs'' = hs' := by simpa [hr] using hr'.symm
    obtain ⟨rfl, rfl⟩ : ta' = ta ∧ ti' = ti := by simpa [ht] using ht'.symm
    simpa using h V₁ vs hV₁
  | @resumeThrowNull vs _ _ _ =>
    have hV' : V ++ [.cont k] = (V₁ ++ liftV vs) ++ [.val (.ref .null)] := by rw [hV]; simp
    exact absurd (List.append_inj' hV' rfl).2 (by simp)

/-- **Dropping a continuation** (step-indexed). -/
theorem safe_dropCont {n : Nat} {V : List FVal} {k : Nat} (h : Safe P fx Q n ⟨s, K, f, fvals V⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.core (.plain .drop)]⟩ := by
  refine safe_last (notStop_core_plain rfl (by simp) (by simp) (by simp))
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | core h' => exact (drop_core_root hV h').elim
  | dropCont =>
    obtain ⟨rfl, -⟩ := List.append_inj' hV rfl
    simpa using h
  | invoke hc => simp [Admin.IsCallRef] at hc

/-- **An unhandled `suspend`** stops (every number of steps). -/
theorem safe_suspend {n : Nat} {V : List FVal} {x : TagIdx}
    (h : ∀ E vs, E.plug (suspCode vs x) = fvals V ++ [.fx (.suspend x)] → Unhandled s f E x →
      Q s K f (.susp E vs x)) :
    Safe P fx Q n ⟨s, K, f, fvals V ++ [.fx (.suspend x)]⟩ :=
  tsafe_hwp (tsafe_suspend h) n

/-- **An unhandled `switch`** stops (every number of steps). -/
theorem safe_switch {n : Nat} {V : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (h : ∀ E vs, E.plug (switchCode vs k ct x) = fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)] →
      Unhandled s f E x → Q s K f (.swtch E vs k ct x)) :
    Safe P fx Q n ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)]⟩ :=
  tsafe_hwp (tsafe_switch h) n

/-- A `switch` without a continuation below it neither steps nor stops. -/
theorem safe_switch_nil {n : Nat} {ct : TypeIdx} {x : TagIdx} :
    Safe P fx Q n ⟨s, K, f, fvals [] ++ [.fx (.switch ct x)]⟩ :=
  tsafe_hwp tsafe_switch_nil n

/-! ## Core instructions, blocks and calls -/

/-- **A plain instruction without a host call** (step-indexed). -/
theorem safe_inert {n : Nat} {V : List FVal} {i : Instr} (hi : Silmaril.Wasm.Logic.Hoare.Inert i)
    (hd : i ≠ .drop) (hb : ∀ l, i ≠ .br l) (hr : i ≠ .return_)
    (h : ∀ V₁ args c₀, V = V₁ ++ liftV args →
      Silmaril.Wasm.SingleThreaded.Det.Head P s f args (.plain i) c₀ →
      Safe P fx Q n ⟨c₀.store, K, c₀.frame, fvals V₁ ++ c₀.code.map .core⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals V ++ [.core (.plain i)]⟩ := by
  refine safe_last (notStop_core_plain hi.1 hi.2.1 hb hr) fun V₁ V₂ y' hV hroot => ?_
  subst hV
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := inert_root hi hd hroot
  simpa using h (V₁ ++ liftV vs) args c₀ (by simp [liftV]) hh

/-- **`block`** (step-indexed). -/
theorem safe_block {n : Nat} {V : List FVal} {bt : BlockType} {body : List InstrFX}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (h : ∀ V₁ vs, V = V₁ ++ vs → vs.length = t₁.length →
      Safe P fx Q n ⟨s, K, f, fvals V₁ ++
        [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals V ++ [.block bt body]⟩ := by
  refine safe_last ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩
    fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | block hbt' hm =>
    rw [hbt] at hbt'
    obtain ⟨rfl, rfl⟩ : t₁ = _ ∧ t₂ = _ := by simpa using hbt'
    exact h V₁ V₂ hV hm

/-- **A call of an FX function** (`invoke`, step-indexed). -/
theorem safe_invoke {n : Nat} {V : List FVal} {a : Nat} {fi : FuncInst H} {hh : H} {F : FuncFX}
    {c : Admin} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fx hh = some F)
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs → vs.length = F.nparams →
      Safe P fx Q n ⟨s, K, f, fvals V₁ ++ [.frame F.nresults (Frame.forCall F.module vs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ [.core c]⟩ := by
  refine safe_last (notStop_callRef hc) fun V₁ V₂ y' hV hroot => ?_
  cases hroot with
  | core h' => exact (invoke_core_root hc hf hcode hV h').elim
  | dropCont => simp [Admin.IsCallRef] at hc
  | trapSeq => simp [Admin.IsCallRef] at hc
  | throwSeq => simp [Admin.IsCallRef] at hc
  | @invoke _ vs a' fi' hh' F' _ hf' hcode' hfx' hn' =>
    have hV' : V ++ [.val (.ref (.func a))] = (V₁ ++ liftV vs) ++ [.val (.ref (.func a'))] := by
      rw [hV]; simp
    obtain ⟨hV₁, ha⟩ := List.append_inj' hV' rfl
    obtain rfl : a' = a := by simpa using ha.symm
    obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : hh' = hh := by rw [hcode] at hcode'; simpa using hcode'.symm
    obtain rfl : F' = F := Option.some.inj (hfx'.symm.trans hfx)
    simpa using h V₁ vs hV₁ hn'

/-! ## The same rules for `HWP` -/

/-- Lift a one-step rule to `HWP`. -/
theorem hwp_of_step {c c' : ConfigFX H} (hstep : ∀ n, Safe P fx Q n c' → Safe P fx Q (n + 1) c)
    (h : ∀ n, Safe P fx Q n c') : ∀ n, Safe P fx Q n c
  | 0 => trivial
  | n + 1 => hstep n (h n)

theorem hwp_contNew {V : List FVal} {a : Nat} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi)
    (h : HWP P fx s (K ++ [some (newCont a fi)]) f (fvals V ++ [.contRef K.length]) Q) :
    HWP P fx s K f (fvals (V ++ [.val (.ref (.func a))]) ++ [.fx (.contNew ct)]) Q :=
  hwp_of_step (fun _ hn => safe_contNew hf hn) h

theorem hwp_contBind {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      HWP P fx s (K.set k none ++ [some (bindCont C vs)]) f (fvals V₁ ++ [.contRef K.length]) Q) :
    HWP P fx s K f (fvals (V ++ [.cont k]) ++ [.fx (.contBind ct ct')]) Q
  | 0 => trivial
  | n + 1 => safe_contBind hk fun V₁ vs hV => h V₁ vs hV n

theorem hwp_resume {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {hos : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      HWP P fx s (K.set k none) f (fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]) Q) :
    HWP P fx s K f (fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]) Q
  | 0 => trivial
  | n + 1 => safe_resume hk hr fun V₁ vs hV => h V₁ vs hV n

theorem hwp_resumeThrow {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {hos : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs →
      HWP P fx (s.addExn ⟨ta, vs⟩) (K.set k none) f
        (fvals V₁ ++ [.handler hs' (C.plug (cthrowing s.exns.length))]) Q) :
    HWP P fx s K f (fvals (V ++ [.cont k]) ++ [.fx (.resumeThrow ct x hos)]) Q
  | 0 => trivial
  | n + 1 => safe_resumeThrow hk ht hr fun V₁ vs hV => h V₁ vs hV n

theorem hwp_invoke {V : List FVal} {a : Nat} {fi : FuncInst H} {hh : H} {F : FuncFX}
    {c : Admin} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fx hh = some F)
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs → vs.length = F.nparams →
      HWP P fx s K f (fvals V₁ ++ [.frame F.nresults (Frame.forCall F.module vs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]) Q) :
    HWP P fx s K f (fvals (V ++ [.val (.ref (.func a))]) ++ [.core c]) Q
  | 0 => trivial
  | n + 1 => safe_invoke hc hf hcode hfx fun V₁ vs hV hn => h V₁ vs hV hn n

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
