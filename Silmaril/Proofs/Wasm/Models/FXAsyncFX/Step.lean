module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.SimSus

/-!
# The simulation step: every kernel step in the fragment is matched

`Matched S W c r`: a kernel step result `r` is matched from the `StepFX'` configuration `c`: a
next configuration by a positive `StepFX'` run to a related configuration, a stop by the
`StepFX'` result of the same behaviour (and not a trap). **`sim_step`**: from related
configurations, a kernel step in the fragment (`fine`) is matched. The proof dispatches on the
encoded instruction (`EncI`) to the cases of `SimTop`, `SimCall`, `SimRet`, `SimRes` and
`SimSus`, after computing the kernel step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- A kernel step result is matched from `c`. -/
def Matched (S : Setup H) (W : Prog (Ins Val)) (c : ConfigFX H) : Res (SCfg Val) Val → Prop
  | .next x' => SimGoal S W c x'
  | .stop o => o ≠ .trap ∧ ∃ r : Result, c.code = r.toAdmin.map .core ∧
      r.toBehaviour = obsB o.toObs

theorem sstep_exec {P : Prog (Ins Val)} {test : Val → Bool} {K : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {rest : List (SFrame Val)} {i : Ins Val} {c : List (Ins Val)}
    (hc : fr.code = i :: c) : sstep P test ⟨K, fr :: rest⟩ = sexec P test K fr i c rest := by
  simp only [sstep, hc]

/-- The data of a related configuration with its top frame. -/
structure Top (S : Setup H) (W : Prog (Ins Val)) (KK : List (Option (List (SFrame Val))))
    (K : List (Option ContFX)) (fr : SFrame Val) (a : Ann) (rs : List (SFrame Val × Ann)) :
    Prop where
  main : MainOk S W ((fr, a) :: rs)
  conts : List.Forall₂ (KRel S W) KK K
  noTrap : sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩ ≠ .stop .trap
  top : fineTop W fr (rs.map Prod.fst) = true

/-- The configuration of a top frame. -/
abbrev cfgOf (S : Setup H) (K : List (Option ContFX)) (fr : SFrame Val) (a : Ann)
    (rs : List (SFrame Val × Ann)) : ConfigFX H :=
  ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩

variable {KK : List (Option (List (SFrame Val)))} {K : List (Option ContFX)} {fr : SFrame Val}
  {a : Ann} {rs : List (SFrame Val × Ann)}

theorem matched_prim (hok : Ok S W) (hT : Top S W KK K fr a rs) {n : Nat}
    {op : List Val → List Val} {i : Instr} {c : List (Ins Val)} {Y : List InstrFX}
    (hc : fr.code = .prim n op :: c) (hY : a.code = .core i :: Y) (hi : PrimOk S n op i)
    (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hall : (fr.ops.take n).all isI32 = true := by simpa only [fineTop, hc] using hT.top
  have hnt : sexec W i32Test KK fr (.prim n op) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  cases hp : popN n fr.ops with
  | none => exact absurd (by simp only [sexec, hp]) hnt
  | some ao =>
    obtain ⟨args, o⟩ := ao
    obtain ⟨hops, hlen⟩ := popN_eq hp
    have htake : fr.ops.take n = args := by rw [hops, ← hlen, List.take_left]
    obtain ⟨bs, rfl⟩ := i32s_of_all (htake ▸ hall)
    have hbs : bs.length = n := by simpa only [List.length_map] using hlen
    have hstep : sexec W i32Test KK fr (.prim n op) c (rs.map Prod.fst) =
        .next ⟨KK, { fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o } ::
          rs.map Prod.fst⟩ := by
      simp only [sexec, hp, allVals_map]
    rw [hstep]
    exact sim_prim S hok hT.main hT.conts hops hbs hY hi henc

theorem matched_drop (hT : Top S W KK K fr a rs) {c : List (Ins Val)} {Y : List InstrFX}
    (hc : fr.code = .drop :: c) (hY : a.code = .core .drop :: Y) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr .drop c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  cases ho : fr.ops with
  | nil => exact absurd (by simp only [sexec, ho]) hnt
  | cons x o =>
    have hstep : sexec W i32Test KK fr .drop c (rs.map Prod.fst) =
        .next ⟨KK, { fr with code := c, ops := o } :: rs.map Prod.fst⟩ := by
      simp only [sexec, ho]
    rw [hstep]
    exact sim_drop S hT.main hT.conts ho hY henc

/-- The kernel's call, when the function exists and its arguments are popped. -/
theorem scall_next {P : Prog (Ins Val)} {f np : Nat} {body : List (Ins Val)} {ops args o : List (SV Val)}
    {c : List (Ins Val)} {rest : List (SFrame Val)} (hP : P f = some (np, body))
    (hp : popN np ops = some (args, o)) :
    scall P KK f fr ops c rest =
      .next ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o, wait := none } :: rest⟩ := by
  simp only [scall, hP, hp]

theorem scall_trap {P : Prog (Ins Val)} {f np : Nat} {body : List (Ins Val)} {ops : List (SV Val)}
    {c : List (Ins Val)} {rest : List (SFrame Val)} (hP : P f = some (np, body))
    (hp : popN np ops = none) : scall P KK f fr ops c rest = .stop .trap := by
  simp only [scall, hP, hp]

theorem matched_call (hok : Ok S W) (hT : Top S W KK K fr a rs) {f : Nat} {c : List (Ins Val)}
    {Y : List InstrFX} (hc : fr.code = .call f :: c)
    (hY : a.code = .core (.call (S.xf f)) :: Y) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.call f) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  cases hW : W f with
  | none => exact absurd (by simp only [sexec, scall, hW]) hnt
  | some nb =>
    obtain ⟨np, body⟩ := nb
    have hall : (allVals (fr.ops.take np)).isSome = true := by
      simpa only [fineTop, hc, hW] using hT.top
    cases hp : popN np fr.ops with
    | none => exact absurd (scall_trap (fr := fr) hW hp) hnt
    | some ao =>
      obtain ⟨args, o⟩ := ao
      obtain ⟨hops, hlen⟩ := popN_eq hp
      have htake : fr.ops.take np = args := by rw [hops, ← hlen, List.take_left]
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (htake ▸ hall)
      show Matched S W _ (scall W KK f fr fr.ops c (rs.map Prod.fst))
      rw [scall_next hW hp]
      exact sim_call S hok hT.main hT.conts hops hws hlen hW hY henc

theorem matched_contNew (hok : Ok S W) (hT : Top S W KK K fr a rs) {f : Nat}
    {bf c : List (Ins Val)} {Y : List InstrFX} (hc : fr.code = .contNew f :: c)
    (hY : a.code = .core (.refFunc (S.xf f)) :: .fx (.contNew S.ct) :: Y)
    (hf : W f = some (0, bf)) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hstep : sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩ =
      .next ⟨KK ++ [some [⟨bf, [], none⟩]],
        { fr with code := c, ops := .cont KK.length :: fr.ops } :: rs.map Prod.fst⟩ := by
    simp only [sstep_exec hc, sexec, hf]
  rw [hstep]
  exact sim_contNew S hok hT.main hT.conts hY hf henc

theorem matched_push (hT : Top S W KK K fr a rs) {v : Val} {i : Instr} {c : List (Ins Val)}
    {Y : List InstrFX} (hc : fr.code = .push v :: c) (hY : a.code = .core i :: .core .nop :: Y)
    (hv : Admin.plain i = v.toAdmin) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hstep : sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩ =
      .next ⟨KK, { fr with code := c, ops := .val v :: fr.ops } :: rs.map Prod.fst⟩ := by
    simp only [sstep_exec hc, sexec]
  rw [hstep]
  exact sim_push S hT.main hT.conts hY hv henc

theorem v_i32 {v : Val} (h : isI32 (.val v) = true) : ∃ b, v = Val.i32 b := by
  match v, h with
  | .num ⟨.int .i32, b⟩, _ => exact ⟨b, rfl⟩

theorem matched_cond (hok : Ok S W) (hT : Top S W KK K fr a rs) {f g np : Nat}
    {bf bg c : List (Ins Val)} {Y : List InstrFX} {bt : BlockType}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hc : fr.code = .cond f g :: c)
    (hY : a.code = .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: Y)
    (hf : W f = some (np, bf)) (hg : W g = some (np, bg))
    (hbt : S.M.blockType? bt = some (t₁, t₂)) (ht : t₁.length = np) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.cond f g) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  have htop : fineTop W fr (rs.map Prod.fst) = true := hT.top
  rw [sstep_exec hc]
  obtain ⟨v, o', ho⟩ : ∃ v o', fr.ops = .val v :: o' := by
    match hops : fr.ops, htop with
    | .val v :: o', _ => exact ⟨v, o', rfl⟩
    | [], h => simp only [fineTop, hc, hops, reduceCtorEq] at h
    | .cont _ :: _, h => simp only [fineTop, hc, hops, reduceCtorEq] at h
  have hWfn : W (if i32Test v then f else g) = some (np, if i32Test v then bf else bg) := by
    split <;> assumption
  have hfine : isI32 (.val v) = true ∧ (allVals (o'.take np)).isSome = true := by
    simpa only [fineTop, hc, ho, hWfn, Bool.and_eq_true] using htop
  obtain ⟨b, rfl⟩ := v_i32 hfine.1
  have hstep : sexec W i32Test KK fr (.cond f g) c (rs.map Prod.fst) =
      scall W KK (if i32Test (Val.i32 b) then f else g) fr o' c (rs.map Prod.fst) := by
    simp only [sexec, ho]
  rw [hstep]
  cases hp : popN np o' with
  | none => exact absurd (by simp only [sexec, ho, scall, hWfn, hp]) hnt
  | some ao =>
    obtain ⟨args, o⟩ := ao
    obtain ⟨hops, hlen⟩ := popN_eq hp
    have htake : o'.take np = args := by rw [hops, ← hlen, List.take_left]
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (htake ▸ hfine.2)
    rw [scall_next hWfn hp]
    exact sim_cond S hok hT.main hT.conts (by rw [ho, hops]; rfl) hws hlen hWfn hbt ht hY henc

theorem popN_zero {α : Type} (o : List α) : popN 0 o = some ([], o) := by
  simp only [popN, Nat.zero_le, ite_true, List.take_zero, List.drop_zero]

theorem with_ops_nil (top : SFrame Val) : { top with ops := [] ++ top.ops } = top := by
  cases top
  rfl

/-- The kernel's `resume` on continuation `k` with segment `top :: seg`. -/
theorem sexec_resume {k : Nat} {o : List (SV Val)} {hs : List Clause} {c : List (Ins Val)}
    {rest : List (SFrame Val)} {top : SFrame Val} {seg : List (SFrame Val)}
    (ho : fr.ops = .cont k :: o) (hk : KK[k]? = some (some (top :: seg))) :
    sexec W i32Test KK fr (.resume 0 hs) c rest =
      .next ⟨KK.set k none, top :: seg ++ { fr with code := c, ops := o, wait := some hs } :: rest⟩ := by
  simp only [sexec, ho, popN_zero, hk, with_ops_nil]

theorem matched_resume (hok : Ok S W) (hT : Top S W KK K fr a rs) {t hf np : Nat}
    {c bh : List (Ins Val)} {Y Z : List InstrFX} {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType} (hc : fr.code = .resume 0 [⟨t, hf⟩] :: c)
    (hY : a.code = .block btD (.block btH (bodyH S t) :: Z) :: Y) (htag : TagOk S t)
    (hh : W hf = some (np, bh)) (hZ : EncI S W bh Z)
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.resume 0 [⟨t, hf⟩]) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  obtain ⟨k, o, ho⟩ : ∃ k o, fr.ops = .cont k :: o := by
    match hops : fr.ops with
    | .cont k :: o => exact ⟨k, o, rfl⟩
    | [] => exact absurd (by simp only [sexec, hops]) hnt
    | .val _ :: _ => exact absurd (by simp only [sexec, hops]) hnt
  obtain ⟨top, seg, hk⟩ : ∃ top seg, KK[k]? = some (some (top :: seg)) := by
    match hkk : KK[k]? with
    | some (some (top :: seg)) => exact ⟨top, seg, rfl⟩
    | none => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
    | some none => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
    | some (some []) => exact absurd (by simp only [sexec, ho, popN_zero, hkk]) hnt
  rw [sexec_resume ho hk]
  exact sim_resume S hok hT.main hT.conts ho hk hY htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ henc

theorem matched_suspend (hok : Ok S W) (hT : Top S W KK K fr a rs) {t : Nat} {c : List (Ins Val)}
    {Y : List InstrFX} (hc : fr.code = .suspend t (S.ar t) :: c)
    (hY : a.code = .fx (.suspend (S.xt t)) :: Y) (htag : TagOk S t) (henc : EncI S W c Y) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.suspend t (S.ar t)) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  obtain ⟨pl, o, hp⟩ : ∃ pl o, popN (S.ar t) fr.ops = some (pl, o) := by
    match hpp : popN (S.ar t) fr.ops with
    | some (pl, o) => exact ⟨pl, o, rfl⟩
    | none => exact absurd (by simp only [sexec, hpp]) hnt
  obtain ⟨m, h, r, rs', hsp⟩ : ∃ m h r rs', split t (rs.map Prod.fst) = some (m, h, r, rs') := by
    match hss : split t (rs.map Prod.fst) with
    | some (m, h, r, rs') => exact ⟨m, h, r, rs', rfl⟩
    | none => exact absurd (by simp only [sexec, hp, hss]) hnt
  obtain ⟨np, body, hW⟩ : ∃ np body, W h = some (np, body) := by
    match hww : W h with
    | some (np, body) => exact ⟨np, body, rfl⟩
    | none => exact absurd (by simp only [sexec, hp, hsp, hww]) hnt
  have hstep : sexec W i32Test KK fr (.suspend t (S.ar t)) c (rs.map Prod.fst) =
      .next ⟨KK ++ [some ({ fr with code := c, ops := o } :: m)],
        ⟨body, .cont KK.length :: pl, none⟩ :: { r with wait := none } :: rs'⟩ := by
    simp only [sexec, hp, hsp, hW]
  obtain ⟨hops, hlen⟩ := popN_eq hp
  rw [hstep]
  exact sim_suspend S hok hT.main hT.conts hops hlen hY htag henc hsp hW

theorem matched_nil (hT : Top S W KK K fr a rs) (hc : fr.code = []) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  match rs, hT with
  | [], hT =>
    show Matched S W (cfgOf S K fr a []) (sstep W i32Test ⟨KK, fr :: [].map Prod.fst⟩)
    obtain ⟨ws, hws⟩ : ∃ ws, allVals fr.ops = some ws :=
      Option.isSome_iff_exists.mp (by simpa only [fineTop, hc, List.map_nil] using hT.top)
    have hstep : sstep W i32Test ⟨KK, [fr]⟩ = .stop (.done fr.ops) := by simp only [sstep, hc]
    rw [List.map_nil, hstep]
    have hb : (Result.values ws.reverse).toBehaviour = obsB (Outcome.done fr.ops).toObs := by
      simp only [Outcome.toObs, obsB, hws, Result.toBehaviour_values]
    show Outcome.done fr.ops ≠ .trap ∧ ∃ r : Result,
      (cfgOf S K fr a []).code = r.toAdmin.map AdminFX.core ∧
        r.toBehaviour = obsB (Outcome.done fr.ops).toObs
    exact ⟨(fun h => nomatch h), Result.values ws.reverse, done_result S hT.main hc hws, hb⟩
  | (b, ab) :: rs', hT =>
    show Matched S W (cfgOf S K fr a ((b, ab) :: rs'))
      (sstep W i32Test ⟨KK, fr :: ((b, ab) :: rs').map Prod.fst⟩)
    obtain ⟨r, hr⟩ : ∃ r, fr.ops = [r] := by
      have h1 : fr.ops.length = 1 := by
        simpa only [fineTop, hc, List.map_cons, beq_iff_eq] using hT.top
      match hops : fr.ops, h1 with
      | [r], _ => exact ⟨r, rfl⟩
    have hstep : sstep W i32Test ⟨KK, fr :: (b, ab).1 :: rs'.map Prod.fst⟩ =
        .next ⟨KK, { b with ops := fr.ops ++ b.ops } :: rs'.map Prod.fst⟩ := by
      simp only [sstep, hc]
    rw [List.map_cons, hstep]
    exact sim_return S hT.main hT.conts hc hr

/-- **Every kernel step from a top frame in the fragment is matched**, by the encoded
instruction. -/
theorem matched_top (hok : Ok S W) (hT : Top S W KK K fr a rs) :
    Matched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have henc : EncI S W fr.code a.code := (hT.main.1 _ (List.mem_cons_self ..)).1
  generalize hc : fr.code = code at henc
  generalize hY : a.code = Y at henc
  cases henc with
  | nil => exact matched_nil S hT hc
  | push hv h => exact matched_push S hT hc hY hv h
  | prim hi h => exact matched_prim S hok hT hc hY hi h
  | drop h => exact matched_drop S hT hc hY h
  | call h => exact matched_call S hok hT hc hY h
  | cond hf hg hbt ht h => exact matched_cond S hok hT hc hY hf hg hbt ht h
  | contNew hf h => exact matched_contNew S hok hT hc hY hf h
  | resume htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ h =>
    exact matched_resume S hok hT hc hY htag hh hZ hD hD₁ hD₂ hH hH₁ hH₂ h
  | suspend htag h => exact matched_suspend S hok hT hc hY htag h

theorem fine_cons {fr : SFrame Val} {rest : List (SFrame Val)}
    (h : fine W ⟨KK, fr :: rest⟩ = true) :
    sstep W i32Test ⟨KK, fr :: rest⟩ ≠ .stop .trap ∧ fineTop W fr rest = true := by
  refine ⟨fun ht => ?_, ?_⟩
  · simp only [fine, ht, Bool.false_and, Bool.false_eq_true] at h
  · simp only [fine, Bool.and_eq_true] at h
    exact h.2

/-- **The simulation step**: from related configurations, a kernel step in the fragment is
matched by `StepFX'`. -/
theorem sim_step (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hf : fine W x = true) : Matched S W c (sstep W i32Test x) := by
  obtain ⟨hs, hf₀, hK, st, hstk, hmain, hcode⟩ := hR
  have hc : c = ⟨S.s, c.conts, S.f0, (stkCtx S st).plug []⟩ := by
    rw [← hs, ← hf₀, ← hcode]
  match st, hmain, hstk with
  | [], hm, _ =>
    obtain ⟨init, last, heq, -⟩ := hm.2.2
    exact absurd heq.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | (fr, a) :: rs, hm, hstk =>
    have hx : x = ⟨x.conts, fr :: rs.map Prod.fst⟩ := by
      rw [← List.map_cons (f := Prod.fst) (a := (fr, a)), ← hstk]
    have hf' : fine W ⟨x.conts, fr :: rs.map Prod.fst⟩ = true := hx ▸ hf
    obtain ⟨hnt, htop⟩ := fine_cons hf'
    rw [hc, hx]
    exact matched_top S hok ⟨hm, hK, hnt, htop⟩

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
