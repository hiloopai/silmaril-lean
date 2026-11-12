module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.URet

/-!
# Backward simulation: the dispatch on the encoded instruction

The converses of `matched_nil`, `matched_prim`, `matched_drop`, `matched_call`,
`matched_contNew`, `matched_push` and `matched_cond`: from a related configuration in the
fragment, the kernel step is matched by `UMatched` (every `StepFX'` run reaches the next related
configuration). The kernel side of each case is the computation of `matched_*`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX Top cfgOf sstep_exec scall_next scall_trap popN_eq
  i32s_of_all v_i32 allVals_map done_result encI_nil)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} (S : Setup H) {W : Prog (Ins Val)}

variable {KK : List (Option (List (SFrame Val)))} {K : List (Option ContFX)} {fr : SFrame Val}
  {a : Ann} {rs : List (SFrame Val × Ann)}

theorem umatched_nil (hS : SX S = SD o S.fx) (hT : Top S W KK K fr a rs) (hc : fr.code = []) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  match rs, hT with
  | [], hT =>
    show UMatched S W (cfgOf S K fr a []) (sstep W i32Test ⟨KK, fr :: [].map Prod.fst⟩)
    obtain ⟨ws, hws⟩ : ∃ ws, allVals fr.ops = some ws :=
      Option.isSome_iff_exists.mp (by simpa only [fineTop, hc, List.map_nil] using hT.top)
    have hstep : sstep W i32Test ⟨KK, [fr]⟩ = .stop (.done fr.ops) := by simp only [sstep, hc]
    rw [List.map_nil, hstep]
    refine ⟨ws.reverse, ?_, ?_⟩
    · show (stkCtx S [(fr, a)]).plug [] = cvals ws.reverse
      rw [done_result S hT.main hc hws]
      rfl
    · simp only [Outcome.toObs, obsB, hws]
  | (b, ab) :: rs', hT =>
    show UMatched S W (cfgOf S K fr a ((b, ab) :: rs'))
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
    exact u_return S hS hT.main hT.conts hc hr

theorem umatched_prim (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) (hT : Top S W KK K fr a rs) {n : Nat}
    {op : List Val → List Val} {i : Instr} {c : List (Ins Val)} {Y : List InstrFX}
    (hc : fr.code = .prim n op :: c) (hY : a.code = .core i :: Y) (hi : PrimOk S n op i)
    (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hall : (fr.ops.take n).all isI32 = true := by simpa only [fineTop, hc] using hT.top
  have hnt : sexec W i32Test KK fr (.prim n op) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  cases hp : popN n fr.ops with
  | none => exact absurd (by simp only [sexec, hp]) hnt
  | some ao =>
    obtain ⟨args, o'⟩ := ao
    obtain ⟨hops, hlen⟩ := popN_eq hp
    have htake : fr.ops.take n = args := by rw [hops, ← hlen, List.take_left]
    obtain ⟨bs, rfl⟩ := i32s_of_all (htake ▸ hall)
    have hbs : bs.length = n := by simpa only [List.length_map] using hlen
    have hstep : sexec W i32Test KK fr (.prim n op) c (rs.map Prod.fst) =
        .next ⟨KK, { fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o' } ::
          rs.map Prod.fst⟩ := by
      simp only [sexec, hp, allVals_map]
    rw [hstep]
    exact u_prim S hS hP hH hok hT.main hT.conts hops hbs hY hi henc

theorem umatched_drop (hS : SX S = SD o S.fx) (hT : Top S W KK K fr a rs) {c : List (Ins Val)}
    {Y : List InstrFX} (hc : fr.code = .drop :: c) (hY : a.code = .core .drop :: Y)
    (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr .drop c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  rw [sstep_exec hc]
  cases ho : fr.ops with
  | nil => exact absurd (by simp only [sexec, ho]) hnt
  | cons x o' =>
    have hstep : sexec W i32Test KK fr .drop c (rs.map Prod.fst) =
        .next ⟨KK, { fr with code := c, ops := o' } :: rs.map Prod.fst⟩ := by
      simp only [sexec, ho]
    rw [hstep]
    exact u_drop S hS hT.main hT.conts ho hY henc

theorem umatched_call (hS : SX S = SD o S.fx) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    {f : Nat} {c : List (Ins Val)} {Y : List InstrFX} (hc : fr.code = .call f :: c)
    (hY : a.code = .core (.call (S.xf f)) :: Y) (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
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
      obtain ⟨args, o'⟩ := ao
      obtain ⟨hops, hlen⟩ := popN_eq hp
      have htake : fr.ops.take np = args := by rw [hops, ← hlen, List.take_left]
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (htake ▸ hall)
      show UMatched S W _ (scall W KK f fr fr.ops c (rs.map Prod.fst))
      rw [scall_next hW hp]
      exact u_call S hS hok hT.main hT.conts hops hws hlen hW hY henc

theorem umatched_contNew (hS : SX S = SD o S.fx) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    {f : Nat} {bf c : List (Ins Val)} {Y : List InstrFX} (hc : fr.code = .contNew f :: c)
    (hY : a.code = .core (.refFunc (S.xf f)) :: .fx (.contNew S.ct) :: Y)
    (hf : W f = some (0, bf)) (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hstep : sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩ =
      .next ⟨KK ++ [some [⟨bf, [], none⟩]],
        { fr with code := c, ops := .cont KK.length :: fr.ops } :: rs.map Prod.fst⟩ := by
    simp only [sstep_exec hc, sexec, hf]
  rw [hstep]
  exact u_contNew S hS hok hT.main hT.conts hY hf henc

theorem umatched_push (hS : SX S = SD o S.fx) (hT : Top S W KK K fr a rs) {v : Val} {i : Instr}
    {c : List (Ins Val)} {Y : List InstrFX} (hc : fr.code = .push v :: c)
    (hY : a.code = .core i :: .core .nop :: Y) (hv : Admin.plain i = v.toAdmin)
    (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hstep : sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩ =
      .next ⟨KK, { fr with code := c, ops := .val v :: fr.ops } :: rs.map Prod.fst⟩ := by
    simp only [sstep_exec hc, sexec]
  rw [hstep]
  exact u_push S hS hT.main hT.conts hY hv henc

theorem umatched_cond (hS : SX S = SD o S.fx) (hok : Ok S W) (hT : Top S W KK K fr a rs)
    {f g np : Nat} {bf bg c : List (Ins Val)} {Y : List InstrFX} {bt : BlockType}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hc : fr.code = .cond f g :: c)
    (hY : a.code = .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: Y)
    (hf : W f = some (np, bf)) (hg : W g = some (np, bg))
    (hbt : S.M.blockType? bt = some (t₁, t₂)) (ht : t₁.length = np) (henc : EncI S W c Y) :
    UMatched S W (cfgOf S K fr a rs) (sstep W i32Test ⟨KK, fr :: rs.map Prod.fst⟩) := by
  have hnt : sexec W i32Test KK fr (.cond f g) c (rs.map Prod.fst) ≠ .stop .trap := by
    rw [← sstep_exec hc]; exact hT.noTrap
  have htop : fineTop W fr (rs.map Prod.fst) = true := hT.top
  rw [sstep_exec hc]
  obtain ⟨v, o'', ho⟩ : ∃ v o'', fr.ops = .val v :: o'' := by
    match hops : fr.ops, htop with
    | .val v :: o'', _ => exact ⟨v, o'', rfl⟩
    | [], h => simp only [fineTop, hc, hops, reduceCtorEq] at h
    | .cont _ :: _, h => simp only [fineTop, hc, hops, reduceCtorEq] at h
  have hWfn : W (if i32Test v then f else g) = some (np, if i32Test v then bf else bg) := by
    split <;> assumption
  have hfine : isI32 (.val v) = true ∧ (allVals (o''.take np)).isSome = true := by
    simpa only [fineTop, hc, ho, hWfn, Bool.and_eq_true] using htop
  obtain ⟨b, rfl⟩ := v_i32 hfine.1
  have hstep : sexec W i32Test KK fr (.cond f g) c (rs.map Prod.fst) =
      scall W KK (if i32Test (Val.i32 b) then f else g) fr o'' c (rs.map Prod.fst) := by
    simp only [sexec, ho]
  rw [hstep]
  cases hp : popN np o'' with
  | none => exact absurd (by simp only [sexec, ho, scall, hWfn, hp]) hnt
  | some ao =>
    obtain ⟨args, o'⟩ := ao
    obtain ⟨hops, hlen⟩ := popN_eq hp
    have htake : o''.take np = args := by rw [hops, ← hlen, List.take_left]
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (htake ▸ hfine.2)
    rw [scall_next hWfn hp]
    exact u_cond S hS hok hT.main hT.conts (by rw [ho, hops]; rfl) hws hlen hWfn hbt ht hY henc

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
