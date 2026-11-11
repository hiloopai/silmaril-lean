module

public import Silmaril.Proofs.Wasm.Verify.Guard.Step
public import Silmaril.Proofs.Wasm.Verify.Reach.Strategy

/-!
# Guarded calls: the callout of a guarded call

* `guard_ctx`: when the guard discipline holds and the code is `E.fill [call x]` with `call x`
  a bad call, the hole of `E` is preceded by a guard: `E.fill Y = E'.fill (i32.const c :: Y)`
  with `c ≠ 0`.
* `fill_pair`: replacing the hole of an evaluation context keeps the guard discipline when
  the replacement does.
* `decompose_fill`: the host-call redex of `E.fill (vals args ++ [ref.func a, call_ref])` is
  found by `decompose?` with exactly the context `E` and the arguments `args`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {G B : Nat → Prop} {fs : List Nat}

/-! ## Guards before bad calls -/

theorem isGdA_toAdmin {v : Val} (h : isGdA v.toAdmin = true) :
    ∃ c : BitVec IntType.i32.width, v = .num ⟨.int .i32, c⟩ ∧ c ≠ 0 := by
  rcases v with ⟨⟨_ | _⟩, b⟩ | _ | _
  · exact ⟨b, rfl, bne_iff_ne.1 (by simpa [Val.toAdmin, isGdA] using h)⟩
  all_goals simp [Val.toAdmin, isGdA] at h

theorem nextSt_toAdmin {v : Val} {st : PSt} (hst : st ≠ .ex) :
    nextSt v.toAdmin st = if isGdA v.toAdmin then .gd else .other := by
  simp [nextSt, hst]

theorem finSt_vals_ne_ex {st : PSt} (hst : st ≠ .ex) : ∀ vs : List Val, finSt st (vals vs) ≠ .ex
  | [] => hst
  | v :: vs => by
    have h₁ : nextSt v.toAdmin st ≠ .ex := by rw [nextSt_toAdmin hst]; split <;> simp
    simpa [vals] using finSt_vals_ne_ex h₁ vs

/-- A value prefix that leaves the state other than `other` ends with a guard. -/
theorem vals_last_guard {pre : List Val} (h : finSt .other (vals pre) ≠ .other) :
    ∃ (pre' : List Val) (c : BitVec IntType.i32.width), pre = pre' ++ [.num ⟨.int .i32, c⟩] ∧
      c ≠ 0 := by
  rcases List.eq_nil_or_concat pre with rfl | ⟨pre', v, rfl⟩
  · exact absurd rfl h
  · rw [List.concat_eq_append] at h ⊢
    have hne : finSt .other (vals pre') ≠ .ex := finSt_vals_ne_ex (by simp) pre'
    have hv : finSt .other (vals (pre' ++ [v])) = nextSt v.toAdmin (finSt .other (vals pre')) := by
      simp [vals, finSt_append]
    rw [hv, nextSt_toAdmin hne] at h
    have hg : isGdA v.toAdmin = true := by
      by_contra hg
      simp [hg] at h
    obtain ⟨c, rfl, hc⟩ := isGdA_toAdmin hg
    exact ⟨pre', c, rfl, hc⟩

theorem badI_isBadA {x : FuncIdx} (h : BadI B fs (.call x)) : isBadA B fs (.plain (.call x)) := h

theorem deepP_sub_label {pre : List Val} {n : Nat} {k : List Instr} {body rest : List Admin}
    (h : DeepP B fs (vals pre ++ [.label n k body] ++ rest)) :
    Chain B fs .other body ∧ DeepP B fs body := by
  have h₁ : DeepP B fs [.label n k body] := (deepP_append.1 (deepP_append.1 h).1).2
  exact ⟨h₁.1 body (by simp), fun b hb => h₁.1 b (by simp [hb]), fun c hc => h₁.2 c (by simp [hc])⟩

theorem deepP_sub_handler {pre : List Val} {n : Nat} {cs : List Catch} {body rest : List Admin}
    (h : DeepP B fs (vals pre ++ [.handler n cs body] ++ rest)) :
    Chain B fs .other body ∧ DeepP B fs body := by
  have h₁ : DeepP B fs [.handler n cs body] := (deepP_append.1 (deepP_append.1 h).1).2
  exact ⟨h₁.1 body (by simp), fun b hb => h₁.1 b (by simp [hb]), fun c hc => h₁.2 c (by simp [hc])⟩

theorem deepP_sub_frame {pre : List Val} {n : Nat} {fr : Frame} {body rest : List Admin}
    (h : DeepP B fs (vals pre ++ [.frame n fr body] ++ rest)) :
    Chain B fs .other body ∧ DeepP B fs body := by
  have h₁ : DeepP B fs [.frame n fr body] := (deepP_append.1 (deepP_append.1 h).1).2
  exact ⟨h₁.1 body (by simp), fun b hb => h₁.1 b (by simp [hb]), fun c hc => h₁.2 c (by simp [hc])⟩

/-- **A bad call is preceded by a guard.** -/
theorem guard_ctx {x : FuncIdx} (hb : BadI B fs (.call x)) :
    ∀ (E : Ctx), Chain B fs .other (E.fill [.plain (.call x)]) →
      DeepP B fs (E.fill [.plain (.call x)]) →
      ∃ (E' : Ctx) (c : BitVec IntType.i32.width), c ≠ 0 ∧
        ∀ Y, E.fill Y = E'.fill (vals [.num ⟨.int .i32, c⟩] ++ Y)
  | .top pre rest, hch, _ => by
    have h₁ : Chain B fs (finSt .other (vals pre)) ([.plain (.call x)] ++ rest) := by
      simpa only [Ctx.fill, List.append_assoc, chain_vals_append] using hch
    have h₂ : finSt .other (vals pre) ≠ .other := h₁.1 (badI_isBadA hb)
    obtain ⟨pre', c, rfl, hc⟩ := vals_last_guard h₂
    exact ⟨.top pre' rest, c, hc, fun Y => by simp [Ctx.fill, vals]⟩
  | .label pre n k E rest, _, hd => by
    obtain ⟨hch', hd'⟩ := deepP_sub_label (by simpa only [Ctx.fill] using hd)
    obtain ⟨E', c, hc, hE⟩ := guard_ctx hb E hch' hd'
    exact ⟨.label pre n k E' rest, c, hc, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .handler pre n cs E rest, _, hd => by
    obtain ⟨hch', hd'⟩ := deepP_sub_handler (by simpa only [Ctx.fill] using hd)
    obtain ⟨E', c, hc, hE⟩ := guard_ctx hb E hch' hd'
    exact ⟨.handler pre n cs E' rest, c, hc, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .frame pre n fr E rest, _, hd => by
    obtain ⟨hch', hd'⟩ := deepP_sub_frame (by simpa only [Ctx.fill] using hd)
    obtain ⟨E', c, hc, hE⟩ := guard_ctx hb E hch' hd'
    exact ⟨.frame pre n fr E' rest, c, hc, fun Y => by simp [Ctx.fill, hE Y]⟩

/-! ## Replacing the hole of a context -/

theorem PairPost.congr {c c' d d' : Config H} (h : PairPost B fs c c') (hd : d.code = c.code)
    (hd' : d'.code = c'.code) : PairPost B fs d d' := by
  unfold PairPost
  rw [hd, hd']
  exact h

/-- **Replacing the hole of an evaluation context keeps the guard discipline.** -/
theorem fill_pair {s : Store H} {f : Frame} {X Y : List Admin}
    (h : PairPost B fs (⟨s, f, Y⟩ : Config H) ⟨s, f, X⟩) :
    ∀ (E : Ctx) (s' : Store H) (f' : Frame),
      PairPost B fs (⟨s', f', E.fill Y⟩ : Config H) ⟨s', f', E.fill X⟩
  | .top pre rest, s', f' => by
    have h' : PairPost B fs (⟨s', f', Y⟩ : Config H) ⟨s', f', X⟩ := h.congr rfl rfl
    simpa only [Ctx.fill] using pair_ctxtInstrs (vs := pre) (rest := rest) h'
  | .label pre n k E rest, s', f' => by
    simpa only [Ctx.fill] using pair_ctxtInstrs (vs := pre) (rest := rest)
      (pair_ctxtLabel (n := n) (cont := k) (fill_pair h E s' f'))
  | .handler pre n cs E rest, s', f' => by
    simpa only [Ctx.fill] using pair_ctxtInstrs (vs := pre) (rest := rest)
      (pair_ctxtHandler (n := n) (cs := cs) (fill_pair h E s' f'))
  | .frame pre n fr E rest, s', f' => by
    simpa only [Ctx.fill] using pair_ctxtInstrs (vs := pre) (rest := rest)
      (pair_ctxtFrame (n := n) (f := f') (fill_pair h E s' fr))

/-! ## The redex of a guarded call -/

theorem splitVals_label (n : Nat) (k : List Instr) (body : List Admin) :
    splitVals [.label n k body] = ([], [.label n k body]) := by
  simp [splitVals, Admin.val?]

theorem splitVals_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    splitVals [.handler n cs body] = ([], [.handler n cs body]) := by
  simp [splitVals, Admin.val?]

theorem splitVals_frame (n : Nat) (fr : Frame) (body : List Admin) :
    splitVals [.frame n fr body] = ([], [.frame n fr body]) := by
  simp [splitVals, Admin.val?]

/-- **The host-call redex of a filled context is found at that context.** -/
theorem decompose_fill {s : Store H} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    {c : Admin} (hc : c.IsCallRef) {args : List Val} (hn : args.length = ps.length) :
    ∀ E : Ctx, decompose? s (E.fill (vals args ++ [.ref (.func a), c])) = some (E, a, h, args)
  | .top pre rest => by
    have h₀ := decompose?_wrap pre rest (decompose?_redex hc hf he hn hcode)
    simpa [Ctx.fill, Ctx.wrap] using h₀
  | .label pre n k E rest => by
    have h₁ : decompose? s [.label n k (E.fill (vals args ++ [.ref (.func a), c]))] =
        some (.label [] n k E [], a, h, args) := by
      rw [decompose?_of_split (splitVals_label _ _ _)]
      simp [decompHead, decompose_fill hf he hcode hc hn E]
    have h₀ := decompose?_wrap pre rest h₁
    simpa [Ctx.fill, Ctx.wrap] using h₀
  | .handler pre n cs E rest => by
    have h₁ : decompose? s [.handler n cs (E.fill (vals args ++ [.ref (.func a), c]))] =
        some (.handler [] n cs E [], a, h, args) := by
      rw [decompose?_of_split (splitVals_handler _ _ _)]
      simp [decompHead, decompose_fill hf he hcode hc hn E]
    have h₀ := decompose?_wrap pre rest h₁
    simpa [Ctx.fill, Ctx.wrap] using h₀
  | .frame pre n fr E rest => by
    have h₁ : decompose? s [.frame n fr (E.fill (vals args ++ [.ref (.func a), c]))] =
        some (.frame [] n fr E [], a, h, args) := by
      rw [decompose?_of_split (splitVals_frame _ _ _)]
      simp [decompHead, decompose_fill hf he hcode hc hn E]
    have h₀ := decompose?_wrap pre rest h₁
    simpa [Ctx.fill, Ctx.wrap] using h₀

end Silmaril.Wasm.Verify
