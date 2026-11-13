module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Safe
public import Silmaril.Wasm.JcoTool.KTee.Defs

/-!
# The callback of the generated tee is safe on Core 3.0

`genT_cbSafe`: `CbSafe (KTee.genT N) g` for `N ≤ 256` and globals whose batch length is at most
`256` (`KTee.okT`'s bound). Every `dexec` run of the tee's callback `KTee.cbT N` is a `bexec CBL`
run, so `KCoreRun.rstep_core` applies to the tee.

The callback has no loop. Almost all of it is *syntactically* safe (`SOk`): locals below `CBL`,
globals below `NG`, every divisor the constant `16`, every load and store at a constant address in
memory, `stream.read` into the constant buffer `IN` of at most `256` bytes, the drops. Such a
statement is safe from every state (`sok_safe`). The one exception is the write of output `j`
(`KTee.actW j`), whose buffer `IN + OFF j .. IN + LEN` is in memory because its guard `wrG j` gives
`OFF j < LEN` and the precondition `LEN ≤ 256` (`actW_safe`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Tee

open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Proofs.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 Bin IN LR INSR OUTSW WS yield_ seqs locals FUEL)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec dcallBI isE andE)
open Silmaril.Wasm.JcoTool.KTee

/-! ## Syntactically safe code -/

/-- An expression `cev CBL` computes in every state. -/
def EOkS : E → Bool
  | .c _ => true
  | .l i => decide (i < CBL)
  | .g i => decide (i < NG)
  | .bin o a b => EOkS a && EOkS b &&
      (match o, b with
       | .divu, .c n => decide (n % M32 ≠ 0)
       | .remu, .c n => decide (n % M32 ≠ 0)
       | .divu, _ => false
       | .remu, _ => false
       | _, _ => true)
  | .eqz a => EOkS a
  | .ld8 (.c n) => decide (n % M32 < MSZ)
  | .ld8 _ => false

theorem eoks_ok {s : DSt} : ∀ {e : E}, EOkS e = true → EOk CBL s e
  | .c _, _ => trivial
  | .l i, h => show i < CBL by simpa [EOkS] using h
  | .g i, h => show i < NG by simpa [EOkS] using h
  | .bin o a b, h => by
    simp only [EOkS, Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hd⟩ := h
    refine ⟨eoks_ok ha, eoks_ok hb, fun ho => ?_⟩
    rcases ho with rfl | rfl <;> (cases b <;> simp_all [E.eval])
  | .eqz a, h => eoks_ok (e := a) h
  | .ld8 (.c n), h => by
    refine ⟨trivial, ?_⟩
    simpa [EOkS, E.eval] using h
  | .ld8 (.l _), h => by simp [EOkS] at h
  | .ld8 (.g _), h => by simp [EOkS] at h
  | .ld8 (.bin _ _ _), h => by simp [EOkS] at h
  | .ld8 (.eqz _), h => by simp [EOkS] at h
  | .ld8 (.ld8 _), h => by simp [EOkS] at h

/-- A statement `bexec CBL` runs wherever `dexec` does, from every state. -/
def SOk : S → Bool
  | .nop => true
  | .unreachable => true
  | .lset i e => decide (i < CBL) && EOkS e
  | .gset i e => decide (i < NG) && EOkS e
  | .st8 (.c a) v => decide (a % M32 < MSZ) && EOkS v
  | .seq a b => SOk a && SOk b
  | .ite c t e => EOkS c && SOk t && SOk e
  | .ret e => EOkS e
  | .call .dropR [a] [] => EOkS a
  | .call .dropW [a] [] => EOkS a
  | .call .streamRead [h, .c p, .c n] [d] =>
    EOkS h && decide (d < CBL) && decide (p % M32 + n % M32 ≤ MSZ)
  | _ => false

theorem True_lout : ∀ o s, (fun _ _ => True : Out → DSt → Prop) o s → True := fun _ _ _ => trivial

/-- **Syntactically safe statements are safe from every state.** -/
theorem sok_safe {P : DSt → Prop} : ∀ {S : S}, SOk S = true → Safe CBL P S (fun _ _ => True)
  | .nop, _ => safe_nop fun _ _ => trivial
  | .unreachable, _ => safe_unreachable
  | .lset i e, h => by
    simp only [SOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact safe_lset h.1 fun _ _ => ⟨eoks_ok h.2, trivial⟩
  | .gset i e, h => by
    simp only [SOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact safe_gset h.1 fun _ _ => ⟨eoks_ok h.2, trivial⟩
  | .st8 (.c a) v, h => by
    simp only [SOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact safe_st8 fun _ _ => ⟨trivial, eoks_ok h.2, by simpa [E.eval] using h.1, trivial⟩
  | .seq a b, h => by
    simp only [SOk, Bool.and_eq_true] at h
    exact safe_seq (sok_safe h.1) (sok_safe h.2) fun _ _ _ _ => trivial
  | .ite c t e, h => by
    simp only [SOk, Bool.and_eq_true] at h
    exact safe_ite (fun _ _ => eoks_ok h.1.1) (sok_safe h.1.2) (sok_safe h.2) fun _ _ _ => trivial
  | .ret e, h => safe_ret fun _ _ => ⟨eoks_ok h, trivial⟩
  | .call .dropR [a] [], h => safe_call fun _ _ =>
      ⟨by simpa using eoks_ok (s := _) h, fun _ hr => bcall_dropR hr, fun _ _ _ => trivial⟩
  | .call .dropW [a] [], h => safe_call fun _ _ =>
      ⟨by simpa using eoks_ok (s := _) h, fun _ hr => bcall_dropW hr, fun _ _ _ => trivial⟩
  | .call .streamRead [hh, .c p, .c n] [d], h => by
    simp only [SOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hh', hd⟩, hm⟩ := h
    refine safe_call fun s _ => ⟨?_, fun r hr => bcall_read ?_ hd hr, fun _ _ _ => trivial⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact eoks_ok hh'
      · trivial
      · trivial
    · simp only [E.eval, memOK]
      exact decide_eq_true hm
  -- every other statement is not `SOk`
  | .st8 (.l _) _, h | .st8 (.g _) _, h | .st8 (.bin _ _ _) _, h | .st8 (.eqz _) _, h
  | .st8 (.ld8 _) _, h | .mcopy _ _ _, h | .block _, h | .loop _, h | .br _, h | .brIf _ _, h => by
    simp [SOk] at h
  | .call .streamNew _ _, h | .call .streamWrite _ _, h | .call .wsNew _ _, h | .call .join _ _, h
  | .call .taskReturn _ _, h => by simp [SOk] at h
  | .call .dropR [] _, h | .call .dropR (_ :: _ :: _) _, h | .call .dropR [_] (_ :: _), h
  | .call .dropW [] _, h | .call .dropW (_ :: _ :: _) _, h | .call .dropW [_] (_ :: _), h => by
    simp [SOk] at h
  | .call .streamRead [] _, h | .call .streamRead [_] _, h | .call .streamRead [_, _] _, h
  | .call .streamRead (_ :: _ :: _ :: _ :: _) _, h => by simp [SOk] at h
  | .call .streamRead [_, .l _, _] _, h | .call .streamRead [_, .g _, _] _, h
  | .call .streamRead [_, .bin _ _ _, _] _, h | .call .streamRead [_, .eqz _, _] _, h
  | .call .streamRead [_, .ld8 _, _] _, h => by simp [SOk] at h
  | .call .streamRead [_, .c _, .l _] _, h | .call .streamRead [_, .c _, .g _] _, h
  | .call .streamRead [_, .c _, .bin _ _ _] _, h | .call .streamRead [_, .c _, .eqz _] _, h
  | .call .streamRead [_, .c _, .ld8 _] _, h => by simp [SOk] at h
  | .call .streamRead [_, .c _, .c _] [], h | .call .streamRead [_, .c _, .c _] (_ :: _ :: _), h => by
    simp [SOk] at h

/-! ## The write of an output -/

theorem andE_ne {s : Silmaril.Wasm.JcoTool.KCore.St} {a b : E} (h : (andE a b).eval s ≠ 0) :
    a.eval s ≠ 0 ∧ b.eval s ≠ 0 := by
  refine ⟨fun h0 => h ?_, fun h0 => h ?_⟩ <;> simp only [andE, E.eval, Bin.eval, h0, ↓reduceIte] <;>
    split <;> simp_all [M32]

theorem wrG_lt {s : DSt} {j : Nat} (h : (wrG j).eval s.down ≠ 0) : s.g (OFFg j) < s.g LENg := by
  have h2 := (andE_ne h).2
  simp only [E.eval, Bin.eval] at h2
  by_contra hc
  simp_all [DSt.down]

theorem actW_rest_ok (j : Nat) (hj : j ≤ 1) :
    SOk (.seq (.ite (isE (.l LR) Silmaril.Wasm.Component.Async.blocked) (.st8 (.c (aO j)) (.c 1))
      (onW j (.l LR))) yield_) = true := by
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl

/-- **The write of output `j`**: its buffer `IN + OFF j`, `LEN - OFF j` lies in memory. -/
theorem actW_safe (j : Nat) (hj : j ≤ 1) :
    Safe CBL (fun s => s.g LENg ≤ 256 ∧ (wrG j).eval s.down ≠ 0) (actW j) (fun _ _ => True) := by
  have hW : WHg j < NG := by unfold WHg; split <;> decide
  have hO : OFFg j < NG := by unfold OFFg; split <;> decide
  refine safe_seq (R := fun _ _ => True) ?_ (sok_safe (actW_rest_ok j hj)) fun _ _ _ _ => trivial
  refine safe_call fun s ⟨hL, hg⟩ => ⟨?_, fun r hr => bcall_write ?_ (by decide) hr, fun _ _ _ => trivial⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (show EOk CBL s (.g (WHg j)) from hW)
    · exact ⟨trivial, hO, fun h => by rcases h with h | h <;> cases h⟩
    · exact ⟨(show LENg < NG by decide), hO, fun h => by rcases h with h | h <;> cases h⟩
  · have hlt := wrG_lt hg
    have hl : s.g LENg ≤ 256 := hL
    simp only [E.eval, Bin.eval, memOK, DSt.down, IN, M32]
    apply decide_eq_true
    have e : (2 : Nat) ^ 32 = 4294967296 := rfl
    simp only [e]
    unfold MSZ
    omega

/-! ## The callback -/

theorem readyRest_ok (N : Nat) (hN : N ≤ 256) :
    SOk (.ite rdG (actR N) <| .ite stopG actStop <| .ite (closeG 0) (actClose 0) <|
      .ite (closeG 1) (actClose 1) <| .ite exitG (.ret (.c 0)) (.ret Silmaril.Wasm.JcoTool.KCore.waitCode)) = true := by
  simp only [SOk, EOkS, actR, seqs, onR, endedOf, actStop, actClose, rdG, stopG, closeG, exitG, orE,
    andE, isE, ldA, aRS, aO, OFFg, WHg, Silmaril.Wasm.JcoTool.KCore.waitCode, yield_, Bool.and_eq_true,
    decide_eq_true_eq]
  simp [IN, MSZ, CBL, NG, LR, INSR, OUTSW, WS, LENg, OFF0, OFF1, W1g, M32]
  omega

/-- **The tee's callback is safe from states whose batch length is at most `256`.** -/
theorem cbT_safe (N : Nat) (hN : N ≤ 256) :
    Safe CBL (fun s => s.g LENg ≤ 256) (cbT N) (fun _ _ => True) := by
  have hev : SOk evR = true := rfl
  have hw0 : SOk (evW 0) = true := rfl
  have hw1 : SOk (evW 1) = true := rfl
  have hy := readyRest_ok N hN
  have tt : ∀ o s, (fun _ _ => True : Out → DSt → Prop) o s → (fun _ _ => True : Out → DSt → Prop) (lout o) s :=
    fun _ _ _ => trivial
  unfold cbT readyT
  refine safe_ite (fun _ _ => eoks_ok rfl) (sok_safe hev) ?_ tt
  refine safe_ite (fun _ _ => eoks_ok rfl) (sok_safe hw0) ?_ tt
  refine safe_ite (fun _ _ => eoks_ok rfl) (sok_safe hw1) ?_ tt
  refine safe_ite (fun _ _ => eoks_ok rfl) ?_ safe_unreachable tt
  refine safe_ite (fun _ _ => eoks_ok rfl) ?_ ?_ tt
  · exact (actW_safe 0 (by decide)).conseq (fun s h => ⟨h.1.1.1.1.1, h.2⟩) fun _ _ h => h
  refine safe_ite (fun _ _ => eoks_ok rfl) ?_ (sok_safe hy) tt
  exact (actW_safe 1 (by decide)).conseq (fun s h => ⟨h.1.1.1.1.1.1, h.2⟩) fun _ _ h => h

/-- **`CbSafe` for the generated tee.** -/
theorem genT_cbSafe {N : Nat} (hN : N ≤ 256) (g : Nat → Nat) (hg : g LENg ≤ 256) :
    CbSafe (genT N) g := by
  intro ps m st rp r _ hd
  obtain ⟨o, s'⟩ := r
  exact (cbT_safe N hN FUEL ⟨g, m, locals ps, st, rp⟩ o s' hg hd).1

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Tee
