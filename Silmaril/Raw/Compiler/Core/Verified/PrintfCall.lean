module

public import Silmaril.Compiler.Core.Verified.PrintfKill.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The variadic printf call and cleanup boundary

Recognize the actual one-int variadic list supplied by Cerberus, run the
canonical proxy, then run its unsequenced cleanup. The integer is loaded from
its live argument object; the proof is parametric in its value and caller.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfCall

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval)
open PrintfStd PrintfStmt StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-- The callee, format object and one typed variadic integer object (the `int` type may carry
annotations, such as its source location). -/
def ccallInt : EExp → Option (Sym × Sym × Sym)
  | .mk _ (.ccall _ _ (.mk _ _ (.sym g)) [.mk _ _ (.sym q),
      .mk _ _ (.ctor .cons [.mk _ _ (.ctor .tuple [
        .mk _ _ (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ _ (.sym p)]),
        .mk _ _ (.ctor (.nil _) [])])]) => some (g, q, p)
  | _ => none

/-- `int`, with any annotations. -/
def isIntTy : Ctype → Bool
  | .mk _ (.basic (.integer (.signed .int))) => true
  | _ => false

/-- The two kills following the call. -/
def cleanupOf : EExp → Option (EExp × EExp)
  | .mk _ (.unseq [a, b]) => some (a, b)
  | _ => none

/-- The real call, cleanup and return of its result. -/
def callInt (e : EExp) : Option (Sym × Sym × Sym) := do
  let (ret, cl, r1) ← sseqOf e
  let (g, q, p) ← ccallInt cl
  let (kl, r2) ← sseqNone r1
  let (k0, k1) ← cleanupOf kl
  let (t0, q') ← killOf k0
  let (t1, p') ← killOf k1
  let ret' ← pureSym r2
  if isCharPtr t0 ∧ isIntTy t1 ∧ q'.key = q.key ∧ p'.key = p.key ∧
      ret'.key = ret.key ∧ ret.key ≠ q.key ∧ ret.key ≠ p.key then some (g, q, p) else none

theorem ccallInt_inv {e : EExp} {g q p : Sym} (h : ccallInt e = some (g, q, p)) :
    ∃ ann u ty a1 u1 a2 u2 a3 u3 a4 u4 a5 u5 iann a6 u6 a7 u7 bt,
      e = .mk ann (.ccall u ty (.mk a1 u1 (.sym g)) [.mk a2 u2 (.sym q),
        .mk a3 u3 (.ctor .cons [.mk a4 u4 (.ctor .tuple [
          .mk a5 u5 (.val (.ctype (Mem.Concrete.intType iann))), .mk a6 u6 (.sym p)]),
          .mk a7 u7 (.ctor (.nil bt) [])])]) := by
  unfold ccallInt at h
  split at h
  · cases h
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem isIntTy_inv {t : Ctype} (h : isIntTy t = true) : ∃ a, t = Mem.Concrete.intType a := by
  unfold isIntTy at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem cleanupOf_inv {e a b : EExp} (h : cleanupOf e = some (a, b)) :
    ∃ ann, e = .mk ann (.unseq [a, b]) := by
  unfold cleanupOf at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

variable (file : Program) (labels : Labels)

/-- The actual variadic list evaluates to the typed pointer pair. -/
theorem ccall_reaches {e : EExp} {g q p : Sym} (h : ccallInt e = some (g, q, p))
    {env : Env} {proxy : Sym} {fid faddr iid iaddr : Int}
    (hg : env.lookup g = some (.loaded (.specified (.pointer (.function proxy)))))
    (hq : env.lookup q = some (.object (.pointer (.allocated fid faddr))))
    (hp : env.lookup p = some (.object (.pointer (.allocated iid iaddr))))
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ ann bt iann, ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.apply (.procedure env) [.loaded (.specified (.pointer (.function proxy))),
        .object (.pointer (.allocated fid faddr)),
        .list bt [.tuple [.ctype (Mem.Concrete.intType iann), .object (.pointer (.allocated iid iaddr))]]],
        k, SeqReach.focusMemory ann m⟩ := by
  obtain ⟨ann, u, ty, a1, u1, a2, u2, a3, u3, a4, u4, a5, u5, iann, a6, u6, a7, u7, bt, rfl⟩ :=
    ccallInt_inv h
  cases u; cases u1; cases u2; cases u3; cases u4; cases u5; cases u6; cases u7
  refine ⟨ann, bt, iann, (CallReach.ccall_enter ann ty _ _ env k m).trans
    ((SeqReach.pure_symbol a1 g env _ hg _ _).trans ?_)⟩
  apply CallReach.arguments_reaches
  refine .cons (SeqReach.pure_symbol a2 q env _ hq) (.cons ?_ .nil)
  apply PrintfStd.pe_of_eval
  intro tags
  exact .ctor (.cons (.ctor (.cons .val (.cons (.sym hp) .nil)) rfl)
    (.cons (.ctor .nil rfl) .nil)) rfl

/-- Printing a runtime int and killing both call temporaries preserves all
older objects and any output that preceded this statement. -/
theorem callInt_reaches {e : EExp} {g q p : Sym} (h : callInt e = some (g, q, p))
    {env : Env} {proxy : Sym} {s : Std} (hs : stdOf file proxy = some s)
    (hg : env.lookup g = some (.loaded (.specified (.pointer (.function proxy)))))
    {fid faddr sid saddr iid iaddr n : Int}
    (hq : env.lookup q = some (.object (.pointer (.allocated fid faddr))))
    (hp : env.lookup p = some (.object (.pointer (.allocated iid iaddr))))
    {cs : List Int} (hcs : StringFormat cs) {m : Mem.Concrete.State}
    (fmt : PtrObj m fid faddr sid saddr) (str : StrObj m sid saddr cs)
    (slot : Locals.Slot m iid iaddr n) (below : iid < m.nextId) (above : m.lastAddress ≤ iaddr)
    (range : Mem.Concrete.IntRange n) (ne : fid ≠ iid)
    (pre suffix : List Char) (hpre : ∀ c ∈ pre, c ≠ '%') (hsuf : ∀ c ∈ suffix, c ≠ '%')
    (shape : cs.dropLast.map (fun c => Char.ofNat c.toNat) = pre ++ '%' :: 'd' :: suffix)
    (k : List Frame) :
    ∃ m' zs, ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.loaded (.specified (.integer
        (String.ofList pre ++ (toString n ++ String.ofList suffix)).length))),
        .annotations zs :: k, m'⟩ ∧
      m'.stdout = m.stdout ++ (String.ofList pre ++ (toString n ++ String.ofList suffix)) ∧
      m'.nextId = m.nextId ∧ m'.lastAddress = m.lastAddress ∧ m'.dead = fid :: iid :: m.dead ∧
      (∀ m₀, Keeps m₀ m → m₀.nextId ≤ fid → m₀.nextId ≤ iid → Keeps m₀ m') := by
  unfold callInt at h
  obtain ⟨⟨ret, cl, r1⟩, q1, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨g', q', p'⟩, q2, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨kl, r2⟩, q3, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨e0, e1⟩, q4, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨t0, q''⟩, q5, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨⟨t1, p''⟩, q6, h⟩ := bind_some h; try dsimp only at h
  obtain ⟨ret', q7, h⟩ := bind_some h
  split at h
  case isFalse => cases h
  rename_i hc
  cases h
  obtain ⟨hct, hit, kq, kp, kr, nrq, nrp⟩ := hc
  obtain ⟨tann, qual, cann, rfl⟩ := isCharPtr_inv hct
  obtain ⟨kann, rfl⟩ := isIntTy_inv hit
  obtain ⟨B0, P0, b0, rfl⟩ := sseqOf_inv q1
  let K := .strongBind (.mk P0 (.base (some ret, b0))) r1 env :: k
  obtain ⟨C0, bt, iann, run⟩ := ccall_reaches file labels q2 hg hq hp K m
  let mc := SeqReach.focusMemory C0 m
  have keep : Keeps m mc := keeps_focus C0 m
  have slotc := PrintfVariadic.slot_keeps slot below above keep
  have chain := (ExitCall.lift file labels (ExitCall.ra_sseq file labels B0 _ _ _)
    (ExitCall.plain_effectExpr _ _)).trans run
  obtain ⟨m2, zs, run2, out2, keep2, alloc2⟩ := PrintfStmt.bridgeP file labels chain
    (PrintfVariadic.proxy_decimal_reaches hs hcs (fmt.keeps keep) (str.keeps keep)
      slotc (by simpa [mc] using below) (by simpa [mc] using above)
      range pre suffix hpre hsuf shape env K bt)
  obtain ⟨B1, P1, b1, rfl⟩ := sseqNone_inv q3
  obtain ⟨A0, rfl⟩ := cleanupOf_inv q4
  obtain ⟨B2, a2, u2, rfl⟩ := pureSym_inv q7
  cases u2
  let E := extendEnv [(ret, .loaded (.specified (.integer
    (String.ofList pre ++ (toString n ++ String.ofList suffix)).length)))] env
  have hq2 : E.lookup q'' = some (.object (.pointer (.allocated fid faddr))) := by
    rw [ReturnLit.lookup_key kq, lk_other (Ne.symm nrq)]; exact hq
  have hp2 : E.lookup p'' = some (.object (.pointer (.allocated iid iaddr))) := by
    rw [ReturnLit.lookup_key kp, lk_other (Ne.symm nrp)]; exact hp
  have keep02 := keep.trans keep2
  have slot2 := PrintfVariadic.slot_keeps slot below above keep02
  obtain ⟨m3, run3, out3, next3, last3, dead3, keep3⟩ := PrintfKill.cleanup
    (file := file) (labels := labels) tann kann qual (charTy cann) q5 q6 hq2 hp2
    (fmt.slot.keeps keep02) slot2.live ne A0
    (.strongBind (.mk P1 (.base (none, b1))) (.mk B2 (.pure (.mk a2 () (.sym ret')))) E :: .annotations zs :: k)
  have run4 := run2.trans ((v_strongBind zs rfl _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels B1 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (run3.trans ((v_strongBind [] (ys := []) rfl _ _).trans
    ((SeqReach.effect_pure_reaches B2 (SeqReach.pure_symbol a2 ret' E _ (lk_same kr _ _)) _ _).trans
    (v_merge _ _ _ _ _))))))
  obtain ⟨last2, next2, dead2⟩ := alloc2
  refine ⟨SeqReach.focusMemory B2 m3, [] ++ zs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [E, K] using run4
  · simp [out3, out2, mc]
  · simp [next3, next2, mc]
  · simp [last3, last2, mc]
  · simp [dead3, dead2, mc]
  · intro m₀ keep0 hf hi
    exact (keep3 m₀ (keep0.trans keep02) hf hi).trans (keeps_focus B2 _)

end Silmaril.Compile.Core.Verified.PrintfCall
