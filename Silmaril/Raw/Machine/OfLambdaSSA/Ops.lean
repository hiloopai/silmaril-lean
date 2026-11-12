module

public import Silmaril.Machine.OfLambdaSSA.Defs

/-!
# One opcode, one op (unrefined)

`opOf f as ds` is the RTL op that performs opcode `f` on argument registers `as`
into destination registers `ds`. It runs from a frame holding the words `ws` in
`as` exactly when the opcode steps on `packValues ws`, and it leaves the result
words in `ds`; and an op changes only the registers it defines.

These are case analyses over the seven opcodes, valid but not refined into
a declarative style; they stay in `Raw` and are used only
by `Silmaril.Proofs.Machine.OfLambdaSSA`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Isotope (Value)

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-- An op changes only the registers it defines. -/
theorem op_exec_get {o : Op ℕ} {fr fr' : Frame ℕ} {m m' : Memory}
    (h : o.exec fr m = some (fr', m')) {x : ℕ} (hx : x ∉ o.defs) : fr'.get x = fr.get x := by
  cases o with
  | const d v =>
    obtain ⟨rfl, -⟩ : fr.set d v = fr' ∧ m = m' := by simpa [Op.exec] using h
    simp [Frame.get_set, show x ≠ d by simpa [Op.defs] using hx]
  | move d s =>
    obtain ⟨w, -, rfl, -⟩ : ∃ w, fr.get s = some w ∧ fr.set d w = fr' ∧ m = m' := by
      simpa [Op.exec] using h
    simp [Frame.get_set, show x ≠ d by simpa [Op.defs] using hx]
  | unary op d s =>
    obtain ⟨w, -, rfl, -⟩ : ∃ w, fr.get s = some w ∧ fr.set d (op.eval w) = fr' ∧ m = m' := by
      simpa [Op.exec] using h
    simp [Frame.get_set, show x ≠ d by simpa [Op.defs] using hx]
  | binary op d a b =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, rfl, -⟩ := h
    simp [Frame.get_set, show x ≠ d by simpa [Op.defs] using hx]
  | load w e d b off =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, rfl, -⟩ := h
    simp [Frame.get_set, show x ≠ d by simpa [Op.defs] using hx]
  | store w b off s =>
    simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, rfl, -⟩ := h
    rfl
  | call => simp [Op.exec] at h


/-- The ops `opOf` builds, one per opcode. -/
theorem opOf_some {f : Opcode sigs} {as ds : List ℕ} {o : Op ℕ} (h : opOf f as ds = some o) :
    (∃ v d, f = .const v ∧ as = [] ∧ ds = [d] ∧ o = .const d v) ∨
    (∃ s d, f = .move ∧ as = [s] ∧ ds = [d] ∧ o = .move d s) ∨
    (∃ op s d, f = .unary op ∧ as = [s] ∧ ds = [d] ∧ o = .unary op d s) ∨
    (∃ op a b d, f = .binary op ∧ as = [a, b] ∧ ds = [d] ∧ o = .binary op d a b) ∨
    (∃ w e off b d, f = .load w e off ∧ as = [b] ∧ ds = [d] ∧ o = .load w e d b off) ∨
    (∃ w off b s, f = .store w off ∧ as = [b, s] ∧ ds = [] ∧ o = .store w b off s) ∨
    (∃ c, f = .call c ∧ as.length = (sigAt sigs c).params ∧ o = .call c as ds) := by
  unfold opOf at h
  split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; simp)
    | (split at h
       · rename_i hlen
         simp only [Option.some.injEq] at h
         subst h
         simp [hlen]
       · simp at h)
    | simp at h

/-- A read of one register. -/
theorem readAll_one {fr : Frame ℕ} {r : ℕ} {ws : List Word} (h : fr.readAll [r] = some ws) :
    ∃ x, fr.get r = some x ∧ ws = [x] := by
  obtain ⟨x, ws', hx, hrest, rfl⟩ := readAll_cons_eq_some.mp h
  exact ⟨x, hx, by simpa using hrest.symm⟩

/-- A read of two registers. -/
theorem readAll_two {fr : Frame ℕ} {r r' : ℕ} {ws : List Word}
    (h : fr.readAll [r, r'] = some ws) : ∃ x y, fr.get r = some x ∧ fr.get r' = some y ∧
      ws = [x, y] := by
  obtain ⟨x, ws', hx, hrest, rfl⟩ := readAll_cons_eq_some.mp h
  obtain ⟨y, hy, rfl⟩ := readAll_one hrest
  exact ⟨x, y, hx, hy, rfl⟩

/-- Reading a register just written. -/
theorem readAll_set (fr : Frame ℕ) (d : ℕ) (w : Word) : (fr.set d w).readAll [d] = some [w] := by
  simp [readAll_cons, Frame.get_set]

/-- **An opcode's step is its op's run**, forwards: the op runs and leaves the
result words in its destinations. -/
theorem op_forward (hsigs : CallOracle.MatchesSigs oracle sigs) {f : Opcode sigs}
    {as ds : List ℕ} {o : Op ℕ} (ho : opOf f as ds = some o) (hn : ds.Nodup)
    (hlen : ds.length = f.results) {fr : Frame ℕ} {ws : List Word} (hr : fr.readAll as = some ws)
    {m m' : Memory} {v : Value Word} (hstep : Opcode.step oracle f (packValues ws) m v m') :
    ∃ fr' rs, Ops.Exec oracle [o] fr m fr' m' ∧ fr'.readAll ds = some rs ∧ v = packValues rs := by
  rcases opOf_some ho with ⟨c, d, rfl, rfl, rfl, rfl⟩ | ⟨s, d, rfl, rfl, rfl, rfl⟩ |
      ⟨op, s, d, rfl, rfl, rfl, rfl⟩ | ⟨op, a, b, d, rfl, rfl, rfl, rfl⟩ |
      ⟨w, e, off, b, d, rfl, rfl, rfl, rfl⟩ | ⟨w, off, b, s, rfl, rfl, rfl, rfl⟩ |
      ⟨c, rfl, -, rfl⟩
  · obtain rfl : ws = [] := by simpa using hr.symm
    cases hstep
    exact ⟨_, _, .op rfl .nil, readAll_set fr d c, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hstep
    exact ⟨_, _, .op (by simp [Op.exec, hx]) .nil, readAll_set fr d x, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hstep
    exact ⟨_, _, .op (by simp [Op.exec, hx]) .nil, readAll_set fr d _, rfl⟩
  · obtain ⟨x, y, hx, hy, rfl⟩ := readAll_two hr
    cases hstep with
    | binary hz => exact ⟨_, _, .op (by simp [Op.exec, hx, hy, hz]) .nil, readAll_set fr d _, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hstep with
    | load hz => exact ⟨_, _, .op (by simp [Op.exec, hx, hz]) .nil, readAll_set fr d _, rfl⟩
  · obtain ⟨x, y, hx, hy, rfl⟩ := readAll_two hr
    cases hstep with
    | store hm => exact ⟨fr, [], .op (by simp [Op.exec, hx, hy, hm]) .nil, rfl, rfl⟩
  · obtain ⟨args, res, heq, rfl, horacle⟩ := Opcode.step_call_iff.mp hstep
    have same : ws = args := packValues_injective heq
    subst same
    have widths : ds.length = res.length := by
      rw [hlen, hsigs c ws m res m' horacle]
      rfl
    obtain ⟨fr', hw⟩ := writeAll_isSome fr widths
    exact ⟨fr', res, .call hr horacle hw .nil, readAll_writeAll hw hn, rfl⟩

/-- **An op's run is its opcode's step**, backwards. -/
theorem op_backward {f : Opcode sigs} {as ds : List ℕ} {o : Op ℕ} (ho : opOf f as ds = some o)
    (hn : ds.Nodup) {fr fr' : Frame ℕ} {ws : List Word} (hr : fr.readAll as = some ws)
    {m m' : Memory} (hexec : Ops.Exec oracle [o] fr m fr' m') :
    ∃ rs, fr'.readAll ds = some rs ∧ Opcode.step oracle f (packValues ws) m (packValues rs) m' := by
  rcases opOf_some ho with ⟨c, d, rfl, rfl, rfl, rfl⟩ | ⟨s, d, rfl, rfl, rfl, rfl⟩ |
      ⟨op, s, d, rfl, rfl, rfl, rfl⟩ | ⟨op, a, b, d, rfl, rfl, rfl, rfl⟩ |
      ⟨w, e, off, b, d, rfl, rfl, rfl, rfl⟩ | ⟨w, off, b, s, rfl, rfl, rfl, rfl⟩ |
      ⟨c, rfl, -, rfl⟩
  · obtain rfl : ws = [] := by simpa using hr.symm
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨rfl, rfl⟩ : fr.set d c = fr' ∧ m = m' := by simpa [Op.exec] using he
      exact ⟨[c], readAll_set fr d c, .const⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨rfl, rfl⟩ : fr.set d x = fr' ∧ m = m' := by simpa [Op.exec, hx] using he
      exact ⟨[x], readAll_set fr d x, .move⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨rfl, rfl⟩ : fr.set d (op.eval x) = fr' ∧ m = m' := by simpa [Op.exec, hx] using he
      exact ⟨_, readAll_set fr d _, .unary⟩
  · obtain ⟨x, y, hx, hy, rfl⟩ := readAll_two hr
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨z, hz, rfl, rfl⟩ : ∃ z, op.eval x y = some z ∧ fr.set d z = fr' ∧ m = m' := by
        simpa [Op.exec, hx, hy] using he
      exact ⟨_, readAll_set fr d _, .binary hz⟩
  · obtain ⟨x, hx, rfl⟩ := readAll_one hr
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨z, hz, rfl, rfl⟩ : ∃ z, m.load w e (x.toNat + off) = some z ∧ fr.set d z = fr' ∧
          m = m' := by
        simpa [Op.exec, hx] using he
      exact ⟨_, readAll_set fr d _, .load hz⟩
  · obtain ⟨x, y, hx, hy, rfl⟩ := readAll_two hr
    cases hexec with
    | op he hrest =>
      cases hrest
      obtain ⟨m₁, hm, rfl, rfl⟩ : ∃ m₁, m.store w (x.toNat + off) y = some m₁ ∧ fr = fr' ∧
          m₁ = m' := by
        simpa [Op.exec, hx, hy] using he
      exact ⟨[], rfl, .store hm⟩
  · cases hexec with
    | op he _ => simp [Op.exec] at he
    | call hvals horacle hw hrest =>
      cases hrest
      obtain rfl : ws = _ := Option.some.inj (hr.symm.trans hvals)
      exact ⟨_, readAll_writeAll hw hn, .call horacle⟩

end Silmaril.Proofs.Machine.OfLambdaSSA
