module

public import Silmaril.Compiler.Core.Verified.PrintfVariadic.Defs
public import Silmaril.Compiler.Core.Verified.PrintfStmt.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The variadic integer argument object

Cerberus passes a variadic `int` through std.core's `create_and_store(ty, x)`.
The procedure allocates a fresh object, stores its argument and returns the
object's pointer. These lemmas use that actual body, preserve earlier objects,
and leave the object live for printf and the caller's later kill.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfArg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Mem.Concrete (intType nextIntAddress)
open PrintfStd PrintfStmt StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-- A create whose alignment and type are read from the same type parameter. -/
def createSym : EExp → Option (Sym × Sym × Prefix)
  | .mk _ (.action (.mk .pos (.mk _ _ (.create
      (.mk _ _ (.ctor .ivAlignof [.mk _ _ (.sym a)])) (.mk _ _ (.sym b)) pref)))) =>
      some (a, b, pref)
  | _ => none

/-- A positive, non-atomic store whose operands are parameters. -/
def storeSym : EExp → Option (Sym × Sym × Sym)
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false (.mk _ _ (.sym ty))
      (.mk _ _ (.sym p)) (.mk _ _ (.sym v)) .na)))) => some (ty, p, v)
  | _ => none

/-- The body of std.core's `create_and_store`, recognized compositionally. -/
def createStoreBody (ty v : Sym) (body : EExp) : Option Unit := do
  let (p, cr, rest) ← wseqOf body
  let (ty₁, ty₂, _) ← createSym cr
  let (st, finish) ← wseqNone rest
  let (ty₃, p₁, v₁) ← storeSym st
  let p₂ ← pureSym finish
  if ty₁.key = ty.key ∧ ty₂.key = ty.key ∧ ty₃.key = ty.key ∧ p₁.key = p.key ∧
      p₂.key = p.key ∧ v₁.key = v.key ∧ distinct [ty, v, p] then some () else none

/-- The helper must be a real std.core procedure and must not dispatch to a builtin. -/
def isCreateStore (file : Fold.Doc) (f : Sym) : Bool :=
  (file.funs.lookup f).isNone &&
    match file.stdlib.lookup f with
    | some (.procedure _ _ _ [(ty, _), (v, _)] body) => distinct [ty, v] && (createStoreBody ty v body).isSome
    | _ => false

theorem createSym_inv {e : EExp} {a b : Sym} {pref : Prefix}
    (h : createSym e = some (a, b, pref)) :
    ∃ ann l u a1 u1 a2 u2 a3 u3, e = .mk ann (.action (.mk .pos (.mk l u (.create
      (.mk a1 u1 (.ctor .ivAlignof [.mk a2 u2 (.sym a)])) (.mk a3 u3 (.sym b)) pref)))) := by
  unfold createSym at h
  split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

theorem storeSym_inv {e : EExp} {ty p v : Sym} (h : storeSym e = some (ty, p, v)) :
    ∃ ann l u a1 u1 a2 u2 a3 u3, e = .mk ann (.action (.mk .pos (.mk l u
      (.store false (.mk a1 u1 (.sym ty)) (.mk a2 u2 (.sym p)) (.mk a3 u3 (.sym v)) .na)))) := by
  unfold storeSym at h
  split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

variable {file : Program} {labels : Labels}

/-- Allocation preserves every earlier object. -/
theorem created_keeps (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    Keeps m (Actions.created pref ann m) := by
  have hw : Keeps m (Mem.Concrete.writeRepresentation (nextIntAddress m)
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m) :=
    (Keeps.refl m).write _ _ (by simp [Mem.Concrete.plainBytes]; unfold nextIntAddress; omega)
  unfold Actions.created
  apply Keeps.updateLast (j := m.nextId) _ rfl (le_refl _)
  refine ⟨hw.enums, ?_, ?_, ?_, hw.dead, hw.bytes, hw.pbytes⟩
  · simp
  · simp only; unfold nextIntAddress; omega
  · intro j hj
    simp only
    rw [Map.lookup_insert_of_key_ne _ _ (show j ≠ m.nextId by omega)]

theorem created_facts (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (Actions.created pref ann m).nextId = m.nextId + 1 ∧
      (Actions.created pref ann m).lastAddress = nextIntAddress m ∧
      (Actions.created pref ann m).dead = m.dead ∧
      (Actions.created pref ann m).stdout = m.stdout := by
  unfold Actions.created
  rw [StrMem.updateLast_of _ _ rfl (Map.lookup_insert _ _ _)]
  simp [wr_stdout,
    (Mem.Concrete.writeRepresentation_allocations _ _ m).2.1]

/-- A variable type operand can instantiate the usual integer allocation proof. -/
theorem create_reaches {e : EExp} {a b : Sym} {pref : Prefix}
    (shape : createSym e = some (a, b, pref)) {env : Env} (cann : List Annot)
    (ha : env.lookup a = some (.ctype (intType cann)))
    (hb : env.lookup b = some (.ctype (intType cann))) (k : List Frame) (m : Mem.Concrete.State)
    (room : 0 < nextIntAddress m) :
    ∃ ann, ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), k,
        Actions.created pref cann (SeqReach.focusMemory ann m)⟩ := by
  obtain ⟨ann, l, u, a1, u1, a2, u2, a3, u3, rfl⟩ := createSym_inv shape
  cases u1; cases u2; cases u3
  have ev : Eval file (tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.sym a)]), .mk a3 () (.sym b)])
      (.inr [.object (.integer 4), .ctype (intType cann)]) :=
    .cons (.ctor (.cons (.sym ha) .nil) (Locals.alignof_int _ cann)) (.cons (.sym hb) .nil)
  refine ⟨ann, (Locals.action_reaches Locals.request_create ev).trans ?_⟩
  simpa only [PrintfStmt.focus_same, nextIntAddress, PrintfStd.focus_lastAddress, PrintfStd.focus_nextId] using
    Actions.create_apply (file := file) (labels := labels) pref cann k (SeqReach.focusMemory ann m)
      (by simpa only [nextIntAddress, PrintfStd.focus_lastAddress] using room)

/-- The generic helper's store initializes its fresh integer object. -/
theorem store_reaches {e : EExp} {ty p v : Sym} (shape : storeSym e = some (ty, p, v))
    {env : Env} (cann : List Annot) {id addr n : Int}
    (ht : env.lookup ty = some (.ctype (intType cann)))
    (hp : env.lookup p = some (.object (.pointer (.allocated id addr))))
    (hv : env.lookup v = some (.loaded (.specified (.integer n))))
    (range : Mem.Concrete.IntRange n) (k : List Frame) {m : Mem.Concrete.State}
    (live : Mem.Concrete.LiveInt m id addr) :
    ∃ ann zs, ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, .annotations zs :: k, Locals.stored (SeqReach.focusMemory ann m) id addr n⟩ := by
  obtain ⟨ann, l, u, a1, u1, a2, u2, a3, u3, rfl⟩ := storeSym_inv shape
  cases u1; cases u2; cases u3
  have ev : Eval file (tagsOf file m) env
      (.inr [.mk a1 () (.sym ty), .mk a2 () (.sym p), .mk a3 () (.sym v)])
      (.inr [.ctype (intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]) := .cons (.sym ht) (.cons (.sym hp) (.cons (.sym hv) .nil))
  obtain ⟨zs, st⟩ := Actions.store_apply (file := file) (labels := labels) cann k
    (Locals.liveInt_focus ann live) range
  exact ⟨ann, zs, (Locals.action_reaches Locals.request_store ev).trans st⟩

/-- The recognized helper body returns a fresh live slot, ready for a variadic
argument list. Its allocation budget is one aligned four-byte object. -/
theorem body_reaches {ty v : Sym} {body : EExp} (shape : createStoreBody ty v body = some ())
    {env : Env} (cann : List Annot) {n : Int}
    (ht : env.lookup ty = some (.ctype (intType cann)))
    (hv : env.lookup v = some (.loaded (.specified (.integer n))))
    (range : Mem.Concrete.IntRange n) (k : List Frame) (m : Mem.Concrete.State)
    (room : 0 < nextIntAddress m) (fresh : m.nextId ∉ m.dead) :
    ∃ m' zs, ReturnConst.Reaches file labels ⟨.effectExpr body env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations zs :: k, m'⟩ ∧
      Locals.Slot m' m.nextId (nextIntAddress m) n ∧ Keeps m m' ∧ m'.stdout = m.stdout ∧
      m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextIntAddress m ∧ m'.dead = m.dead := by
  unfold createStoreBody at shape
  obtain ⟨⟨p, cr, rest⟩, q1, shape⟩ := bind_some shape; try dsimp only at shape
  obtain ⟨⟨ty1, ty2, pref⟩, q2, shape⟩ := bind_some shape; try dsimp only at shape
  obtain ⟨⟨st, finish⟩, q3, shape⟩ := bind_some shape; try dsimp only at shape
  obtain ⟨⟨ty3, p1, v1⟩, q4, shape⟩ := bind_some shape; try dsimp only at shape
  obtain ⟨p2, q5, shape⟩ := bind_some shape
  split at shape
  case isFalse => cases shape
  rename_i cond
  obtain ⟨k1, k2, k3, k4, k5, k6, hd⟩ := cond
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or] at nd
  obtain ⟨⟨ntyv, ntyp⟩, nvp, -⟩ := nd
  obtain ⟨A0, P0, b0, rfl⟩ := wseqOf_inv q1
  obtain ⟨A1, P1, b1, rfl⟩ := wseqNone_inv q3
  obtain ⟨A2, a2, u2, rfl⟩ := pureSym_inv q5
  obtain ⟨ann, crun⟩ := create_reaches (file := file) (labels := labels) q2 cann
    (by rw [ReturnLit.lookup_key k1]; exact ht) (by rw [ReturnLit.lookup_key k2]; exact ht)
    (.effectBind (.mk P0 (.base (some p, b0))) _ env :: k) m room
  let m₁ := Actions.created pref cann (SeqReach.focusMemory ann m)
  have live : Mem.Concrete.LiveInt m₁ m.nextId (nextIntAddress m) := by
    have := Locals.created_live pref cann (SeqReach.focusMemory ann m) (by simpa using fresh)
    simpa only [m₁, PrintfStd.focus_nextId, nextIntAddress, PrintfStd.focus_lastAddress] using this
  obtain ⟨sann, zs, srun⟩ := store_reaches (file := file) (labels := labels) q4 cann
    (by rw [ReturnLit.lookup_key k3, lk_other ntyp]; exact ht)
    (lk_same k4 _ _) (by rw [ReturnLit.lookup_key k6, lk_other nvp]; exact hv) range
    (.effectBind (.mk P1 (.base (none, b1))) _ (extendEnv [(p,
      .object (.pointer (.allocated m.nextId (nextIntAddress m))))] env) :: k) live
  have run := (SeqReach.wseq_reaches A0 crun rfl).trans
    ((ExitCall.lift file labels (ExitCall.ra_wseq file labels A1 _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (srun.trans ((v_effectBind file labels zs (pat := .mk P1 (.base (none, b1))) rfl _ _).trans
      (SeqReach.effect_pure_reaches A2 (SeqReach.pure_symbol a2 p2 _ _ (lk_same k5 _ _)) _ _))))
  have kalloc : Keeps m m₁ := (keeps_focus ann m).trans (created_keeps pref cann _)
  have kstore : Keeps m (Locals.stored (SeqReach.focusMemory sann m₁)
      m.nextId (nextIntAddress m) n) := by
    apply Keeps.lastUsed
    apply Keeps.write (kalloc.trans (keeps_focus sann m₁))
    simp only [Mem.Concrete.plainBytes, List.length_map, Mem.Concrete.encodeInteger_length]
    unfold nextIntAddress
    omega
  have slot := Locals.stored_slot (Locals.liveInt_focus sann live) n
  have facts := created_facts pref cann (SeqReach.focusMemory ann m)
  refine ⟨_, zs, run, Locals.slot_focus A2 slot, kstore.trans (keeps_focus A2 _), ?_, ?_, ?_, ?_⟩
  · simp [Locals.stored, wr_stdout, facts.2.2.2, m₁]
  · simp [Locals.stored, wr_nextId, facts.1, m₁]
  · simp [Locals.stored, wr_lastAddress, facts.2.1, m₁, nextIntAddress]
  · simp [Locals.stored, (Mem.Concrete.writeRepresentation_allocations _ _ _).2.1, facts.2.2.1, m₁]

/-- Dispatch the actual std.core helper with an integer type and value. -/
theorem createStore_reaches {f : Sym} (recognized : isCreateStore file f = true)
    (outer : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot) {n : Int}
    (range : Mem.Concrete.IntRange n) (room : 0 < nextIntAddress m) (fresh : m.nextId ∉ m.dead) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.directProcedure outer) [.loaded (.specified (.pointer (.function f))),
        .ctype (intType cann), .loaded (.specified (.integer n))], k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations zs :: k, m'⟩ ∧
      Locals.Slot m' m.nextId (nextIntAddress m) n ∧ Keeps m m' ∧ m'.stdout = m.stdout ∧
      m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextIntAddress m ∧ m'.dead = m.dead := by
  unfold isCreateStore at recognized
  simp only [Bool.and_eq_true] at recognized
  obtain ⟨hf, hb⟩ := recognized
  have hf' : file.funs.lookup f = none := Option.isNone_iff_eq_none.mp hf
  split at hb
  case h_2 => cases hb
  rename_i loc marker bt ty bty v bval body decl
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hd, hb⟩ := hb
  obtain ⟨u, hb⟩ := Option.isSome_iff_exists.mp hb
  cases u
  have ne : MapKey.key ty ≠ MapKey.key v := by simpa [distinct] using hd
  let E : Env := extendEnv [(ty, .ctype (intType cann)),
    (v, .loaded (.specified (.integer n)))] outer
  have resolved : procedureBody file f [.ctype (intType cann), .loaded (.specified (.integer n))] =
      .ok (body, [(ty, .ctype (intType cann)), (v, .loaded (.specified (.integer n)))]) := by
    rw [CallReach.stdlib_procedure_body decl rfl]; rfl
  have start := CallReach.dispatch_reaches (file := file) (labels := labels) true
    (by simp [libraryCall, hf']) resolved outer k m
  obtain ⟨m', zs, run, slot, keep, out, next, last, dead⟩ := body_reaches
    (file := file) (labels := labels) hb (env := E) cann (by simp [E, extendEnv])
    (by simp [E, extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm ne)]) range
    (.procedureReturn (CallReach.bodyLabels body) :: k) m room fresh
  exact ⟨m', zs, start.trans (run.trans (v_return zs _ _ k m')), slot, keep, out, next, last, dead⟩

end Silmaril.Compile.Core.Verified.PrintfArg
