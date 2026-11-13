module

public import Silmaril.Compiler.Core.Verified.ArrExpr.Defs
public import Silmaril.Compiler.Core.Verified.ArrSyntax.Defs
public import Silmaril.Compiler.Core.Verified.State.Defs
public import Silmaril.Compiler.Core.Verified.StateExitResult.Defs
public import Silmaril.Compiler.Core.Verified.StructObj.Defs
/-! A syntax-directed fragment for one local int array, or one local struct of `int` members
(`StructObj`), with constant indices and member designators.
Element assignments and reads are substituted as pure integer expressions, which
are emitted as runtime arithmetic by `IntExpr.exprOps`. Unsupported shapes reject. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrBlock

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PureEval (Reaches)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open LocalExpr (Shows)
open StateMem (Defined defsOf)
open IntExpr (spec)

/-- Only pure integer expressions are inspected for representability. -/
def okDec (t : IntExpr.Term) (n : Int) : Decidable (t.Ok n) := by
  cases t with
  | lit c => unfold IntExpr.Term.Ok ConvInt.IsInt; exact inferInstance
  | var => unfold IntExpr.Term.Ok ConvInt.IsInt; exact inferInstance
  | bin o a b =>
      letI := okDec a n; letI := okDec b n
      unfold IntExpr.Term.Ok ConvInt.IsInt; exact inferInstance
  | cmp r c d a b =>
      letI := okDec a n; letI := okDec b n
      unfold IntExpr.Term.Ok ConvInt.IsInt; exact inferInstance
  | cond c a b =>
      letI := okDec c n; letI := okDec a n; letI := okDec b n
      simp only [IntExpr.Term.Ok]; exact inferInstance
  | bit o a b =>
      letI := okDec a n; letI := okDec b n
      simp only [IntExpr.Term.Ok]; exact inferInstance
  | divpos o d a => exact okDec a n
termination_by sizeOf t

/-- Executable expression size, excluding erased structural measures. -/
def termSize : IntExpr.Term → Nat
  | .lit _ | .var => 1
  | .bin _ a b | .cmp _ _ _ a b | .bit _ a b => 1 + termSize a + termSize b
  | .cond c a b => 1 + termSize c + termSize a + termSize b
  | .divpos _ _ a => 1 + termSize a

/-- A return expression followed by the array's kill and the main return jump. -/
def ret (file : File Codec.wireModel Unit Unit) (r x : Sym) (N : Nat) (ds : ArrMem.Defs) :
    Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.sseq (.mk _ (.base (none, _))) kl kr))) =>
      if u.key ≠ x.key ∧ StructObj.killAny file x N kl = true ∧ StateStmt.runRet file r u kr = true then
        match ArrExpr.translate file x N ds e with
        | some t => if termSize t ≤ 4096 ∧ @decide (t.Ok 0) (okDec t 0) = true then some t else none
        | none => none
      else none
  | _ => none

/-- `exit(e)` of a closed argument ends the block; the array is never killed. -/
def exitLeaf (file : File Codec.wireModel Unit Unit) (e : Eff) : Option IntExpr.Term :=
  match ExitCall.recognizeBody file e with
  | some n => if @decide ((IntExpr.Term.lit n).Ok 0) (okDec _ 0) = true then some (.lit n) else none
  | none => none

abbrev Pending := List (List Annot × BaseType × Eff)

def frames (env : Env) : Pending → List Frame → List Frame
  | [], k => k
  | (ann, ty, e) :: rest, k =>
      .strongBind (.mk ann (.base (none, ty))) e env :: frames env rest k

def resume (go : ArrMem.Defs → Pending → Eff → Option IntExpr.Term)
    (ds : ArrMem.Defs) : Pending → Option IntExpr.Term
  | [] => none
  | (_, _, e) :: rest => go ds rest e

/-- Bounded syntax traversal, with symbolic definitions for initialized elements. -/
def run (file : File Codec.wireModel Unit Unit) (r x : Sym) (N : Nat) :
    Nat → ArrMem.Defs → Pending → Eff → Option IntExpr.Term
  | 0, _, _, _ => none
  | fuel + 1, ds, pending, e =>
    match ret file r x N ds e with
    | some t => some t
    | none => match exitLeaf file e with
    | some t => some t
    | none => match ArrStmt.assignStmt file e with
      | some ((a, i), t) =>
        if a.key = x.key ∧ 0 ≤ i ∧ i < N ∧ Defined (fun _ => none) t = true ∧
            State.closeSize (fun _ => 0) t ≤ 4096 then
          resume (run file r x N fuel)
            (ArrMem.update ds (x.key, i.toNat) (some (StateExpr.close (defsOf (fun _ => none)) t))) pending
        else none
      | none => match e with
          | .mk _ (.sseq (.mk pann (.base (none, ty))) s rest) =>
              run file r x N fuel ds ((pann, ty, rest) :: pending) s
          | .mk _ (.pure (.mk _ () (.val .unit))) => resume (run file r x N fuel) ds pending
          | _ => none

/-- Exactly one aggregate creation at the start of main. -/
def block (file : File Codec.wireModel Unit Unit) (r : Sym) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr
      (.mk _ (.sseq (.mk _ (.base (none, _))) init rest))) => do
      let N ← StructObj.createAny file cr
      if 0 < N ∧ N ≤ 1048576 ∧ StructObj.uninitAny file x N init = true then
        run file r x N 256 (fun _ => none) [] rest else none
  | _ => none

def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (r, _) [(u, _)] (.mk _ (.pure (.mk _ () (.sym u'))))))) =>
      if u'.key = u.key ∧ StmtIf.labelFree a = true then block file r a else none
  | _ => none

def recognize (doc : Codec.Document) : Option IntExpr.Term := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

variable {file : Program} {labels : Labels}

theorem ret_halts {r x : Sym} {N : Nat} {ds : ArrMem.Defs} {e : Eff} {t : IntExpr.Term}
    (hret : ReturnLabel labels r) (h : ret file r x N ds e = some t)
    {env : Env} {a : ArrMem.Array} (key : a.object.sym.key = x.key) (len : a.length = N)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State) (hm : ArrExpr.Holds env a ds m) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold ret at h
  split at h
  · rename_i ann pann u ty bann e' sann kpann kty kl kr
    split at h
    · rename_i hc
      obtain ⟨fresh, hkl, hkr⟩ := hc
      split at h
      · rename_i t' ht
        split at h
        · rename_i safe
          cases h
          have ok : t.Ok 0 := @of_decide_eq_true (t.Ok 0) (okDec t 0) safe.2
          let REST : Eff := .mk sann (.sseq (.mk kpann (.base (none, kty))) kl kr)
          let K := Frame.strongBind (.mk pann (.base (some u, ty))) REST env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) REST)) env, k, m⟩
              ⟨.effectExpr e' env, .bound :: K, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          have runs := (ArrExpr.translate_spec ht).runs (labels := labels) (env := env) key len ok
          obtain ⟨xs, m₁, fr, hfr, -, tch, run⟩ := runs.2 (.bound :: K) m hm
          let v := spec (t.val 0)
          let env₂ := extendEnv [(u, v)] env
          have hx : ∀ y : Sym, y.key = x.key → env₂.lookup y = some (StateMem.ptr a.object) := by
            intro y hy
            rw [ConvInt.lookup_one_other (by rw [hy]; exact fresh.symm)]
            exact hm.2 a (by simp) y (hy.trans key.symm)
          have live : ArrDesig.Arr m₁ a.object.id a.object.addr N := by
            rw [← len]; exact (hm.1.touched tch).live a (by simp)
          let KK := Frame.strongBind (.mk kpann (.base (none, kty))) kr env₂ :: k
          obtain ⟨kann, kill⟩ := StructObj.killAny_runs hkl env₂ KK m₁ hx live
          let m₂ := Locals.killed (ReturnConst.focusMemory kann m₁) a.object.id
          obtain ⟨m₃, out, done⟩ := StateStmt.killsRun_halts hret [] [] rfl (by simp)
            hkr env₂ hk m₂ (by simp) (by simp) (by simp)
            (IntExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
          left
          refine ⟨ok, m₃, ?_, pre.trans ((Interleave.reaches_of_local file labels run).trans
            ((StateStmt.bound_pop hfr v K m₁).trans
              ((ReturnLit.bind_reaches pann u ty v REST env k m₁).trans
                ((ReturnConst.sequence_reaches file labels sann _ kl kr env₂ k m₁).trans
                  (kill.trans ((ReturnConst.wildcard_sequence_reaches file labels kpann kty .unit kr env₂ k m₂).trans done))))))⟩
          simpa [m₂, Locals.killed, tch.stdout] using out
        · cases h
      · cases h
    · cases h
  · cases h

theorem exitLeaf_halts {e : Eff} {t : IntExpr.Term} (h : exitLeaf file e = some t)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hb : ExitCall.Budget m) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold exitLeaf at h
  split at h
  · rename_i n hn
    split at h
    · rename_i ok
      cases h
      obtain ⟨m', run, out⟩ := StateExit.exit_reaches (file := file) (labels := labels) e hn env k m hb
      exact .inl ⟨@of_decide_eq_true _ (okDec _ 0) ok, m', out, by simpa [IntExpr.Term.val] using run⟩
    · cases h
  · cases h

theorem frames_boundary (env : Env) (pending : Pending) {k : List Frame} (hk : NoBoundary k) :
    NoBoundary (frames env pending k) := by
  induction pending with
  | nil => exact hk
  | cons p rest ih => exact noBoundary_cons ih trivial

theorem run_halts {r x : Sym} {N : Nat} {env : Env} {a : ArrMem.Array} {k : List Frame}
    (key : a.object.sym.key = x.key) (len : a.length = N)
    (hret : ReturnLabel labels r) (hk : NoBoundary k) (fuel : Nat)
    {ds : ArrMem.Defs} {pending : Pending} {e : Eff} {t : IntExpr.Term}
    (h : run file r x N fuel ds pending e = some t) (m : Mem.Concrete.State)
    (hm : ArrExpr.Holds env a ds m) (hb : ExitCall.Budget m) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, frames env pending k, m⟩ 0 t m.stdout := by
  induction fuel generalizing ds pending e t m with
  | zero => cases h
  | succ fuel ih =>
    have next {ads : ArrMem.Defs} (hnext : resume (run file r x N fuel) ads pending = some t)
        (m' : Mem.Concrete.State) (hm' : ArrExpr.Holds env a ads m') (hb' : ExitCall.Budget m') :
        Shows (file := file) (labels := labels) ⟨.value .unit, frames env pending k, m'⟩ 0 t m'.stdout := by
      cases pending with
      | nil => cases hnext
      | cons p rest =>
        obtain ⟨ann, ty, e'⟩ := p
        exact Shows.pre (ReturnConst.wildcard_sequence_reaches file labels ann ty .unit e' env
          (frames env rest k) m') (ih hnext m' hm' hb')
    unfold run at h
    split at h
    · rename_i t' ht
      cases h
      exact ret_halts hret ht key len (frames_boundary env pending hk) m hm
    · split at h
      · rename_i t' ht
        cases h
        exact exitLeaf_halts ht env _ m hb
      · split at h
        · rename_i a' i rhs ha
          split at h
          · rename_i hc
            obtain ⟨ka, lo, hi, hd, _⟩ := hc
            have ni : (i.toNat : Int) = i := Int.toNat_of_nonneg lo
            have ai := hm.1
            have ae := hm.2
            rcases ArrStmt.assign_runs (file := file) (labels := labels)
                (i := i.toNat) (by rwa [ni]) (ArrExpr.scalarEmpty env m) ai ae
                (by constructor <;> simp) (a := a) (by simp) (ka.trans key.symm)
                (by omega) hd (frames env pending k) (by simp [StateMem.PEnv]) with
              ub | ⟨_, m', out, _, ai', reach, fl, fn, fd⟩
            · exact .inr ub
            · have hm' : ArrExpr.Holds env a
                  (ArrMem.update ds (x.key, i.toNat) (some (StateExpr.close (defsOf (fun _ => none)) rhs))) m' :=
                ⟨by simpa [key] using ai', ae⟩
              have hb' : ExitCall.Budget m' := by
                refine ⟨?_, ?_⟩
                · have room := hb.room
                  unfold Mem.Concrete.nextIntAddress at room ⊢
                  rw [fl]; exact room
                · rw [fn, fd]; exact hb.fresh
              have o := next h m' hm' hb'
              rw [out] at o
              exact Shows.pre reach o
          · cases h
        · split at h
          · rename_i ann pann ty s rest _ _ _
            exact Shows.pre (ReturnConst.sequence_reaches file labels ann _ s rest env
              (frames env pending k) m) (ih h m hm hb)
          · rename_i ann pann _ _ _
            let m' := ReturnConst.focusMemory ann m
            have hm' : ArrExpr.Holds env a ds m' := hm.touched (StateStmt.seqFocus_touched ann m)
            have o := next h m' hm' (hb.focus ann)
            have out : m'.stdout = m.stdout := by simp [m']
            rw [out] at o
            exact Shows.pre (StateStmt.pure_unit_reaches ann pann env (frames env pending k) m) o
          · cases h

theorem singletonInv {m : Mem.Concrete.State} (a : ArrMem.Array)
    (live : ArrDesig.Arr m a.object.id a.object.addr a.length) (aligned : a.object.addr % 4 = 0) :
    ArrMem.Inv m [a] (fun _ => none) := by
  constructor
  · intro b hb; simpa only [List.mem_singleton.mp hb] using live
  · intro b hb; simpa only [List.mem_singleton.mp hb] using aligned
  · intro b hb c hc _; exact (List.mem_singleton.mp hb).trans (List.mem_singleton.mp hc).symm
  · intro b hb c hc ne
    exact False.elim (ne ((congrArg (fun a : ArrMem.Array => a.object.sym.key)
      ((List.mem_singleton.mp hb).trans (List.mem_singleton.mp hc).symm))))
  · intro q d hd; cases hd

theorem block_halts {r : Sym} (hret : ReturnLabel labels r) {e : Eff} {t : IntExpr.Term}
    (h : block file r e = some t) (env : Env) (m : Mem.Concrete.State)
    (last : m.lastAddress = StartupReach.errnoAddr) (dead : m.dead = [])
    {k : List Frame} (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold block at h
  split at h
  · rename_i a0 a1 x ty cr b0 b1 ty1 init rest
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨N, hcr, h⟩ := h
    split at h
    · rename_i hc
      obtain ⟨pos, upper, hu⟩ := hc
      have hpos : 0 < ArrDesig.arrAddr m N := by
        unfold ArrDesig.arrAddr
        rw [last]
        simp only [StartupReach.errnoAddr]
        omega
      let REST : Eff := .mk b0 (.sseq (.mk b1 (.base (none, ty1))) init rest)
      let K := Frame.strongBind (.mk a1 (.base (some x, ty))) REST env :: k
      obtain ⟨m₁, create, made⟩ := StructObj.createAny_reaches (file := file) (labels := labels)
        hcr env K m hpos (by rw [dead]; simp)
      let a : ArrMem.Array := ⟨⟨x, m.nextId, ArrDesig.arrAddr m N⟩, N⟩
      let env₁ := extendEnv [(x, StateMem.ptr a.object)] env
      have live : ArrDesig.Arr m₁ a.object.id a.object.addr N := made.arr
      have lookup : ∀ y : Sym, y.key = x.key → env₁.lookup y = some (StateMem.ptr a.object) :=
        fun y hy => ConvInt.lookup_one hy
      let KI := Frame.strongBind (.mk b1 (.base (none, ty1))) rest env₁ :: k
      obtain ⟨iann, xs, initRun⟩ := StructObj.uninitAny_runs hu env₁ KI m₁ lookup live
      let m₂ := ArrInit.stored (ReturnConst.focusMemory iann m₁) a.object.id a.object.addr N
      have live₂ : ArrDesig.Arr m₂ a.object.id a.object.addr N :=
        ArrInit.arr_stored (live.touched (StateStmt.seqFocus_touched iann m₁)) _ _ _
      have inv : ArrExpr.Holds env₁ a (fun _ => none) m₂ := by
        refine ⟨singletonInv a live₂ (ArrLife.arrAddr_bounds m N).2, ?_⟩
        intro b hb y hy
        obtain rfl := List.mem_singleton.mp hb
        exact lookup y hy
      have out : m₂.stdout = m.stdout := by
        simp [m₂, ArrInit.stored, Actions.writeRepresentation_stdout, made.stdout]
      have fields : m₂.lastAddress = ArrDesig.arrAddr m N ∧ m₂.nextId = m.nextId + 1 ∧
          m₂.dead = m.dead := by
        refine ⟨?_, ?_, ?_⟩ <;> simp only [m₂, ArrInit.stored, StructObj.wr_lastAddress,
          StructObj.wr_nextId, Locals.writeRepresentation_dead, State.focus_lastAddress,
          State.focus_nextId, State.focus_dead, made.lastAddress, made.nextId, made.dead]
      have hb : ExitCall.Budget m₂ := by
        refine ⟨?_, ?_⟩
        · unfold Mem.Concrete.nextIntAddress
          rw [fields.1]
          unfold ArrDesig.arrAddr
          rw [last]
          simp only [StartupReach.errnoAddr]
          omega
        · rw [fields.2.1, fields.2.2, dead]; simp
      have o := run_halts (file := file) (labels := labels) (a := a) rfl rfl hret
        (k := .annotations xs :: k) (noBoundary_cons hk trivial) 256 h m₂ inv hb
      rw [out] at o
      exact Shows.pre ((ReturnConst.sequence_reaches file labels a0 _ cr REST env k m).trans
        (create.trans ((ReturnLit.bind_reaches a1 x ty (StateMem.ptr a.object) REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels b0 _ init rest env₁ k m₁).trans
            (initRun.trans (Locals.annotations_bind_reaches xs b1 ty1 .unit rest env₁ k m₂)))))) o
    · cases h
  · cases h

theorem recognize_reaches (doc : Codec.Document) (t : IntExpr.Term) (h : recognize doc = some t)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 t "" := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  cases main : doc.file.main with
  | none => simp [main] at h
  | some sym =>
    cases decl : doc.file.funs.lookup sym with
    | none => simp [main, decl] at h
    | some entry =>
      cases entry <;> try { simp [main, decl] at h }
      case procedure loc marker ty ps body =>
        cases ps with
        | cons p ps => simp [main, decl] at h
        | nil =>
          have hbody : recognizeBody doc.file body = some t := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]
                refine ⟨r, bann, pann', r', hr, ?_⟩
                simp [saves, StmtIf.labelFree_saves a hfree, Map.ofList]
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              have o := block_halts hret hbody ∅ m hlast hdead
                (k := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs])
                (by simp [NoBoundary, hasBoundary])
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`t.val 0 mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (t : IntExpr.Term) (h : recognize doc = some t)
    (args : List String) :
    Spec.CoreUB doc args ∨ t.Ok 0 ∧ Spec.CoreBeh doc args (.exit (t.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc t h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (t.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.ArrBlock
