module

public import Silmaril.Compiler.Core.Verified.TyStmt.Defs
public import Silmaril.Compiler.Core.Verified.TyLir.Defs
public import Silmaril.Compiler.Core.Verified.State.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # `main` as a block of typed integer locals and statements

`State` for locals of every supported integer type (`TyActions.supported`: plain, `signed` and
`unsigned` `char`, `short`, `int`, `long`, `long long`). `recognize doc = some R`: `main` is a
procedure without parameters, the file has no global definitions, and `main`'s body is a block
whose locals are created first (`create(Ivalignof(T), T)`, any number, distinct keys), followed
by a sequence of the statements of `TyStmt`: `T x;`, `T x = e;`, `x = e;`, `if (c) return e;`
and `return e;`, every expression over literals and reads of locals already initialised
(`TyExpr.term`, at the locals' types).

`R` (`Res`) is a closed result: `return e` gives the closed term of `e` converted to the return
type, and `if (c) return e; rest` the runtime selection `sel c e rest` (its test a comparison,
`0` or `1`). Each assignment replaces the local's definition by the closed term of its right-hand
side converted to the local's type. The Lir code (`Res.ops`) computes `R` at run time; nothing is
folded. A size bound on the closed terms keeps repeated self-assignments from blowing up.

`recognize_sound`: Core reaches undefined behaviour (a signed operator leaves its type) or exits
with `R.val mod 256` and no output, for every argument list.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyState

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Machine
open Mem.Concrete (LiveSz tyType nextAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open TyActions (supported width signed Fits)
open TyExpr (Key Term term zero values close)
open TyMem (Local Inv Fresh Defined defsOf update ptr)
open TyStmt (Vars isLocal isFresh typedIn assignStmt initStmt uninitStmt retStmt ifRet Keys Shows
  convT)
open IntExpr (spec overflow)

/-! ## Results -/

/-- A closed result: a returned term, or the selection `sel c a r` (`a` when `c ≠ 1`, `r`
otherwise). -/
inductive Res where
  | ret (t : Term)
  | sel (c a : Term) (r : Res)

/-- The returned value. -/
def Res.val : Res → Int
  | .ret t => t.val zero
  | .sel c a r => if c.val zero = 1 then r.val else a.val zero

/-- A comparison with results `0` and `1`. -/
def Term.bool01 : Term → Bool
  | .bin (.cmp _ _ c₁ c₂) _ _ | .ebin (.cmp _ _ c₁ c₂) _ _ =>
      (c₁ == 0 || c₁ == 1) && (c₂ == 0 || c₂ == 1)
  | _ => false

theorem Term.bool01_val {t : Term} (h : Term.bool01 t = true) (σ : Key → Int) :
    t.val σ = 0 ∨ t.val σ = 1 := by
  match t, h with
  | .bin (.cmp ity r c₁ c₂) a b, h =>
    simp only [Term.bool01, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Term.val, TyGuard.G.val]
    split <;> omega
  | .ebin (.cmp ity r c₁ c₂) a b, h =>
    simp only [Term.bool01, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Term.val, TyGuard.G.val]
    split <;> omega

/-- The guards are those of the recogniser (checked). -/
def gwf : TyGuard.G → Bool
  | .arith ity op | .wrap ity op => supported ity && Guard.arith op
  | .cmp ity r _ _ => supported ity && Guard.rel r
  | .bit ity _ => supported ity

def Term.wf : Term → Bool
  | .lit _ | .var _ _ => true
  | .bin g a b => gwf g && Term.wf a && Term.wf b
  | .ebin g a b => gwf g && Term.wf a && Term.wf b
  | .un g a => gwf g && Term.wf a

def Res.wf : Res → Bool
  | .ret t => Term.wf t
  | .sel c a r => Term.wf c && Term.wf a && Res.wf r && Term.bool01 c

theorem Term.wf_spec : (t : Term) → Term.wf t = true → t.Wf
  | .lit _, _ => trivial
  | .var _ _, _ => trivial
  | .bin g a b, h => by
    simp only [Term.wf, Bool.and_eq_true] at h
    obtain ⟨⟨hg, ha⟩, hb⟩ := h
    refine ⟨?_, Term.wf_spec a ha, Term.wf_spec b hb⟩
    cases g <;> simp only [gwf, Bool.and_eq_true] at hg <;> exact hg
  | .ebin g a b, h => by
    simp only [Term.wf, Bool.and_eq_true] at h
    obtain ⟨⟨hg, ha⟩, hb⟩ := h
    refine ⟨?_, Term.wf_spec a ha, Term.wf_spec b hb⟩
    cases g <;> simp only [gwf, Bool.and_eq_true] at hg <;> exact hg
  | .un g a, h => by
    simp only [Term.wf, Bool.and_eq_true] at h
    obtain ⟨hg, ha⟩ := h
    refine ⟨?_, Term.wf_spec a ha⟩
    cases g <;> simp only [gwf, Bool.and_eq_true] at hg <;> exact hg

/-- The code of `R` into register `d`, the temporaries above. -/
def Res.ops (d : Mir.Reg) : Res → List (Lir.Op Mir.Reg)
  | .ret t => t.ops d
  | .sel c a r => c.ops d ++ a.ops (d + 1) ++ r.ops (d + 2) ++
      [.const (d + 3) (BitVec.ofInt 64 1), .binary (.cmp .eq) d d (d + 3),
        .binary .sub (d + 2) (d + 2) (d + 1), .binary .mul d d (d + 2), .binary .add d d (d + 1)]

theorem ofInt_eq_one {v : Int} (h : v = 0 ∨ v = 1) :
    (BitVec.ofInt 64 v == BitVec.ofInt 64 1) = decide (v = 1) := by
  rcases h with rfl | rfl <;> decide

theorem Res.ops_exec : (R : Res) → Res.wf R = true → (d : Nat) → (fr : Lir.Frame Mir.Reg) →
    (mem : Lir.Memory) → ∃ fr', Lir.execOps (R.ops d) fr mem = some (fr', mem) ∧
      fr'.get d = some (BitVec.ofInt 64 R.val) ∧ ∀ r : Nat, r < d → fr'.get r = fr.get r
  | .ret t, h, d, fr, mem => TyLir.ops_exec t (Term.wf_spec t h) d fr mem
  | .sel c a r, h, d, fr, mem => by
    simp only [Res.wf, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, ha⟩, hr⟩, hb⟩ := h
    obtain ⟨fr₁, x₁, g₁, p₁⟩ := TyLir.ops_exec c (Term.wf_spec c hc) d fr mem
    obtain ⟨fr₂, x₂, g₂, p₂⟩ := TyLir.ops_exec a (Term.wf_spec a ha) (d + 1) fr₁ mem
    obtain ⟨fr₃, x₃, g₃, p₃⟩ := Res.ops_exec r hr (d + 2) fr₂ mem
    have gc : fr₃.get d = some (BitVec.ofInt 64 (c.val zero)) := by
      rw [p₃ d (by omega), p₂ d (by omega)]; exact g₁
    have ga : fr₃.get (d + 1) = some (BitVec.ofInt 64 (a.val zero)) := by
      rw [p₃ (d + 1) (by omega)]; exact g₂
    let f := Lir.ofBool (BitVec.ofInt 64 (c.val zero) == BitVec.ofInt 64 1)
    let wa := BitVec.ofInt 64 (a.val zero)
    let wr := BitVec.ofInt 64 r.val
    refine ⟨(((((fr₃.set (d + 3) (BitVec.ofInt 64 1)).set d f).set (d + 2) (wr - wa)).set d
      (f * (wr - wa))).set d (f * (wr - wa) + wa)), ?_, ?_, fun x hx => ?_⟩
    · simp only [Res.ops, Lir.execOps_append, x₁, Option.bind_some, x₂, x₃]
      simp [Lir.execOps, Lir.Op.exec, gc, ga, g₃, Lir.Binop.eval, Lir.Cond.eval, f, wa, wr]
    · simp only [Lir.Frame.get_set, ↓reduceIte, f, IntExpr.select_cond, ofInt_eq_one
        (Term.bool01_val hb zero), Res.val]
      by_cases h1 : c.val zero = 1 <;> simp [h1, wa, wr]
    · rw [IntExpr.get_below hx, IntExpr.get_below hx, IntExpr.get_below (show x < d + 2 by omega),
        IntExpr.get_below hx, IntExpr.get_below (show x < d + 3 by omega), p₃ x (by omega),
        p₂ x (by omega), p₁ x hx]

/-! ## Statements -/

/-- The statements. -/
inductive Stmt where
  | ret (t : Term)
  | ifRet (c a : Term)
  | assign (x : Sym) (ity : IntegerType) (t : Term)
  | init (x : Sym) (ity : IntegerType) (t : Term)
  | uninit (x : Sym) (ity : IntegerType)

/-- Which statement `s` is. -/
def classify (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) (s : Eff) :
    Option Stmt :=
  match retStmt file ret xs s with
  | some t => some (.ret t)
  | none => match ifRet file ret xs s with
    | some (c, a) => some (.ifRet c a)
    | none => match assignStmt file s with
      | some (x, ity, t) => some (.assign x ity t)
      | none => match initStmt file s with
        | some (x, ity, t) => some (.init x ity t)
        | none => (uninitStmt s).map fun (x, ity) => .uninit x ity

/-- What the classification of `s` says about `s`. -/
def Shape (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) (s : Eff) : Stmt → Prop
  | .ret t => retStmt file ret xs s = some t
  | .ifRet c a => ifRet file ret xs s = some (c, a)
  | .assign x ity t => assignStmt file s = some (x, ity, t)
  | .init x ity t => initStmt file s = some (x, ity, t)
  | .uninit x ity => uninitStmt s = some (x, ity)

theorem classify_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : Vars} {s : Eff}
    {st : Stmt} (h : classify file ret xs s = some st) : Shape file ret xs s st := by
  unfold classify at h
  split at h
  next t ht => cases h; exact ht
  next =>
    split at h
    next c a hc => cases h; exact hc
    next =>
      split at h
      next x ity t hx => cases h; exact hx
      next =>
        split at h
        next x ity t hx => cases h; exact hx
        next =>
          cases hu : uninitStmt s with
          | none => simp [hu] at h
          | some p =>
            obtain ⟨x, ity⟩ := p
            simp only [hu, Option.map_some, Option.some.injEq] at h
            subst h
            exact hu

/-- The size of the closed term of `t`, `sz q` the size of the definition of `q`. -/
def closeSize (sz : Key → Nat) : Term → Nat
  | .lit _ => 1
  | .var q _ => sz q
  | .bin _ a b => 1 + closeSize sz a + closeSize sz b
  | .ebin _ a b => 1 + closeSize sz a + closeSize sz b
  | .un _ a => 2 + closeSize sz a

/-- The largest closed term the fragment emits. -/
def maxSize : Nat := 4096

/-- The statements of a block with the locals `xs`, the definitions `ds` (sizes `sz`). -/
def stmts (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) :
    (Key → Option Term) → (Key → Nat) → Eff → Option Res
  | ds, sz, .mk _ (.sseq (.mk _ (.base (none, _))) s rest) =>
    match classify file ret xs s with
    | some (.ret t) =>
      if Defined ds t = true ∧ typedIn xs t = true ∧ closeSize sz t ≤ maxSize then
        some (.ret (close (defsOf ds) t))
      else none
    | some (.ifRet c a) =>
      if Defined ds c = true ∧ Defined ds a = true ∧ typedIn xs c = true ∧ typedIn xs a = true ∧
          closeSize sz c ≤ maxSize ∧ closeSize sz a ≤ maxSize then
        (stmts file ret xs ds sz rest).map (.sel (close (defsOf ds) c) (close (defsOf ds) a))
      else none
    | some (.assign x ity t) =>
      if isLocal xs x ity = true ∧ Defined ds t = true ∧ typedIn xs t = true ∧
          closeSize sz t ≤ maxSize then
        stmts file ret xs (update ds x.key (some (close (defsOf ds) (convT ity t))))
          (fun q => if q = x.key then closeSize sz t + 2 else sz q) rest
      else none
    | some (.init x ity t) =>
      if isLocal xs x ity = true ∧ Defined ds t = true ∧ typedIn xs t = true ∧
          closeSize sz t ≤ maxSize then
        stmts file ret xs (update ds x.key (some (close (defsOf ds) (convT ity t))))
          (fun q => if q = x.key then closeSize sz t + 2 else sz q) rest
      else none
    | some (.uninit x ity) =>
      if isLocal xs x ity = true then stmts file ret xs (update ds x.key none) sz rest else none
    | none => none
  | _, _, _ => none
termination_by _ _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- `create(Ivalignof(T), T)` of a supported type: `T`. -/
def createTy : Eff → Option IntegerType
  | .mk _ (.action (.mk .pos (.mk _ _ (.create
      (.mk _ () (.ctor .ivAlignof [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity)))))]))
      (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity')))))) _)))) =>
      if ity' = ity ∧ supported ity = true then some ity else none
  | _ => none

/-- The block: the creations of its locals, then its statements. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) : Vars → Eff → Option Res
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    match createTy cr with
    | some ity =>
      if isFresh xs x = true ∧ xs.length < 1024 then block file ret (xs ++ [(x, ity)]) rest
      else none
    | none => none
  | xs, e =>
    if (xs.map (·.1.key)).Nodup then stmts file ret xs (fun _ => none) (fun _ => 0) e else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Res
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then block file ret [] a else none
  | _ => none

/-- `main` is a block of typed integer locals and statements. -/
def recognizeRes (doc : Codec.Document) : Option Res := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- `recognizeRes`, with the guards and tests the Lir code needs (checked). -/
def recognize (doc : Codec.Document) : Option Res :=
  match recognizeRes doc with
  | some R => if Res.wf R = true then some R else none
  | none => none

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem update_key {ds : Key → Option Term} {x : Sym} {l : Local} (hx : x.key = l.sym.key)
    (d : Option Term) : update ds x.key d = update ds l.sym.key d := by rw [hx]

theorem shows_sel_left {s : State} {C A : Term} {R : Res} {out : String}
    (h1 : C.val zero ≠ 1) (o : Shows (file := file) (labels := labels) s (A.val zero) out) :
    Shows (file := file) (labels := labels) s (Res.sel C A R).val out := by
  simpa [Res.val, h1] using o

theorem shows_sel_right {s : State} {C A : Term} {R : Res} {out : String}
    (h1 : C.val zero = 1) (o : Shows (file := file) (labels := labels) s R.val out) :
    Shows (file := file) (labels := labels) s (Res.sel C A R).val out := by
  simpa [Res.val, h1] using o

/-- **The statements** show the value of the closed result, or undefined behaviour. -/
theorem stmts_halts {ret : Sym} (hret : ReturnLabel labels ret) {xs : Vars}
    (nodup : (xs.map (·.1.key)).Nodup) (ds : Key → Option Term) (sz : Key → Nat) (e : Eff)
    {R : Res} (h : stmts file ret xs ds sz e = some R) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls ds) (hls : Keys ls xs) (k : List Frame) (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ R.val m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : NoBoundary K := noBoundary_cons hk trivial
    have pre : Reaches file labels ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (none, ty))) s rest))
        env, k, m⟩ ⟨.effectExpr s env, K, m⟩ :=
      ReturnConst.sequence_reaches file labels ann _ s rest env k m
    refine TyStmt.Shows.pre pre ?_
    split at h
    next t hc =>
      split at h
      next hd =>
        cases h
        exact TyStmt.ret_halts hret (classify_spec hc) inv hls nodup hd.1 hd.2.1 hK
      next => cases h
    next c a hc =>
      split at h
      next hd =>
        obtain ⟨hdc, hda, htc, hta, -, -⟩ := hd
        cases hr : stmts file ret xs ds sz rest with
        | none => simp [hr] at h
        | some Rr =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          rcases TyStmt.ifRet_runs hret (classify_spec hc) inv hls nodup hdc htc hda hta hK with
            ub | ⟨h1, o⟩ | ⟨h1, m', out, inv', reach⟩
          · exact .inr ub
          · exact shows_sel_left (by rw [TyExpr.close_val]; exact h1) o
          · have o := stmts_halts hret nodup ds sz rest hr env m' ls inv' hls k hk
            rw [out] at o
            exact shows_sel_right (by rw [TyExpr.close_val]; exact h1)
              (TyStmt.Shows.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
                .unit rest env k m')) o)
      next => cases h
    next x ity t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd.1
        rw [update_key hx] at h
        rcases TyStmt.assign_runs (classify_spec hc) inv hl hx hty hd.2.1 (hls.typed hd.2.2.1) K with
          ub | ⟨m', out, -, inv', reach⟩
        · exact .inr ub
        · have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls k hk
          rw [out] at o
          exact TyStmt.Shows.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
            .unit rest env k m')) o
      next => cases h
    next x ity t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd.1
        rw [update_key hx] at h
        rcases TyStmt.init_runs (classify_spec hc) inv hl hx hty hd.2.1 (hls.typed hd.2.2.1) K with
          ub | ⟨m', ys, out, -, inv', reach⟩
        · exact .inr ub
        · have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
            (noBoundary_cons hk trivial)
          rw [out] at o
          exact TyStmt.Shows.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest
            env k m')) o
      next => cases h
    next x ity hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx, hty⟩ := hls.mem_of_local hd
        rw [update_key hx] at h
        obtain ⟨m', ys, out, -, inv', reach⟩ := TyStmt.uninit_runs (classify_spec hc) inv hl hx hty K
        have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
          (noBoundary_cons hk trivial)
        rw [out] at o
        exact TyStmt.Shows.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest
          env k m')) o
      next => cases h
    next => cases h
  next => cases h
termination_by sizeOf e

theorem createTy_inv {e : Eff} {ity : IntegerType} (h : createTy e = some ity) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (a1 a2 c1 a3 c2 : List Annot) (pref : Prefix),
      e = .mk ann (.action (.mk .pos (.mk l u
        (.create (.mk a1 () (.ctor .ivAlignof [TyActions.tyVal a2 c1 ity])) (TyActions.tyVal a3 c2 ity)
          pref)))) ∧ supported ity = true := by
  unfold createTy at h
  split at h
  · split at h
    · rename_i hc
      cases h
      obtain ⟨rfl, hs⟩ := hc
      exact ⟨_, _, _, _, _, _, _, _, _, rfl, hs⟩
    · cases h
  · cases h

theorem errno_large : (16 * 1025 : Int) < StartupReach.errnoAddr := by
  simp [StartupReach.errnoAddr]

/-- **The block**: creating its locals keeps `Fresh` and `Inv`, then its statements show. -/
theorem block_halts {ret : Sym} (hret : ReturnLabel labels ret) (xs : Vars) (e : Eff)
    {R : Res} (h : block file ret xs e = some R) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls (fun _ => none)) (hls : Keys ls xs) (fresh : Fresh m ls)
    (k : List Frame) (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ R.val m.stdout := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next ity hcr =>
      split at h
      next hc =>
        obtain ⟨hfx, hlt⟩ := hc
        obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl, hs⟩ := createTy_inv hcr
        have hw := TyActions.width_pos hs
        have hw8 := TyActions.width_le hs
        have hge := TyActions.nextAddress_ge m hw
        have hle := TyActions.nextAddress_le m hw
        have hlast := fresh.last
        have herr := errno_large
        have hpos : 0 < nextAddress m (width ity) := by
          rw [hlen] at hlast
          have : (xs.length : Int) < 1024 := by exact_mod_cast hlt
          omega
        let REST := rest
        let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
        have create := TyActions.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
          pref hs env K m hpos
        let nl : Local := ⟨x, m.nextId, nextAddress m (width ity), ity⟩
        let m₁ := TyActions.created pref c2 ity (focusMemory ann m)
        let env₁ := extendEnv [(x, ptr nl)] env
        have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
        have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
        have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
        have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
        have nfocus : (focusMemory ann m).nextId = m.nextId := TyActions.focus_nextId ann m
        have afocus : nextAddress (focusMemory ann m) (width ity) = nextAddress m (width ity) :=
          TyActions.nextAddress_focus ann m _
        have inv₁ : Inv env₁ m₁ (ls ++ [nl]) (fun _ => none) := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro l hl y hy
            rcases List.mem_append.mp hl with hl | hl
            · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
              exact inv.env l hl y hy
            · obtain rfl := List.mem_singleton.mp hl
              exact ConvInt.lookup_one hy
          · intro l hl
            rcases List.mem_append.mp hl with hl | hl
            · refine ⟨(inv.live l hl).1, TyActions.live_created
                (TyActions.liveSz_focus ann (inv.live l hl).2) pref c2 ity ?_⟩
              rw [nfocus]; exact Int.ne_of_lt (ids l hl)
            · obtain rfl := List.mem_singleton.mp hl
              refine ⟨hs, ?_⟩
              have := TyActions.created_live pref c2 ity (focusMemory ann m)
                (by rw [TyActions.focus_dead, fresh.dead, nfocus]; simp)
              rwa [afocus, nfocus] at this
          · intro a ha b hb e
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.uniq a ha b hb e
            · obtain rfl := List.mem_singleton.mp hb
              exact absurd e (fx a ha)
            · obtain rfl := List.mem_singleton.mp ha
              exact absurd e.symm (fx b hb)
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              rfl
          · intro a ha b hb ne
            rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
            · exact inv.apart a ha b hb ne
            · obtain rfl := List.mem_singleton.mp hb
              refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
              have := addrs a ha
              show a.addr + width a.ity ≤ nextAddress m (width ity) ∨
                nextAddress m (width ity) + width ity ≤ a.addr
              omega
            · obtain rfl := List.mem_singleton.mp ha
              refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
              have := addrs b hb
              show nextAddress m (width ity) + width ity ≤ b.addr ∨
                b.addr + width b.ity ≤ nextAddress m (width ity)
              omega
            · obtain rfl := List.mem_singleton.mp ha
              obtain rfl := List.mem_singleton.mp hb
              exact absurd rfl ne
          · intro q d hd; cases hd
        have hls₁ : Keys (ls ++ [nl]) (xs ++ [(x, ity)]) := by
          simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
          rw [hls]
        have last₁ : m₁.lastAddress = nextAddress m (width ity) := by
          rw [TyActions.created_lastAddress, afocus]
        have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [TyActions.created_dead, TyActions.focus_dead, fresh.dead]
          · intro l hl
            rw [TyActions.created_nextId, nfocus]
            rcases List.mem_append.mp hl with hl | hl
            · have := ids l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              show m.nextId < m.nextId + 1
              omega
          · intro l hl
            rw [last₁]
            rcases List.mem_append.mp hl with hl | hl
            · have := addrs l hl; omega
            · obtain rfl := List.mem_singleton.mp hl
              exact le_refl _
          · rw [last₁, List.length_append, List.length_singleton]
            push_cast
            omega
        have o := block_halts hret (xs ++ [(x, ity)]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k hk
        have out : m₁.stdout = m.stdout := by
          simp [m₁, TyActions.created_stdout]
        rw [out] at o
        exact TyStmt.Shows.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
          (create.trans bind)) o
      next => cases h
    next => cases h
  next =>
    split at h
    next nodup => exact stmts_halts hret nodup _ _ e h env m ls inv hls k hk
    next => cases h
termination_by sizeOf e

/-- The whole-document run. -/
theorem recognize_reaches (doc : Codec.Document) (R : Res) (h : recognizeRes doc = some R)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s R.val "" := by
  unfold recognizeRes at h
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
          have hbody : recognizeBody doc.file body = some R := by simpa [main, decl] using h
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
              have inv₀ : Inv (∅ : Env) m [] (fun _ => none) :=
                ⟨by simp, by simp, by simp, by simp, fun _ _ hd => by cases hd⟩
              have fresh₀ : Fresh m [] := ⟨hdead, by simp, by simp, by simp [hlast]⟩
              have o := block_halts hret [] a hbody ∅ m [] inv₀ rfl fresh₀
                [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
                (by simp [NoBoundary, hasBoundary])
              rw [hout] at o
              exact ⟨s, labels, hinit, TyStmt.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with
`R.val mod 256` and no output. -/
theorem recognizeRes_of {doc : Codec.Document} {R : Res} (h : recognize doc = some R) :
    recognizeRes doc = some R ∧ Res.wf R = true := by
  unfold recognize at h
  split at h
  · rename_i R' hR
    split at h
    · cases h; exact ⟨hR, by assumption⟩
    · cases h
  · cases h

theorem recognize_sound (doc : Codec.Document) (R : Res) (h : recognize doc = some R)
    (args : List String) :
    Spec.CoreUB doc args ∨ Spec.CoreBeh doc args (.exit (R.val % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc R (recognizeRes_of h).1 (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    have beh := Spec.CoreBeh.exit (k := (R.val % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩

end Silmaril.Compile.Core.Verified.TyState
