module

public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.ReturnExpr.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # `main` as a block of `int` locals and statements

`recognize doc = some T`: `main` is a procedure without parameters, the file has no global
definitions, and `main`'s body is a block whose locals are `int`s created first
(`create(Ivalignof(int), int)`, any number, distinct keys), followed by a sequence of the
statements of `StateStmt`: `int x;`, `int x = e;`, `x = e;`, `if (c) return e;` and
`return e;`, every expression an `int` expression over literals and reads of locals already
initialised (`StateExpr.term`).

`T` is a closed `IntExpr.Term` that computes the returned value: each assignment replaces the
local's definition by the closed expression of its right-hand side (`StateExpr.close`), and
`if (c) return e; rest` becomes the runtime selection `StmtIf.choose c e rest`. The Lir code
computes `T` at run time (`IntExpr.exprOps 0 T`, as for `ReturnExpr`); nothing is folded.
A size bound on `T` (`closeSize`) keeps repeated self-assignments from blowing up.

`recognize_sound`: Core reaches undefined behaviour (an operator leaves `int`) or exits with
`T.val 0 mod 256` and no output, for every argument list. The Core run creates the locals in
the concrete memory (`StateMem.Fresh`), keeps each initialised local's slot holding the value
of its definition (`StateMem.Inv`), lifts each assignment's negative store to its bound, and
kills the locals before the jump to the return label.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.State

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt
open LocalExpr (Shows)

/-- The statements. -/
inductive Stmt where
  | ret (t : Term)
  | ifRet (c a : Term)
  | assign (x : Sym) (t : Term)
  | init (x : Sym) (t : Term)
  | uninit (x : Sym)

/-- Which statement `s` is. -/
def classify (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) (s : Eff) :
    Option Stmt :=
  match retStmt file ret xs s with
  | some t => some (.ret t)
  | none => match ifRet file ret xs s with
    | some (c, a) => some (.ifRet c a)
    | none => match assignStmt file s with
      | some (x, t) => some (.assign x t)
      | none => match initStmt file s with
        | some (x, t) => some (.init x t)
        | none => (uninitStmt s).map .uninit

/-- What the classification of `s` says about `s`. -/
def Shape (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) (s : Eff) : Stmt → Prop
  | .ret t => retStmt file ret xs s = some t
  | .ifRet c a => ifRet file ret xs s = some (c, a)
  | .assign x t => assignStmt file s = some (x, t)
  | .init x t => initStmt file s = some (x, t)
  | .uninit x => uninitStmt s = some x

theorem classify_spec {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym} {s : Eff}
    {st : Stmt} (h : classify file ret xs s = some st) : Shape file ret xs s st := by
  unfold classify at h
  split at h
  next t ht => cases h; exact ht
  next =>
    split at h
    next c a hc => cases h; exact hc
    next =>
      split at h
      next x t hx => cases h; exact hx
      next =>
        split at h
        next x t hx => cases h; exact hx
        next =>
          cases hu : uninitStmt s with
          | none => simp [hu] at h
          | some x =>
            simp only [hu, Option.map_some, Option.some.injEq] at h
            subst h
            exact hu

/-- The size of the closed expression of `t`, `sz q` the size of the definition of `q`. -/
def closeSize (sz : Key → Nat) : Term → Nat
  | .lit _ => 1
  | .var q => sz q
  | .bin _ a b => 1 + closeSize sz a + closeSize sz b
  | .cmp _ _ _ a b => 1 + closeSize sz a + closeSize sz b
  | .cond c a b => 1 + closeSize sz c + closeSize sz a + closeSize sz b
  | .un _ a => 2 + closeSize sz a
  | .bit _ a b => 1 + closeSize sz a + closeSize sz b
  | .divpos _ _ a => 2 + closeSize sz a

/-- The largest closed expression the fragment emits. -/
def maxSize : Nat := 4096

/-- The statements of a block with the locals `xs`, the definitions `ds` (sizes `sz`). -/
def stmts (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) :
    (Key → Option IntExpr.Term) → (Key → Nat) → Eff → Option IntExpr.Term
  | ds, sz, .mk _ (.sseq (.mk _ (.base (none, _))) s rest) =>
    match classify file ret xs s with
    | some (.ret t) =>
      if Defined ds t = true ∧ closeSize sz t ≤ maxSize then some (close (defsOf ds) t) else none
    | some (.ifRet c a) =>
      if Defined ds c = true ∧ Defined ds a = true ∧ closeSize sz c ≤ maxSize ∧
          closeSize sz a ≤ maxSize then
        (stmts file ret xs ds sz rest).map
          (StmtIf.choose (close (defsOf ds) c) (close (defsOf ds) a))
      else none
    | some (.assign x t) =>
      if isLocal xs x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
        stmts file ret xs (update ds x.key (some (close (defsOf ds) t)))
          (fun q => if q = x.key then closeSize sz t else sz q) rest
      else none
    | some (.init x t) =>
      if isLocal xs x = true ∧ Defined ds t = true ∧ closeSize sz t ≤ maxSize then
        stmts file ret xs (update ds x.key (some (close (defsOf ds) t)))
          (fun q => if q = x.key then closeSize sz t else sz q) rest
      else none
    | some (.uninit x) =>
      if isLocal xs x = true then stmts file ret xs (update ds x.key none) sz rest else none
    | none => none
  | _, _, _ => none
termination_by _ _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The block: the creations of its locals, then its statements. -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) : List Sym → Eff → Option IntExpr.Term
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    if Locals.createInt cr = true ∧ isFresh xs x = true ∧ xs.length < 1024 then
      block file ret (xs ++ [x]) rest
    else none
  | xs, e =>
    if (xs.map (·.key)).Nodup then stmts file ret xs (fun _ => none) (fun _ => 0) e else none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then block file ret [] a else none
  | _ => none

/-- `main` is a block of `int` locals and statements. -/
def recognize (doc : Codec.Document) : Option IntExpr.Term := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-! ## Core side -/

variable {file : Program} {labels : Labels}

theorem Keys.mem_of_local {ls : List Local} {xs : List Sym} (h : Keys ls xs) {x : Sym}
    (hx : isLocal xs x = true) : ∃ l ∈ ls, x.key = l.sym.key := by
  obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hx
  have hm : y.key ∈ ls.map (·.sym.key) := by rw [h]; exact List.mem_map_of_mem hy
  obtain ⟨l, hl, hlk⟩ := List.mem_map.mp hm
  exact ⟨l, hl, by rw [← (beq_iff_eq.mp hyx), hlk]⟩

theorem update_key {ds : Key → Option IntExpr.Term} {x : Sym} {l : Local} (hx : x.key = l.sym.key)
    (d : Option IntExpr.Term) : update ds x.key d = update ds l.sym.key d := by rw [hx]

/-- The selection shows its first branch when the test is not `1`. -/
theorem shows_choose_left {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 ≠ 1) (o : Shows (file := file) (labels := labels) s 0 A out) :
    Shows (file := file) (labels := labels) s 0 (StmtIf.choose C A B) out := by
  rcases o with ⟨okA, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okA]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_right h1]; exact r
  · exact .inr ub

/-- The selection shows its second branch when the test is `1`. -/
theorem shows_choose_right {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 = 1) (o : Shows (file := file) (labels := labels) s 0 B out) :
    Shows (file := file) (labels := labels) s 0 (StmtIf.choose C A B) out := by
  rcases o with ⟨okB, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okB]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_left h1]; exact r
  · exact .inr ub

/-- **The statements** show the value of the closed expression, or undefined behaviour. -/
theorem stmts_halts {ret : Sym} (hret : ReturnLabel labels ret) {xs : List Sym}
    (nodup : (xs.map (·.key)).Nodup) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : Eff)
    {T : IntExpr.Term} (h : stmts file ret xs ds sz e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls ds) (hls : Keys ls xs) (k : List Frame) (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : NoBoundary K := noBoundary_cons hk trivial
    have pre : Reaches file labels ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (none, ty))) s rest))
        env, k, m⟩ ⟨.effectExpr s env, K, m⟩ :=
      ReturnConst.sequence_reaches file labels ann _ s rest env k m
    refine Shows.pre pre ?_
    split at h
    next t hc =>
      split at h
      next hd =>
        cases h
        exact ret_halts hret (classify_spec hc) inv hls nodup hd.1 hK
      next => cases h
    next c a hc =>
      split at h
      next hd =>
        cases hr : stmts file ret xs ds sz rest with
        | none => simp [hr] at h
        | some Tr =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          have okC := fun okc => StateExpr.close_ok (defsOf ds) c (inv.defs_ok hd.1) okc
          rcases ifRet_runs hret (classify_spec hc) inv hls nodup hd.1 hd.2.1 hK with
            ub | ⟨okc, h1, o⟩ | ⟨okc, h1, m', out, inv', reach⟩
          · exact .inr ub
          · exact shows_choose_left (okC okc) (by rw [StateExpr.close_val]; exact h1) o
          · have o := stmts_halts hret nodup ds sz rest hr env m' ls inv' hls k hk
            rw [out] at o
            exact shows_choose_right (okC okc) (by rw [StateExpr.close_val]; exact h1)
              (Shows.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
                .unit rest env k m')) o)
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases assign_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls k hk
          rw [out] at o
          exact Shows.pre (reach.trans (ReturnConst.wildcard_sequence_reaches file labels pann ty
            .unit rest env k m')) o
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases init_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', ys, out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
            (noBoundary_cons hk trivial)
          rw [out] at o
          exact Shows.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest env k m'))
            o
      next => cases h
    next x hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := Keys.mem_of_local hls hd
        rw [update_key hx] at h
        obtain ⟨m', ys, out, inv', reach⟩ := uninit_runs (classify_spec hc) inv hl hx K
        have o := stmts_halts hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
          (noBoundary_cons hk trivial)
        rw [out] at o
        exact Shows.pre (reach.trans (Locals.annotations_bind_reaches ys pann ty .unit rest env k m')) o
      next => cases h
    next => cases h
  next => cases h
termination_by sizeOf e

theorem focus_nextId (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).nextId = m.nextId := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem focus_dead (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).dead = m.dead := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem focus_lastAddress (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).lastAddress = m.lastAddress := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem created_nextId (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (Actions.created pref ann m).nextId = m.nextId + 1 := by
  unfold Actions.created Mem.Concrete.updateLastAllocation
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape (nextIntAddress m)
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  rw [hw]
  split
  · rfl
  · split <;> rfl

theorem createInt_inv {e : Eff} (h : Locals.createInt e = true) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (a1 a2 c1 a3 c2 : List Annot) (pref : Prefix),
      e = .mk ann (.action (.mk .pos (.mk l u
        (.create (.mk a1 () (.ctor .ivAlignof [Locals.intVal a2 c1])) (Locals.intVal a3 c2) pref)))) := by
  unfold Locals.createInt at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

/-- **The block**: creating its locals keeps `Fresh` and `Inv`, then its statements show. -/
theorem block_halts {ret : Sym} (hret : ReturnLabel labels ret) (xs : List Sym) (e : Eff)
    {T : IntExpr.Term} (h : block file ret xs e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls (fun _ => none)) (hls : Keys ls xs) (fresh : Fresh m ls)
    (k : List Frame) (hk : NoBoundary k) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 T m.stdout := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := createInt_inv hcr
      have hnext : nextIntAddress m = m.lastAddress - 4 := fresh.nextIntAddress
      have hpos : 0 < nextIntAddress m := by
        rw [hnext, fresh.last, hlen]
        simp only [StartupReach.errnoAddr]
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      have create := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
        pref env K m hpos
      rw [focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let m₁ := Actions.created pref c2 (focusMemory ann m)
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) (fun _ => none) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro l hl y hy
          rcases List.mem_append.mp hl with hl | hl
          · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
            exact inv.env l hl y hy
          · obtain rfl := List.mem_singleton.mp hl
            exact ConvInt.lookup_one hy
        · intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · refine StateMem.live_created (Locals.liveInt_focus ann (inv.live l hl)) pref c2 ?_
            rw [focus_nextId]; exact Int.ne_of_lt (ids l hl)
          · obtain rfl := List.mem_singleton.mp hl
            have := Locals.created_live pref c2 (focusMemory ann m)
              (by rw [focus_dead, fresh.dead, focus_nextId]; simp)
            rwa [Locals.nextIntAddress_focus, focus_nextId] at this
        · intro a ha b hb ne
          rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
          · exact inv.apart a ha b hb ne
          · obtain rfl := List.mem_singleton.mp hb
            refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
            have := addrs a ha
            show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
            omega
          · obtain rfl := List.mem_singleton.mp ha
            refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
            have := addrs b hb
            show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
            omega
          · obtain rfl := List.mem_singleton.mp ha
            obtain rfl := List.mem_singleton.mp hb
            exact absurd rfl ne
        · intro q d hd; cases hd
      have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls]
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Fresh m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Locals.created_dead, focus_dead, fresh.dead]
        · intro l hl
          rw [created_nextId, focus_nextId]
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
            show m.lastAddress - 4 ≤ nextIntAddress m
            omega
        · rw [last₁, fresh.last, List.length_append, List.length_singleton]
          push_cast
          ring
      have o := block_halts hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k hk
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      rw [out] at o
      exact Shows.pre ((ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans bind)) o
    next => cases h
  next =>
    split at h
    next nodup => exact stmts_halts hret nodup _ _ e h env m ls inv hls k hk
    next => cases h
termination_by sizeOf e

/-- The whole-document run. -/
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
              have inv₀ : Inv (∅ : Env) m [] (fun _ => none) :=
                ⟨by simp, by simp, by simp, fun _ _ hd => by cases hd⟩
              have fresh₀ : Fresh m [] := ⟨hdead, by simp, by simp, by simp [hlast]⟩
              have o := block_halts hret [] a hbody ∅ m [] inv₀ rfl fresh₀
                [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
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

end Silmaril.Compile.Core.Verified.State
