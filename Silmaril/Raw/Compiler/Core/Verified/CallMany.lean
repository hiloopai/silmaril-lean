module

public import Silmaril.Compiler.Core.Verified.CallManyEval.Defs
public import Silmaril.Compiler.Core.Verified.CallParamAlloc.Defs
public import Silmaril.Compiler.Core.Verified.PrintfKill.Defs
/-! # Calls with several `int` arguments: the caller's side

Cerberus elaborates a call `g(n₁, …, nₖ)` with `k ≥ 2` closed `int` arguments as

```
let strong ((p, (fty, ptys, v, pr)), a₁, …, aₖ) = unseq(<g>, n₁, …, nₖ) in
if not(params_length(ptys) = k) then undef else
if v \/ not(are_compatible(int, fty)) then undef else
let strong x₁ = (let t = params_nth(ptys, 0) in if not are_compatible(int, t) then undef else
  let weak o = create(alignof(int), int) in store(int, o, conv_loaded_int(int, a₁)) ; pure(o)) in
…
let strong xₖ = (… params_nth(ptys, k - 1) … aₖ …) in
let strong r = ccall(_, p, x₁, …, xₖ) in
let strong _ = unseq(kill(int, x₁), …, kill(int, xₖ)) in pure(r)
```

`argSite` recognizes it; `Prepared` is the state at the scheduled call, with the `k` argument
objects allocated below each other (`ArgsMem`) and the caller's cleanup frames, which kill all of
them (`Cleanup`).
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.CallMany

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open ConvInt (IsInt)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open LoadTask (Touched ReadTask plain_effectExpr plain_value plain_pureExpr)
open CallArg (fnTask argLit mkArg isParamsLength isSseq lookup_cons lookup_cons_eq lookup_cons_ne
  lookup_nil fnInfo touched_seq touched_nextIntAddress touched_nextId touched_dead)
open CallParamLocal (annotations_sbind annotations_wbind not_compatible variadic_check)
open CallParamAlloc (Reserve)
open CallManyEval (ctypes)
open Call (retKind)

/-! ## Environments and patterns -/

theorem lookup_extend_mem : ∀ {bs : Bindings} {env : Env} {s : Sym} {v : Val} {y : Sym},
    (bs.map (·.1.key)).Nodup → (s, v) ∈ bs → y.key = s.key → (extendEnv bs env).lookup y = some v
  | [], _, _, _, _, _, h, _ => by simp at h
  | (a, w) :: bs, env, s, v, y, nd, h, hy => by
    rw [lookup_cons]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [hy]
    · have ne : y.key ≠ a.key := by
        rw [hy]; intro e; exact nd.1 ⟨(s, v), h, e⟩
      simp only [ne, ↓reduceIte]
      exact lookup_extend_mem nd.2 h hy

theorem lookup_extend_not : ∀ {bs : Bindings} {env : Env} {y : Sym},
    y.key ∉ bs.map (·.1.key) → (extendEnv bs env).lookup y = env.lookup y
  | [], _, _, _ => rfl
  | (a, w) :: bs, env, y, h => by
    rw [lookup_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [h.1, ↓reduceIte]
    exact lookup_extend_not h.2

/-- The symbols of a list of `base` patterns with names. -/
def baseSyms : List (Pattern Sym) → Option (List Sym)
  | [] => some []
  | .mk _ (.base (some a, _)) :: ps => (baseSyms ps).map (a :: ·)
  | _ :: _ => none

theorem baseSyms_match : ∀ {ps : List (Pattern Sym)} {as : List Sym} {vs : List Val},
    baseSyms ps = some as → as.length = vs.length → matchPatterns ps vs = some (as.zip vs)
  | [], as, vs, h, hl => by
    simp only [baseSyms, Option.some.injEq] at h
    subst h
    cases vs with
    | nil => simp [matchPatterns]
    | cons _ _ => simp at hl
  | .mk _ (.base (some a, _)) :: ps, as, vs, h, hl => by
    simp only [baseSyms, Option.map_eq_some_iff] at h
    obtain ⟨as', h', rfl⟩ := h
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.length_cons, add_left_inj] at hl
      simp [matchPatterns, matchPattern, baseSyms_match h' hl, bind, Option.bind]
  | .mk _ (.base (none, _)) :: _, _, _, h, _ => by simp [baseSyms] at h
  | .mk _ (.ctor _ _) :: _, _, _, h, _ => by simp [baseSyms] at h

/-- The closed `int` arguments of a call. -/
def argLits (file : File Codec.wireModel Unit Unit) : List Eff → Option (List Int)
  | [] => some []
  | e :: es => match argLit file e, argLits file es with
    | some n, some ns => some (n :: ns)
    | _, _ => none

theorem argLits_spec {file : File Codec.wireModel Unit Unit} :
    ∀ {es : List Eff} {ns : List Int}, argLits file es = some ns →
      List.Forall₂ (fun e n => argLit file e = some n) es ns
  | [], ns, h => by simp only [argLits, Option.some.injEq] at h; subst h; exact .nil
  | e :: es, ns, h => by
    unfold argLits at h
    split at h
    · rename_i n ns' he hes
      cases h
      exact .cons he (argLits_spec hes)
    · cases h

/-! ## Syntax of the argument objects and the call -/

/-- `let t = params_nth(ps, i) in if not are_compatible(int, t) then undef else <mkArg a>`. -/
def letArgAt (file : File Codec.wireModel Unit Unit) (pty a : Sym) (i : Nat) : Eff → Bool
  | .mk _ (.let_ (.mk _ (.base (some tt, _)))
      (.mk _ () (.call (.sym nth) [.mk _ () (.sym pty₂), .mk _ () (.val (.object (.integer idx)))]))
      (.mk _ (.if_ (.mk _ () (.not (.mk _ () (.areCompatible (.mk _ () (.val (.ctype ity)))
          (.mk _ () (.sym tt₁))))))
        _ mk))) =>
      decide (pty₂.key = pty.key ∧ tt₁.key = tt.key ∧ idx = (i : Int) ∧ a.key ≠ tt.key) &&
        CallManyEval.isParamsNthRec file nth && decide (retKind ity = some true) && mkArg file a mk
  | _ => false

/-- The kills of the argument objects `xs`, in order. -/
def killsOf : List Eff → List Sym → Bool
  | [], [] => true
  | k :: ks, x :: xs => Locals.killInt x k && killsOf ks xs
  | _, _ => false

/-- `let strong _ = unseq(kill(int, x₁), …, kill(int, xₖ)) in pure(r)`. -/
def killsTail (xs : List Sym) (r : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) (.mk _ (.unseq ks)) (.mk _ (.pure (.mk _ () (.sym r₁))))) =>
      killsOf ks xs && decide (r₁.key = r.key)
  | _ => false

/-- The symbol of an operand that is a symbol. -/
def symOf : PE → Option Sym
  | .mk _ () (.sym x) => some x
  | _ => none

/-- The symbols of an operand list of symbols. -/
def symsOf : List PE → Option (List Sym)
  | [] => some []
  | p :: ps => match symOf p, symsOf ps with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- `let strong r = ccall(_, p, x₁, …, xₖ) in <killsTail>`. -/
def callTail (p : Sym) (xs : List Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (some r, _))) (.mk _ (.ccall () _ (.mk _ () (.sym p₁)) args)) kt) =>
      match symsOf args with
      | some ys => decide (p₁.key = p.key ∧ ys.map (·.key) = xs.map (·.key) ∧
          r.key ∉ xs.map (·.key)) && killsTail xs r kt
      | none => false
  | _ => false

/-- `let strong x = la in ct`: the next argument object's name, its definition and the rest. -/
def restStep : Eff → Option (Sym × Eff × Eff)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) la ct) => some (x, la, ct)
  | _ => none

theorem restStep_spec {e : EE} {x : Sym} {la ct : EE} (h : restStep e = some (x, la, ct)) :
    ∃ ann xann xbt, e = .mk ann (.sseq (.mk xann (.base (some x, xbt))) la ct) := by
  unfold restStep at h
  split at h
  · cases h; exact ⟨_, _, _, rfl⟩
  · cases h

/-- The argument objects of `as`, from parameter index `i` on (`xs`: the objects so far), then
the call. Each object's name is fresh for everything still read. -/
def rest (file : File Codec.wireModel Unit Unit) (pty p : Sym) :
    List Sym → Nat → List Sym → Eff → Bool
  | [], _, xs, e => callTail p xs e
  | a :: as, i, xs, e => match restStep e with
    | some (x, la, ct) => decide (x.key ∉ (p :: pty :: as ++ xs).map (·.key)) &&
        letArgAt file pty a i la && rest file pty p as (i + 1) (xs ++ [x]) ct
    | none => false

/-- The arity and function-type guards, then the argument objects and the call. -/
def guards (file : File Codec.wireModel Unit Unit) (fty pty vs p : Sym) (as : List Sym) :
    Eff → Bool
  | .mk _ (.if_ (.mk _ () (.not (.mk _ () (.op .eq (.mk _ () (.call (.sym len) [.mk _ () (.sym pty₁)]))
        (.mk _ () (.val (.object (.integer n))))))))
      _ (.mk _ (.if_ (.mk _ () (.op .or (.mk _ () (.sym vs₁)) (.mk _ () (.not (.mk _ ()
          (.areCompatible (.mk _ () (.val (.ctype rty))) (.mk _ () (.sym fty₁))))))))
        _ r))) =>
      decide (pty₁.key = pty.key ∧ vs₁.key = vs.key ∧ fty₁.key = fty.key ∧ n = (as.length : Int)) &&
        isParamsLength file len && decide (retKind rty = some true) && rest file pty p as 0 [] r
  | _ => false

/-- The most arguments of a recognized call. -/
def maxArgs : Nat := 16

/-- The elaboration of a call `g(n₁, …, nₖ)`, `2 ≤ k ≤ maxArgs`, of closed `int` arguments:
the procedure and the argument values. -/
def argSite (file : File Codec.wireModel Unit Unit) : Eff → Option (Sym × List Int)
  | .mk _ (.sseq (.mk _ (.ctor .tuple (.mk _ (.ctor .tuple [.mk _ (.base (some p, _)),
        .mk _ (.ctor .tuple [.mk _ (.base (some fty, _)), .mk _ (.base (some pty, _)),
          .mk _ (.base (some vs, _)), .mk _ (.base (some pr, _))])]) :: aps)))
      (.mk _ (.unseq (t1 :: ts))) gd) =>
      match fnTask t1, baseSyms aps, argLits file ts with
      | some g, some as, some ns =>
        if decide (2 ≤ as.length ∧ as.length ≤ maxArgs ∧ as.length = ns.length) &&
            decide (((p :: fty :: pty :: vs :: pr :: as).map (·.key)).Nodup) &&
            ns.all (fun n => decide (-2147483648 ≤ n ∧ n ≤ 2147483647)) &&
            guards file fty pty vs p as gd
        then some (g, ns) else none
      | _, _, _ => none
  | _ => none

theorem argSite_facts {file : File Codec.wireModel Unit Unit} {e : EE} {g : Sym} {ns : List Int}
    (h : argSite file e = some (g, ns)) : ns.length ≤ maxArgs ∧ ∀ n ∈ ns, IsInt n := by
  unfold argSite at h
  split at h
  · rename_i _ eA pA pA1 pA2 p pT pA3 fA fty fT psA pty psT vA vs vT prA pr prT aps uA t1 ts gd
    cases hfn : fnTask t1 <;> cases hbs : baseSyms aps <;> cases hlits : argLits file ts <;>
      simp only [hfn, hbs, hlits, reduceCtorEq] at h
    split at h
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at cond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨by omega, fun n hn => cond.1.2 n hn⟩
    · cases h
  · cases h

theorem argSite_len {file : File Codec.wireModel Unit Unit} {e : EE} {g : Sym} {ns : List Int}
    (h : argSite file e = some (g, ns)) : ns.length ≤ maxArgs := (argSite_facts h).1

theorem argSite_range {file : File Codec.wireModel Unit Unit} {e : EE} {g : Sym} {ns : List Int}
    (h : argSite file e = some (g, ns)) : ∀ n ∈ ns, IsInt n := (argSite_facts h).2

/-! ## The argument objects in memory -/

/-- The pointer to an argument object `(id, addr)`. -/
abbrev ptrOf (o : Int × Int) : Val := .object (.pointer (.allocated o.1 o.2))

/-- The argument objects `objs` hold `ns`, below the allocation frontier, with distinct ids
and disjoint bytes. -/
structure ArgsMem (m : Mem.Concrete.State) (objs : List (Int × Int)) (ns : List Int) : Prop where
  slots : List.Forall₂ (fun o n => Locals.Slot m o.1 o.2 n) objs ns
  below : ∀ o ∈ objs, o.1 < m.nextId
  above : ∀ o ∈ objs, m.lastAddress ≤ o.2
  apart : objs.Pairwise (fun a b => a.1 ≠ b.1 ∧ Slots.Apart a.2 4 b.2 4)

theorem ArgsMem.nil (m : Mem.Concrete.State) : ArgsMem m [] [] :=
  ⟨.nil, by simp, by simp, .nil⟩

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : List.Forall₂ R l₁ l₂) (hab : R a b) : List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (f : ∀ a ∈ l₁, ∀ b, R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    exact .cons (f _ (by simp) _ h) (ih fun a ha b r => f a (by simp [ha]) b r)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => simp at ha
  | cons h _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, by simp, h⟩
    · obtain ⟨b, hb, r⟩ := ih ha; exact ⟨b, by simp [hb], r⟩

/-- A memory change that keeps every slot apart from a fresh object keeps `ArgsMem`, and the
fresh object joins it. -/
theorem ArgsMem.snoc {m m' : Mem.Concrete.State} {objs : List (Int × Int)} {ns : List Int}
    (h : ArgsMem m objs ns) {n : Int} (aligned : m.lastAddress % 4 = 0)
    (keep : ∀ id addr v, Locals.Slot m id addr v → id ≠ m.nextId →
      Slots.Apart (nextIntAddress m) 4 addr 4 → Locals.Slot m' id addr v)
    (slot : Locals.Slot m' m.nextId (nextIntAddress m) n)
    (next : m'.nextId = m.nextId + 1) (last : m'.lastAddress = nextIntAddress m) :
    ArgsMem m' (objs ++ [(m.nextId, nextIntAddress m)]) (ns ++ [n]) := by
  have na : nextIntAddress m = m.lastAddress - 4 := by
    simp only [nextIntAddress]; omega
  refine ⟨forall₂_snoc (forall₂_imp h.slots fun o ho v s => keep _ _ _ s
      (by have := h.below o ho; omega) (by have := h.above o ho; left; omega)) slot, ?_, ?_, ?_⟩
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · have := h.below o ho; omega
    · simp at ho; subst ho; simp; omega
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · have := h.above o ho; omega
    · simp at ho; subst ho; simp [last]
  · refine List.pairwise_append.mpr ⟨h.apart, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨by have := h.below a ha; omega, by have := h.above a ha; right; simp; omega⟩

/-! ## Allocating the argument objects -/

variable {file : Program} {labels : Labels}

/-- `CallParamAlloc.mkArg_local`, which also keeps every older slot apart from the new object. -/
theorem mkArg_frame {fuel : Nat} {a : Sym} {e : EE} (h : mkArg file a e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {n : Int} (ha : env.lookup a = some (IntExpr.spec n))
    (hn : IntRange n) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead)
    (hb : Reserve (fuel + 1) m) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Locals.Slot m' m.nextId (nextIntAddress m) n ∧ Reserve fuel m' ∧
      m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextIntAddress m ∧
      (∀ id addr v, Locals.Slot m id addr v → id ≠ m.nextId →
        Slots.Apart (nextIntAddress m) 4 addr 4 → Locals.Slot m' id addr v) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold mkArg at h
  split at h
  · rename_i _ ann oann o ot cr wann w2ann w2t stann stl stu a1 c1 a2 o₁ a3 cv a4 c3 a5 a₁ pann bann o₂
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hcr, ho₁, ho₂, ha₁, hao⟩, hcv⟩ := h
    unfold Locals.createInt at hcr
    split at hcr
    · rename_i crann crloc cru ca1 ca2 cc1 ca3 cc2 pref
      let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
      let PURE : EE := .mk pann (.pure (.mk bann () (.sym o₂)))
      let ST : EE := .mk stann (.action (.mk .pos (.mk stl stu (.store false
        (Locals.intVal a1 c1) (.mk a2 () (.sym o₁))
        (.mk a3 () (.call (.sym cv) [Locals.intVal a4 c3, .mk a5 () (.sym a₁)])) .na))))
      let W2 : EE := .mk wann (.wseq (.mk w2ann (.base (none, w2t))) ST PURE)
      let m₁ := Actions.created pref cc2 (focusMemory crann m)
      have rc := StateActionsLocal.create (file := file) (labels := labels) crann ca1 ca2 ca3 cc1 cc2
        crloc cru pref env (.effectBind (.mk oann (.base (some o, ot))) W2 env :: k) m hpos
      rw [touched_nextId (LoadTask.focusMemory_touched crann m)] at rc
      have live₁ : LiveInt m₁ m.nextId (nextIntAddress m) := by
        simpa [m₁, Locals.nextIntAddress_focus, touched_nextId (LoadTask.focusMemory_touched crann m)] using
          (Locals.created_live pref cc2 (focusMemory crann m) (by rw [touched_nextId (LoadTask.focusMemory_touched crann m), touched_dead (LoadTask.focusMemory_touched crann m)]; exact hdead))
      let env₁ := extendEnv [(o, ptr)] env
      have hx₁ : env₁.lookup o₁ = some ptr := ConvInt.lookup_one ho₁
      have ht₁ : env₁.lookup a₁ = some (IntExpr.spec n) := by
        rw [ConvInt.lookup_one_other (by rw [ha₁]; exact hao), ReturnLit.lookup_key ha₁]; exact ha
      obtain ⟨ys, rst⟩ := StateActionsLocal.store (file := file) (labels := labels)
        stann a1 a2 a3 a4 a5 c1 c3 stl stu o₁ cv a₁ hcv env₁
        (.effectBind (.mk w2ann (.base (none, w2t))) PURE env₁ :: k) m₁ hx₁ ht₁ hn live₁
      let m₂ := Locals.stored (focusMemory stann m₁) m.nextId (nextIntAddress m) n
      refine ⟨focusMemory pann m₂, ys, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [m₂, m₁, Locals.stored_stdout, Actions.created_stdout]
      · exact (LoadTask.focusMemory_touched pann m₂).slot
          (Locals.stored_slot (Locals.liveInt_focus stann live₁) n)
      · exact (((hb.focus crann).created pref cc2).same (Rmw.same_focus stann m₁)).same
          (Rmw.same_stored _ _ _ _) |>.focus pann
      · calc
          (focusMemory pann m₂).nextId = m₂.nextId := (Rmw.same_focus pann m₂).1
          _ = (focusMemory stann m₁).nextId := (Rmw.same_stored _ _ _ _).1
          _ = m₁.nextId := (Rmw.same_focus stann m₁).1
          _ = m.nextId + 1 := by simp [m₁, State.created_nextId, State.focus_nextId]
      · calc
          (focusMemory pann m₂).lastAddress = m₂.lastAddress := (Rmw.same_focus pann m₂).2.2
          _ = (focusMemory stann m₁).lastAddress := (Rmw.same_stored _ _ _ _).2.2
          _ = m₁.lastAddress := (Rmw.same_focus stann m₁).2.2
          _ = nextIntAddress m := by
            simp only [m₁, Locals.created_lastAddress, Locals.nextIntAddress_focus]
      · intro id addr v s ne ap
        have t0 := LoadTask.focusMemory_touched crann m
        have s1 : Locals.Slot m₁ id addr v :=
          Slots.slot_created (t0.slot s) pref cc2 (by rw [touched_nextId t0]; exact ne)
            (by rw [Locals.nextIntAddress_focus]; exact ap)
        exact (LoadTask.focusMemory_touched pann m₂).slot
          (Slots.slot_stored ((LoadTask.focusMemory_touched stann m₁).slot s1) m.nextId
            (nextIntAddress m) n ap)
      refine (StateActionsLocal.wseq ann _ _ W2 env k m).trans (rc.trans ?_)
      have bind : LocalReaches file labels false
          ⟨.value ptr, .effectBind (.mk oann (.base (some o, ot))) W2 env :: k, m₁⟩
          ⟨.effectExpr W2 env₁, k, m₁⟩ :=
        .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, env₁]) (plain_effectExpr _ _))
      refine bind.trans ?_
      refine (StateActionsLocal.wseq wann _ ST PURE env₁ k m₁).trans (rst.trans ?_)
      refine (annotations_wbind ys (bs := []) rfl PURE env₁ k m₂).trans ?_
      exact CallLocal.pure pann (fun _ => .sym (by
        rw [lookup_nil]; exact ConvInt.lookup_one ho₂)) (.annotations ys :: k) m₂
    · cases hcr
  · cases h

/-- The argument at parameter index `i`: its type guard, then its object. -/
theorem letArgAt_local {fuel : Nat} {pty a : Sym} {i : Nat} {e : EE}
    (h : letArgAt file pty a i e = true) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {cs : List Ctype} {c : Ctype} {n : Int}
    (hp : env.lookup pty = some (ctypes cs)) (hci : cs[i]? = some c) (hc : retKind c = some true)
    (ha : env.lookup a = some (IntExpr.spec n)) (hn : IntRange n)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) (hb : Reserve (fuel + 1) m) :
    ∃ m' ys, m'.stdout = m.stdout ∧ Locals.Slot m' m.nextId (nextIntAddress m) n ∧ Reserve fuel m' ∧
      m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextIntAddress m ∧
      (∀ id addr v, Locals.Slot m id addr v → id ≠ m.nextId →
        Slots.Apart (nextIntAddress m) 4 addr 4 → Locals.Slot m' id addr v) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), .annotations ys :: k, m'⟩ := by
  unfold letArgAt at h
  split at h
  · rename_i _ lann tann tt tbt nann nth a1 pty₂ a2 idx iann cann bann cvann ity cfann tt₁ u mk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty, htt, rfl, hat⟩, hnth⟩, hity⟩, hmk⟩ := h
    let env₁ := extendEnv [(tt, .ctype c)] env
    let m₁ := focusMemory lann m
    let m₂ := focusMemory iann m₁
    have T : Touched m m₂ := (touched_seq lann m).trans (touched_seq iann m₁)
    have ha₁ : env₁.lookup a = some (IntExpr.spec n) := by
      rw [ConvInt.lookup_one_other hat]; exact ha
    obtain ⟨m', ys, out, slot, reserve, next, last, keep, r⟩ := mkArg_frame (fuel := fuel)
      (file := file) (labels := labels) hmk env₁ k m₂ ha₁ hn
      (by rw [touched_nextIntAddress T]; exact hpos)
      (by rw [touched_nextId T, touched_dead T]; exact hdead) (hb.touched T)
    rw [touched_nextId T, touched_nextIntAddress T] at slot r keep
    rw [touched_nextIntAddress T] at last
    refine ⟨m', ys, out.trans T.stdout, slot, reserve, by simpa [touched_nextId T] using next, last,
      fun id addr v s ne ap => keep id addr v (T.slot s) ne ap, ?_⟩
    refine (CallArena.effect_let lann (xs := [(tt, .ctype c)])
      (CallArena.of_eval fun tags => CallManyEval.nth_eval hnth tags cs i c hci rfl
        (.sym ((ReturnLit.lookup_key hpty).trans hp)) .val) rfl k m).trans ?_
    exact (CallArena.effect_if iann false
      (not_compatible hity hc (ConvInt.lookup_one htt)) k m₁).trans r
  · cases h

/-! ## Killing the argument objects -/

theorem killInt_killOf {x : Sym} {e : EE} (h : Locals.killInt x e = true) :
    ∃ cann x', PrintfStmt.killOf e = some (Mem.Concrete.intType cann, x') ∧ x'.key = x.key ∧
      hasCCall e = false := by
  unfold Locals.killInt at h
  split at h
  · rename_i _ ann l u cann a x'
    exact ⟨cann, x', rfl, of_decide_eq_true h, by simp [hasCCall]⟩
  · cases h

theorem unseqTasks_snoc (es : List EE) (e : EE) (env : Env) :
    unseqTasks (es ++ [e]) env = unseqTasks es env ++ [(es.length, .effectExpr e env, [])] := by
  simp [unseqTasks, List.zipIdx_append]

/-- The kills of distinct live objects run as unsequenced tasks, last first. -/
theorem kills_tasks {env : Env} {k : List Frame} :
    ∀ (ps : List (EE × (Int × Int))) (m : Mem.Concrete.State),
    (∀ q ∈ ps, ∃ x, Locals.killInt x q.1 = true ∧ env.lookup x = some (ptrOf q.2)) →
    ((ps.map (·.2.1)).Nodup) → (∀ q ∈ ps, LiveInt m q.2.1 q.2.2) →
    ∃ m', TasksRun file labels false k (unseqTasks (ps.map (·.1)) env) m
        ((List.range ps.length).map fun i => (i, (.unit : Val), ([] : List Access))) m' ∧
      m'.stdout = m.stdout ∧ m'.nextId = m.nextId ∧ m'.lastAddress = m.lastAddress ∧
      (∀ d ∈ m'.dead, d ∈ m.dead ∨ d ∈ ps.map (·.2.1)) := by
  intro ps
  induction ps using List.reverseRecOn with
  | nil => intro m _ _ _; exact ⟨m, by simpa [unseqTasks] using .nil, rfl, rfl, rfl, fun d h => .inl h⟩
  | append_singleton ps q ih =>
    intro m shape nodup live
    obtain ⟨x, hk, hx⟩ := shape q (by simp)
    obtain ⟨cann, x', so, hkey, calls⟩ := killInt_killOf hk
    obtain ⟨ann, run⟩ := PrintfKill.int_task (file := file) (labels := labels) cann so
      ((ReturnLit.lookup_key hkey).trans hx) (live q (by simp))
    let m₁ := StrMem.killed (SeqReach.focusMemory ann m) q.2.1
    have nd : (ps.map (·.2.1)).Nodup ∧ q.2.1 ∉ ps.map (·.2.1) := by
      simp only [List.map_append, List.map_singleton] at nodup
      exact ⟨nodup.sublist (List.sublist_append_left _ _),
        fun hm => by
          have := List.nodup_append.mp nodup
          exact this.2.2 _ hm _ (by simp) rfl⟩
    have live₁ : ∀ q' ∈ ps, LiveInt m₁ q'.2.1 q'.2.2 := by
      intro q' hq'
      refine StateMem.live_killed (Locals.liveInt_focus ann (live q' (by simp [hq']))) _ ?_
      intro e; exact nd.2 (e ▸ List.mem_map_of_mem hq')
    obtain ⟨m', rest, out, next, last, dead⟩ := ih m₁ (fun q' hq' => shape q' (by simp [hq'])) nd.1 live₁
    have flag : taskFlag false k (unseqTasks (ps.map (·.1)) env) = false := by
      apply Interleave.taskFlag_unseq (es := ps.map (·.1)) _ (List.prefix_refl _)
      intro e he
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp he
      obtain ⟨x'', hk', -⟩ := shape q' (by simp [hq'])
      obtain ⟨_, _, _, _, hcall⟩ := killInt_killOf hk'
      exact hcall
    have run' : TaskRuns file labels (taskFlag false k (unseqTasks (ps.map (·.1)) env))
        ⟨.effectExpr q.1 env, [], m⟩ .unit [] m₁ := by rw [flag]; exact run
    refine ⟨m', ?_, ?_, ?_, ?_, ?_⟩
    · have hl : (ps ++ [q]).length = ps.length + 1 := by simp
      rw [List.map_append, List.map_singleton, unseqTasks_snoc, hl, List.range_succ, List.map_append,
        List.map_singleton, List.length_map]
      exact .snoc run' rest
    · rw [out]; simp [m₁, StrMem.killed]
    · rw [next]; simp [m₁, StrMem.killed]
    · rw [last]; simp [m₁, StrMem.killed]
    · intro d hd
      rcases dead d hd with hd | hd
      · simp only [m₁, StrMem.killed, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact .inr (by simp)
        · exact .inl (by simpa using hd)
      · exact .inr (by simp [hd])

/-! ## The prepared call -/

/-- The pointer to the procedure `g`. -/
abbrev fp (g : Sym) : Val := .loaded (.specified (.pointer (.function g)))

/-- Caller frames finish the call by killing its argument objects. -/
def Cleanup (fr : List Frame) (objs : List (Int × Int)) (k : List Frame) : Prop :=
  ∀ (f : Nat) (v : Val) (m : Mem.Concrete.State), (∀ o ∈ objs, LiveInt m o.1 o.2) → Reserve f m →
    (∀ o ∈ objs, o.1 < m.nextId) →
    ∃ m' fs xs, m'.stdout = m.stdout ∧ Reserve f m' ∧ Cond.OneAnn fs xs ∧
      LocalReaches file labels false ⟨.value v, fr, m⟩ ⟨.value v, fs ++ k, m'⟩

/-- Setup stops at the scheduled call of `g` on its argument objects, which hold `ns`. -/
def Prepared (fuel : Nat) (g : Sym) (ns : List Int) (s : State) (k : List Frame) (out : String) :
    Prop :=
  ∃ env m fr objs, m.stdout = out ∧ ArgsMem m objs ns ∧ Reserve fuel m ∧
    LocalReaches file labels false s ⟨.apply (.procedure env) (fp g :: objs.map ptrOf), fr, m⟩ ∧
    Cleanup (file := file) (labels := labels) fr objs k

theorem Prepared.pre {fuel : Nat} {g : Sym} {ns : List Int} {s s' : State} {k : List Frame}
    {out : String} (r : LocalReaches file labels false s s')
    (h : Prepared (file := file) (labels := labels) fuel g ns s' k out) :
    Prepared (file := file) (labels := labels) fuel g ns s k out := by
  obtain ⟨env, m, fr, objs, out, mem, reserve, run, cleanup⟩ := h
  exact ⟨env, m, fr, objs, out, mem, reserve, r.trans run, cleanup⟩

theorem Prepared.annotations {fuel : Nat} {g : Sym} {ns : List Int} {s : State} {k : List Frame}
    {out : String} (ys : List Access)
    (h : Prepared (file := file) (labels := labels) fuel g ns s (.annotations ys :: k) out) :
    Prepared (file := file) (labels := labels) fuel g ns s k out := by
  obtain ⟨env, m, fr, objs, out, mem, reserve, run, cleanup⟩ := h
  refine ⟨env, m, fr, objs, out, mem, reserve, run, ?_⟩
  intro f v m' live reserve hid
  obtain ⟨m'', fs, xs, hout, reserve', hfs, r⟩ := cleanup f v m' live reserve hid
  rcases hfs with ⟨rfl, rfl⟩ | rfl
  · exact ⟨m'', [.annotations ys], ys, hout, reserve', .inr rfl, r⟩
  · refine ⟨m'', [.annotations (xs ++ ys)], xs ++ ys, hout, reserve', .inr rfl, ?_⟩
    exact r.tail (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))

theorem symOf_spec {p : PE} {x : Sym} (h : symOf p = some x) : ∃ ann, p = .mk ann () (.sym x) := by
  unfold symOf at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem symsOf_eval {tags : Mem.Concrete.Tags} {env : Env} (args : List PE) :
    ∀ {ys : List Sym} {objs : List (Int × Int)}, symsOf args = some ys →
    List.Forall₂ (fun y o => env.lookup y = some (ptrOf o)) ys objs →
    Eval file tags env (.inr args) (.inr (objs.map ptrOf)) := by
  induction args with
  | nil =>
    intro ys objs h f
    simp only [symsOf, Option.some.injEq] at h
    subst h; cases f; exact .nil
  | cons p args ih =>
    intro ys objs h f
    cases hp : symOf p with
    | none => simp [symsOf, hp] at h
    | some x =>
      cases hs : symsOf args with
      | none => simp [symsOf, hp, hs] at h
      | some xs =>
        simp only [symsOf, hp, hs, Option.some.injEq] at h
        subst h
        obtain ⟨ann, rfl⟩ := symOf_spec hp
        cases f with
        | cons hx f => exact .cons (.sym hx) (ih hs f)

theorem forall₂_keys {env : Env} : ∀ {ys xs : List Sym} {objs : List (Int × Int)},
    ys.map (·.key) = xs.map (·.key) →
    List.Forall₂ (fun x o => env.lookup x = some (ptrOf o)) xs objs →
    List.Forall₂ (fun y o => env.lookup y = some (ptrOf o)) ys objs
  | [], [], _, _, f => f
  | y :: ys, x :: xs, o :: objs, h, .cons hx f => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons ((ReturnLit.lookup_key h.1).trans hx) (forall₂_keys h.2 f)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

theorem killsOf_pairs : ∀ {ks : List EE} {xs : List Sym} {objs : List (Int × Int)} {env : Env},
    killsOf ks xs = true → List.Forall₂ (fun x o => env.lookup x = some (ptrOf o)) xs objs →
    ∃ ps : List (EE × (Int × Int)), ps.map (·.1) = ks ∧ ps.map (·.2) = objs ∧
      ∀ q ∈ ps, ∃ x, Locals.killInt x q.1 = true ∧ env.lookup x = some (ptrOf q.2)
  | [], [], [], _, _, _ => ⟨[], rfl, rfl, by simp⟩
  | k :: ks, x :: xs, o :: objs, env, h, .cons hx f => by
    simp only [killsOf, Bool.and_eq_true] at h
    obtain ⟨ps, h1, h2, h3⟩ := killsOf_pairs h.2 f
    refine ⟨(k, o) :: ps, by simp [h1], by simp [h2], ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨x, h.1, hx⟩
    · exact h3 q hq
  | [], _ :: _, _, _, h, _ => by simp [killsOf] at h
  | _ :: _, [], _, _, h, _ => by simp [killsOf] at h
  | [], [], _ :: _, _, _, f => by cases f
  | _ :: _, _ :: _, [], _, _, f => by cases f

/-- The call itself and its cleanup continuation. -/
theorem callTail_prepared {fuel : Nat} {p : Sym} {xs : List Sym} {e : EE}
    (h : callTail p xs e = true) {g : Sym} (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {objs : List (Int × Int)} {ns : List Int} (hp : env.lookup p = some (fp g))
    (hxs : List.Forall₂ (fun x o => env.lookup x = some (ptrOf o)) xs objs)
    (mem : ArgsMem m objs ns) (hb : Reserve fuel m) :
    Prepared (file := file) (labels := labels) fuel g ns ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  unfold callTail at h
  split at h
  · rename_i _ ann rann r rt cann mt pann p₁ args kt
    split at h
    · rename_i ys hys
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hp₁, hkeys, hr⟩, hkt⟩ := h
      let K := Frame.strongBind (.mk rann (.base (some r, rt))) kt env :: k
      refine ⟨env, focusMemory cann m, K, objs, by simp, ?_, hb.focus cann, ?_, ?_⟩
      · exact ⟨forall₂_imp mem.slots fun o _ n s => (LoadTask.focusMemory_touched cann m).slot s,
          by simpa only [State.focus_nextId] using mem.below,
          by simpa only [State.focus_lastAddress] using mem.above, mem.apart⟩
      · refine (CallLocal.sequence ann _ _ _ env k m).trans ?_
        refine (CallLocal.focus (c' := .pureExpr (.mk pann () (.sym p₁)) env)
          (k' := .arguments (.procedure env) [] args env :: K)
          cann m (plain_pureExpr _ _) ?_).trans ?_
        · simp [requestAux, awaitsScheduling, arguments, focusMemory]; rfl
        · simpa [PureEval.argState] using PureLocal.args_local file _
            (Eval.cons (Eval.sym (by rw [ReturnLit.lookup_key hp₁]; exact hp))
              (symsOf_eval args hys (forall₂_keys hkeys hxs)))
            (.procedure env) [] K (focusMemory cann m) rfl
      · intro f v m' live reserve hid
        unfold killsTail at hkt
        split at hkt
        · rename_i kann wann wt uann ks pann' bann r₁
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hkt
          obtain ⟨hks, hr₁⟩ := hkt
          let env₁ := extendEnv [(r, v)] env
          have hxs₁ : List.Forall₂ (fun x o => env₁.lookup x = some (ptrOf o)) xs objs :=
            forall₂_imp hxs fun x hx o l => by
              rw [ConvInt.lookup_one_other (fun e => hr (e ▸ List.mem_map_of_mem hx))]; exact l
          obtain ⟨ps, h1, h2, h3⟩ := killsOf_pairs hks hxs₁
          have nodup : (ps.map (·.2.1)).Nodup := by
            have := mem.apart
            rw [← h2] at this
            rw [show ps.map (·.2.1) = (ps.map (·.2)).map (·.1) by simp]
            exact List.Pairwise.map _ (fun a b h => h.1) (List.pairwise_map.mpr (List.pairwise_map.mp this))
          obtain ⟨m₁, tasks, out₁, next₁, last₁, dead₁⟩ := kills_tasks (file := file) (labels := labels)
            (env := env₁) (k := .strongBind (.mk wann (.base (none, wt)))
              (.mk pann' (.pure (.mk bann () (.sym r₁)))) env₁ :: k) ps m' h3 nodup
            (fun q hq => live q.2 (h2 ▸ List.mem_map_of_mem hq))
          rw [h1] at tasks
          have all := Interleave.unseq_runs file labels (annots := uann) (es := ks) (env := env₁)
            (by simpa using tasks) (by intro x hx a ha; simp at hx; obtain ⟨_, _, rfl⟩ := hx; simp at ha)
          have noAcc : ((List.range ps.length).map fun i => (i, (.unit : Val), ([] : List Access))).flatMap
              (·.2.2) = [] := by
            induction (List.range ps.length) with
            | nil => rfl
            | cons _ _ ih => simp
          rw [noAcc] at all
          have reserve₁ : Reserve f m₁ := by
            refine ⟨fun d hd => ?_, by rw [last₁]; exact reserve.aligned, by rw [last₁]; exact reserve.room⟩
            rw [next₁]
            rcases dead₁ d hd with hd | hd
            · exact reserve.dead d hd
            · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
              exact hid q.2 (h2 ▸ List.mem_map_of_mem hq)
          refine ⟨focusMemory pann' m₁, [.annotations []], [], by simp [out₁], reserve₁.focus pann',
            .inr rfl, ?_⟩
          refine (CallLocal.bind rann r rt v _ env k m').trans ?_
          refine (CallLocal.sequence kann _ _ _ env₁ k m').trans ?_
          refine all.trans ?_
          refine (annotations_sbind _ (bs := []) (by simp [matchPattern]) _ env₁ k m₁).trans ?_
          have hr' : (extendEnv [] env₁).lookup r₁ = some v := by
            rw [lookup_nil, ReturnLit.lookup_key hr₁]; exact ConvInt.lookup_one rfl
          exact CallLocal.pure pann' (fun _ => .sym hr') (.annotations [] :: k) m₁
        · cases hkt
    · cases h
  · cases h

/-- The argument objects, then the call. -/
theorem rest_prepared {pty p g : Sym} {cs : List Ctype} (hcs : ∀ c ∈ cs, retKind c = some true) :
    ∀ (as : List Sym) (i : Nat) (xs : List Sym) (e : EE) (env : Env) (k : List Frame)
      (m : Mem.Concrete.State) (fuel : Nat) (objs : List (Int × Int)) (ns₀ ns : List Int),
    rest file pty p as i xs e = true → cs.length = i + as.length →
    env.lookup p = some (fp g) → env.lookup pty = some (ctypes cs) →
    List.Forall₂ (fun a n => env.lookup a = some (IntExpr.spec n) ∧ IntRange n) as ns →
    List.Forall₂ (fun x o => env.lookup x = some (ptrOf o)) xs objs →
    ArgsMem m objs ns₀ → Reserve (fuel + as.length) m →
    Prepared (file := file) (labels := labels) fuel g (ns₀ ++ ns) ⟨.effectExpr e env, k, m⟩ k m.stdout
  | [], i, xs, e, env, k, m, fuel, objs, ns₀, ns, h, _, hp, _, hns, hxs, mem, hb => by
    cases hns
    simpa using callTail_prepared (file := file) (labels := labels) h env k m hp hxs mem hb
  | a :: as, i, xs, e, env, k, m, fuel, objs, ns₀, ns, h, hlen, hp, hpty, hns, hxs, mem, hb => by
    simp only [rest] at h
    cases hstep : restStep e with
    | none => simp [hstep] at h
    | some step =>
      obtain ⟨x, la, ct⟩ := step
      obtain ⟨ann, xann, xbt, rfl⟩ := restStep_spec hstep
      simp only [hstep, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hx, hla⟩, hct⟩ := h
      · have hxp : x.key ≠ p.key := fun e => hx (by simp [e])
        have hxpty : x.key ≠ pty.key := fun e => hx (by simp [e])
        have hxas : x.key ∉ as.map (·.key) := fun e => hx (by
          obtain ⟨b, hb, hk⟩ := List.mem_map.mp e
          exact List.mem_map.mpr ⟨b, by simp [hb], hk⟩)
        have hxxs : x.key ∉ xs.map (·.key) := fun e => hx (by
          obtain ⟨b, hb, hk⟩ := List.mem_map.mp e
          exact List.mem_map.mpr ⟨b, by simp [hb], hk⟩)
        cases hns with
        | cons hn hns =>
          rename_i n ns'
          obtain ⟨c, hci⟩ : ∃ c, cs[i]? = some c := by
            refine ⟨cs[i]'(by simp at hlen; omega), ?_⟩
            simp
          have hc := hcs c (List.mem_of_getElem? hci)
          obtain ⟨m₁, ys, out₁, slot₁, reserve₁, next₁, last₁, keep₁, r₁⟩ := letArgAt_local
            (fuel := fuel + as.length) (file := file) (labels := labels) hla env
            (.strongBind (.mk xann (.base (some x, xbt))) ct env :: k) m hpty hci hc hn.1 hn.2
            hb.budget.room hb.budget.fresh (by simpa [Nat.add_assoc] using hb)
          let o : Int × Int := (m.nextId, nextIntAddress m)
          let env₁ := extendEnv [(x, ptrOf o)] env
          have pre := (CallLocal.sequence ann _ la ct env k m).trans
            (r₁.trans (annotations_sbind ys (bs := [(x, ptrOf o)]) rfl ct env k m₁))
          have mem₁ := mem.snoc (n := n) hb.aligned keep₁ slot₁ next₁ last₁
          have hp₁ : env₁.lookup p = some (fp g) := by
            rw [ConvInt.lookup_one_other (Ne.symm hxp)]; exact hp
          have hpty₁ : env₁.lookup pty = some (ctypes cs) := by
            rw [ConvInt.lookup_one_other (Ne.symm hxpty)]; exact hpty
          have hns₁ : List.Forall₂ (fun a n => env₁.lookup a = some (IntExpr.spec n) ∧ IntRange n) as ns' :=
            forall₂_imp hns fun a' ha' n' l => by
              rw [ConvInt.lookup_one_other (fun e => hxas (e ▸ List.mem_map_of_mem ha'))]; exact l
          have hxs₁ : List.Forall₂ (fun x o => env₁.lookup x = some (ptrOf o)) (xs ++ [x]) (objs ++ [o]) :=
            forall₂_snoc (forall₂_imp hxs fun x' hx' o' l => by
              rw [ConvInt.lookup_one_other (fun e => hxxs (e ▸ List.mem_map_of_mem hx'))]; exact l)
              (ConvInt.lookup_one rfl)
          have r := rest_prepared hcs as (i + 1) (xs ++ [x]) ct env₁ (.annotations ys :: k) m₁ fuel
            (objs ++ [o]) (ns₀ ++ [n]) ns' hct (by simp at hlen; omega) hp₁ hpty₁ hns₁ hxs₁ mem₁ reserve₁
          rw [out₁] at r
          simpa using (r.annotations ys).pre pre

/-- The arity and function-type guards pass. -/
theorem guards_prepared {fuel : Nat} {fty pty vs p : Sym} {as : List Sym} {e : EE}
    (h : guards file fty pty vs p as e = true) {g : Sym} (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {cs : List Ctype} {frt : Ctype} {ns : List Int}
    (hp : env.lookup p = some (fp g)) (hpty : env.lookup pty = some (ctypes cs))
    (hcs : ∀ c ∈ cs, retKind c = some true) (hlen : cs.length = as.length)
    (hvs : env.lookup vs = some .false) (hfty : env.lookup fty = some (.ctype frt))
    (hfrt : retKind frt = some true)
    (hns : List.Forall₂ (fun a n => env.lookup a = some (IntExpr.spec n) ∧ IntRange n) as ns)
    (hb : Reserve (fuel + as.length) m) :
    Prepared (file := file) (labels := labels) fuel g ns ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  unfold guards at h
  split at h
  · rename_i _ i1ann c1a c1b c1c len c1d pty₁ c1e n u1 i2ann c2a c2b vs₁ c2c c2d c2e rty c2f fty₁
      u2 r
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hpty₁, hvs₁, hfty₁, rfl⟩, hlen'⟩, hrty⟩, hrest⟩ := h
    let m₁ := focusMemory i1ann m
    let m₂ := focusMemory i2ann m₁
    have T : Touched m m₂ := (touched_seq i1ann m).trans (touched_seq i2ann m₁)
    have o := rest_prepared (file := file) (labels := labels) hcs as 0 [] _ env k m₂ fuel [] [] ns
      hrest (by simp [hlen]) hp hpty hns .nil (ArgsMem.nil m₂) (hb.touched T)
    rw [T.stdout] at o
    simp only [List.nil_append] at o
    refine o.pre ?_
    exact (CallArena.effect_if i1ann false
      (CallArena.of_eval fun tags => CallManyEval.length_eval hlen'
        ((ReturnLit.lookup_key hpty₁).trans hpty) (by simp [hlen]) tags) k m).trans
      (CallArena.effect_if i2ann false (variadic_check hrty hfrt
        ((ReturnLit.lookup_key hvs₁).trans hvs) ((ReturnLit.lookup_key hfty₁).trans hfty)) k m₁)
  · cases h

theorem forall₂_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ (fun a b => f a = g b) l₁ l₂) : l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem forall₂_zip {α β γ : Type} (f : β → γ) :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      List.Forall₂ (fun a b => (a, f b) ∈ l₁.zip (l₂.map f) ∧ b ∈ l₂) l₁ l₂
  | [], [], _ => .nil
  | a :: l₁, b :: l₂, h => by
    refine .cons (by simp) (forall₂_imp (forall₂_zip f (by simpa using h)) fun x _ y hm => ?_)
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
    exact ⟨.inr hm.1, .inr hm.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The whole caller-side prefix of a call `g(n₁, …, nₖ)`** is a local trace to the scheduled
call, the argument objects allocated and initialized. -/
theorem argSite_prepared {fuel : Nat} {e : EE} {g : Sym} {ns : List Int}
    (hs : argSite file e = some (g, ns)) {loc : Loc} {attrs : Attributes} {rty : Ctype}
    {params : List (Option Sym × Ctype)} {proto : Bool}
    (hinfo : file.funInfo.lookup g = some (loc, attrs, rty, params, false, proto))
    (hr : retKind rty = some true) (hps : ∀ q ∈ params, retKind q.2 = some true)
    (hlen : params.length = ns.length)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hb : Reserve (fuel + ns.length) m) :
    Prepared (file := file) (labels := labels) fuel g ns ⟨.effectExpr e env, k, m⟩ k m.stdout := by
  unfold argSite at hs
  split at hs
  · rename_i _ eA pA pA1 pA2 p pT pA3 fA fty fT psA pty psT vA vs vT prA pr prT aps uA t1 ts gd
    cases hfn : fnTask t1 with
    | none => simp [hfn] at hs
    | some g' =>
    cases hbs : baseSyms aps with
    | none => simp [hfn, hbs] at hs
    | some as =>
    cases hlits : argLits file ts with
    | none => simp [hfn, hbs, hlits] at hs
    | some ns' =>
    simp only [hfn, hbs, hlits] at hs
    split at hs
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at cond
      obtain ⟨⟨⟨⟨-, -, hasl⟩, nodup⟩, ranges⟩, hgd⟩ := cond
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hlit := argLits_spec hlits
      let info := fnInfo g' rty params false proto
      let val : EE → Val := fun e => if isSseq e then info else
        match argLit file e with
        | some n => IntExpr.spec n
        | none => .unit
      obtain ⟨hpure, hread⟩ := CallArg.fnTask_spec (file := file) (labels := labels) hfn (fun _ => True)
        hinfo env
      have hs1 : isSseq t1 = true := by simpa [CallArg.isPure] using hpure
      have tasks : ∀ e ∈ t1 :: ts, ReadTask (file := file) (labels := labels) (fun _ => True) env e
          (val e) := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simpa [val, hs1] using hread
        · obtain ⟨n, -, hn⟩ := forall₂_mem_left hlit he
          obtain ⟨hp', -, hr'⟩ := CallArg.argLit_spec (file := file) (labels := labels) hn (fun _ => True) env
          have : isSseq e = false := by simpa [CallArg.isPure] using hp'
          simpa [val, this, hn] using hr'
      have hvals : (t1 :: ts).map val = info :: ns'.map IntExpr.spec := by
        simp only [List.map_cons, val, hs1, ↓reduceIte, List.cons.injEq, true_and]
        refine forall₂_map_eq (forall₂_imp hlit fun e he n hn => ?_)
        obtain ⟨hp', -, -⟩ := CallArg.argLit_spec (file := file) (labels := labels) hn (fun _ => True) env
        have : isSseq e = false := by simpa [CallArg.isPure] using hp'
        simp [this, hn]
      let HEAD : Pattern Sym := .mk pA1 (.ctor .tuple [.mk pA2 (.base (some p, pT)),
        .mk pA3 (.ctor .tuple [.mk fA (.base (some fty, fT)), .mk psA (.base (some pty, psT)),
          .mk vA (.base (some vs, vT)), .mk prA (.base (some pr, prT))])])
      let PAT : Pattern Sym := .mk pA (.ctor .tuple (HEAD :: aps))
      obtain ⟨xs, m₁, -, tch₁, run⟩ := LoadTask.unseq_reads (file := file) (labels := labels)
        (k := .strongBind PAT gd env :: k) (annots := uA) (fun _ => True) (fun _ _ _ _ => trivial) val
        tasks m trivial
      rw [hvals] at run
      let lits := ns'.map IntExpr.spec
      let headBs : Bindings := [(p, fp g'), (fty, .ctype rty),
        (pty, .list .ctype (params.map fun q => .ctype q.2)), (vs, boolean false), (pr, boolean proto)]
      let bs : Bindings := headBs ++ as.zip lits
      have hlits_len : as.length = lits.length := by simp [lits, hasl]
      have hm : matchPattern PAT (.tuple (info :: lits)) = some bs := by
        have := baseSyms_match hbs hlits_len
        simp [PAT, HEAD, info, fnInfo, matchPattern, matchPatterns, this, bind, Option.bind, bs, headBs]
      let env₁ := extendEnv bs env
      have pre : LocalReaches file labels false
          ⟨.effectExpr (.mk eA (.sseq PAT (.mk uA (.unseq (t1 :: ts))) gd)) env, k, m⟩
          ⟨.effectExpr gd env₁, .annotations xs :: k, m₁⟩ :=
        (CallLocal.sequence eA PAT _ gd env k m).trans
          (run.trans (annotations_sbind xs hm gd env k m₁))
      have keys : (bs.map (·.1.key)).Nodup := by
        have hz : (as.zip lits).map (·.1) = as := List.map_fst_zip (le_of_eq hlits_len)
        have : bs.map (·.1.key) = (p :: fty :: pty :: vs :: pr :: as).map (·.key) := by
          simp only [bs, headBs, List.map_cons, List.cons_append, List.nil_append]
          rw [show (as.zip lits).map (·.1.key) = ((as.zip lits).map (·.1)).map (·.key) by simp, hz]
        rw [this]; exact nodup
      have look : ∀ {s : Sym} {v : Val}, (s, v) ∈ bs → env₁.lookup s = some v :=
        fun h => lookup_extend_mem keys h rfl
      have hct : (.list .ctype (params.map fun q => .ctype q.2) : Val) = ctypes (params.map (·.2)) := by
        simp [ctypes, List.map_map]
      have hns : List.Forall₂ (fun a n => env₁.lookup a = some (IntExpr.spec n) ∧ IntRange n) as ns' :=
        forall₂_imp (forall₂_zip IntExpr.spec hasl) fun a _ n hm' =>
          ⟨look (List.mem_append_right _ hm'.1), (ranges n hm'.2).1, (ranges n hm'.2).2⟩
      have lp : env₁.lookup p = some (fp g') := look (by simp [bs, headBs])
      have lfty : env₁.lookup fty = some (.ctype rty) := look (by simp [bs, headBs])
      have lpty : env₁.lookup pty = some (ctypes (params.map (·.2))) := by
        rw [← hct]; exact look (by simp [bs, headBs])
      have lvs : env₁.lookup vs = some (boolean false) := look (by simp [bs, headBs])
      have o := guards_prepared (fuel := fuel) (file := file) (labels := labels) hgd env₁
        (.annotations xs :: k) m₁ lp lpty
        (fun c hc => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc; exact hps q hq)
        (by simp [hlen, hasl]) lvs lfty hr hns (by rw [hasl]; exact hb.touched tch₁)
      rw [tch₁.stdout] at o
      exact (o.annotations xs).pre pre
    · cases hs
  · cases hs

end Silmaril.Compile.Core.Verified.CallMany
