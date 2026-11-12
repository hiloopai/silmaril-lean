module

public import Silmaril.Compiler.Core.Verified.PrintfStd.Defs
public import Silmaril.Compiler.Core.Verified.Globals.Defs

/-! # Startup with string literals

Cerberus elaborates each string literal of a C file to a global definition of Core

```
create_readonly(Ivalignof(char[n]), char[n], Specified(array(Specified(conv_int(char, c₁)), …, Specified(0))))
```

that the dynamics runs before `main` (`Dynamics.initial`, the `.globals` control), binding the
literal's symbol to the pointer to the new read-only object. `lits file (definitions file) = some ls`
when every global definition is such a literal, with its characters in `0 … 127` and its last
character 0 (the characters fold: `Fold.eval`, constant folding of the literal's integer
constants); `ls` lists the literals and their characters.

`initial_reaches_body`: from the initial state of such a file whose `main` is a procedure without
parameters, the dynamics reaches `main`'s body in an environment in which every literal points to
a string object holding its characters (`LitEnv`), under one annotation frame, with empty stdout,
nothing killed, and the last allocation far above 0 (room for every later allocation of the
fragment).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StrLit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold (WVal WEnv PExp Doc)
open StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-! ## The recogniser -/

/-- A literal's character: a folded `Specified` integer. -/
def litChar (file : Doc) (p : PExp) : Option Int :=
  match Fold.eval file Return.fuel ∅ p with
  | some (.loaded (.specified (.integer c))) => some c
  | _ => none

/-- `char[n]`. -/
def isCharArr (n : Int) : Ctype → Bool
  | .mk _ (.array (.mk _ (.basic (.integer .char))) (some n')) => n' == n
  | _ => false

/-- A string's characters: each in `0 … 127`, the last one 0, at most `2²⁰` of them. -/
def strChars (cs : List Int) : Bool :=
  cs.getLast? == some 0 && cs.all (fun c => 0 ≤ c && c ≤ 127) && cs.length ≤ 2 ^ 20

/-- A string literal's definition: its characters. -/
def strLit (file : Doc) : EExp → Option (List Int)
  | .mk _ (.action (.mk .pos (.mk _ _ (.createReadOnly
      (.mk _ _ (.ctor .ivAlignof [.mk _ _ (.val (.ctype t1))]))
      (.mk _ _ (.val (.ctype t2)))
      (.mk _ _ (.ctor .specified [.mk _ _ (.ctor .array elems)])) _)))) =>
      match elems.mapM (litChar file) with
      | some cs =>
          if isCharArr cs.length t1 && isCharArr cs.length t2 && strChars cs then some cs else none
      | none => none
  | _ => none

/-- The global definitions of a file, in the order `Dynamics.initial` runs them. -/
def definitions (file : Doc) : List (Sym × EExp) :=
  file.globs.filterMap fun (sym, decl) => match decl with
    | .definition _ e => some (sym, e)
    | .declaration _ => none

/-- Every definition is a string literal: the literals and their characters. -/
def lits (file : Doc) : List (Sym × EExp) → Option (List (Sym × List Int))
  | [] => some []
  | (x, e) :: ds => (strLit file e).bind fun cs => (lits file ds).map fun ls => (x, cs) :: ls

/-- The literals of a file whose global definitions are all string literals, with distinct
symbols, at most `2²⁰` of them. -/
def litsOf (file : Doc) : Option (List (Sym × List Int)) :=
  if ((definitions file).map fun d => d.1.key).Nodup ∧ (definitions file).length ≤ 2 ^ 20 then
    lits file (definitions file)
  else none

/-! ## The literals at run time -/

/-- Every literal points to a string object holding its characters, at an address in the
address space. -/
def LitEnv (ls : List (Sym × List Int)) (env : Env) (m : Mem.Concrete.State) : Prop :=
  ∀ x cs, (x, cs) ∈ ls → ∃ id addr,
    env.lookup x = some (.object (.pointer (.allocated id addr))) ∧ StrObj m id addr cs ∧
    0 < addr ∧ addr < 2 ^ 48

theorem LitEnv.keeps {ls : List (Sym × List Int)} {env : Env} {m m' : Mem.Concrete.State}
    (h : LitEnv ls env m) (k : Keeps m m') : LitEnv ls env m' := by
  intro x cs hx
  obtain ⟨id, addr, look, obj, h0, h1⟩ := h x cs hx
  exact ⟨id, addr, look, obj.keeps k, h0, h1⟩

theorem LitEnv.insert {ls : List (Sym × List Int)} {env : Env} {m : Mem.Concrete.State}
    (h : LitEnv ls env m) (s : Sym) (v : Val) (hx : ∀ y ∈ ls, s.key ≠ y.1.key) :
    LitEnv ls (env.insert s v) m := by
  intro x cs hm
  obtain ⟨id, addr, look, rest⟩ := h x cs hm
  exact ⟨id, addr, by rw [Map.lookup_insert_of_key_ne _ _ (fun e => hx (x, cs) hm e.symm)]; exact look,
    rest⟩

/-- Bindings of other symbols keep the literals. -/
theorem LitEnv.extend {ls : List (Sym × List Int)} {env : Env} {m : Mem.Concrete.State}
    (h : LitEnv ls env m) (xs : Bindings) (hx : ∀ x ∈ xs, ∀ y ∈ ls, x.1.key ≠ y.1.key) :
    LitEnv ls (extendEnv xs env) m := by
  induction xs with
  | nil => simpa [extendEnv] using h
  | cons x xs ih =>
    obtain ⟨s, v⟩ := x
    have := (ih fun y hy => hx y (List.mem_cons_of_mem _ hy)).insert s v
      (hx (s, v) List.mem_cons_self)
    simpa [extendEnv, List.foldr] using this


theorem lits_chars {file : Doc} : ∀ {ds : List (Sym × EExp)} {ls : List (Sym × List Int)},
    lits file ds = some ls → ∀ x cs, (x, cs) ∈ ls → strChars cs = true := by
  intro ds
  induction ds with
  | nil => intro ls h; simp [lits] at h; subst h; simp
  | cons d ds ih =>
    obtain ⟨y, e⟩ := d
    intro ls h x cs hx
    simp only [lits] at h
    cases he : strLit file e with
    | none => simp [he] at h
    | some cs' =>
      cases hd : lits file ds with
      | none => simp [he, hd] at h
      | some ls' =>
        simp only [he, hd, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with hx | hx
        · cases hx
          unfold strLit at he
          split at he
          · split at he
            · split at he
              · rename_i hif; cases he
                simp only [Bool.and_eq_true] at hif
                exact hif.2
              · cases he
            · cases he
          · cases he
        · exact ih hd x cs hx

/-! ## One literal -/

section Literal
variable {file : Program} {labels : Labels}

open SeqReach (PureEval located_next_reaches pure_value)

theorem strLit_inv {e : EExp} {cs : List Int} (h : strLit file e = some cs) :
    ∃ ann l u a1 u1 a2 u2 t1 a3 u3 t2 a4 u4 a5 u5 elems pref,
      e = .mk ann (.action (.mk .pos (.mk l u (.createReadOnly
        (.mk a1 u1 (.ctor .ivAlignof [.mk a2 u2 (.val (.ctype t1))]))
        (.mk a3 u3 (.val (.ctype t2)))
        (.mk a4 u4 (.ctor .specified [.mk a5 u5 (.ctor .array elems)])) pref)))) ∧
      elems.mapM (litChar file) = some cs ∧ isCharArr cs.length t1 = true ∧
      isCharArr cs.length t2 = true ∧ strChars cs = true := by
  unfold strLit at h
  split at h
  · split at h
    · rename_i cs' hm
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hm, hc.1.1, hc.1.2, hc.2⟩
      · cases h
    · cases h
  · cases h

theorem isCharArr_inv {n : Int} {t : Ctype} (h : isCharArr n t = true) :
    ∃ a b, t = charArr a b n := by
  unfold isCharArr at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    exact ⟨_, _, rfl⟩
  · cases h

theorem litChar_eval {p : PExp} {c : Int} (h : litChar file p = some c) :
    Fold.eval file Return.fuel ∅ p = some (.loaded (.specified (.integer c))) := by
  unfold litChar at h
  split at h
  · rename_i heq; cases h; exact heq
  · cases h

theorem elems_eval (env : Env) : ∀ (elems : List PE) (cs : List Int),
    elems.mapM (litChar file) = some cs →
    List.Forall₂ (fun p v => PureEval file labels p env v) elems
      (cs.map fun c => .loaded (.specified (.integer c)))
  | [], cs, h => by simp at h; subst h; exact .nil
  | p :: ps, cs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs, rfl⟩ := h
    refine .cons ?_ (elems_eval env ps cs' hcs)
    intro k m
    exact Fold.eval_reaches_sub file labels Return.fuel ∅ p _ (litChar_eval hc) env (Fold.EnvSub.empty env) k m

/-- A constructor over operands that evaluate, whose primitive succeeds. -/
theorem ctor_pe {c : Ctor} {p : PE} {ps : List PE} {v w : Val} {vs : List Val} {env : Env}
    (hp : PureEval file labels p env v)
    (hps : List.Forall₂ (fun p v => PureEval file labels p env v) ps vs)
    (hprim : ∀ tags, primitive (.ctor c) (v :: vs) tags = .ok w) (ann : List Annot) (u : Unit) :
    PureEval file labels (.mk ann u (.ctor c (p :: ps))) env w := by
  intro k m
  exact (ExitCall.lift file labels (ExitCall.ra_ctor file labels ann u c p ps) (ExitCall.plain_pureExpr _ _)).trans
    ((hp _ _).trans ((CallReach.arguments_reaches hps (.ctor c) [] v k m).trans
      (PureEval.apply_reaches file (op := .ctor c) trivial (by simpa using hprim _))))

/-- Entering `create_readonly(a, t, v)`: its first operand, under the focus. -/
theorem createReadOnly_enter (ann : List Annot) (l : Loc) (u : Unit) (p q r : PE) (pref : Prefix)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.createReadOnly p q r pref))))) env, k, m⟩
      ⟨.pureExpr p env, .arguments (.memory (.createReadOnly pref)) [] [q, r] env :: k,
        SeqReach.focusMemory ann m⟩ := by
  apply located_next_reaches ann (by intro o; simp)
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (SeqReach.focusMemory ann m).currentLocation == m.currentLocation then
    Request.next (.pureExpr p env) (.arguments (.memory (.createReadOnly pref)) [] [q, r] env :: k)
    else .next (.setLocation (SeqReach.focusMemory ann m).currentLocation (.pureExpr p env))
      (.arguments (.memory (.createReadOnly pref)) [] [q, r] env :: k)) with
    | .next (.jumping s vs env) frames => jump labels s vs env frames
    | r => r) = _
  by_cases eq : (SeqReach.focusMemory ann m).currentLocation == m.currentLocation <;> simp [eq]

theorem mapM_comp_ok {α β γ ε : Type} (f : α → Except ε β) (g : γ → α) (h : γ → β)
    (hf : ∀ x, f (g x) = .ok (h x)) (l : List γ) : List.mapM (f ∘ g) l = .ok (l.map h) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapM_cons, Function.comp, hf, ih, List.map_cons]
    rfl

theorem focus_fields (ann : List Annot) (m : Mem.Concrete.State) :
    (SeqReach.focusMemory ann m).nextId = m.nextId ∧
      (SeqReach.focusMemory ann m).lastAddress = m.lastAddress ∧
      (SeqReach.focusMemory ann m).dead = m.dead ∧ (SeqReach.focusMemory ann m).stdout = m.stdout := by
  unfold SeqReach.focusMemory
  split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem lml (b : List Annot) (cs : List Int) :
    loadedMemoryList (charTy b) (cs.map fun c => .specified (.integer c)) =
      .ok (cs.map (Mem.Concrete.MemoryValue.integer .char)) := by
  induction cs with
  | nil => simp [loadedMemoryList, pure, Except.pure]
  | cons c cs ih =>
    simp [loadedMemoryList, toMemory, objectMemory, intType, ih, pure, Except.pure, bind, Except.bind]

theorem strChars_spec {cs : List Int} (h : strChars cs = true) :
    cs ≠ [] ∧ (∀ c ∈ cs, 0 ≤ c ∧ c < 128) ∧ cs.length ≤ 2 ^ 20 := by
  simp only [strChars, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, fun c hc => ?_, h3⟩
  · intro e; subst e; simp at h1
  · have := h2 c hc; omega

/-- **A string literal's definition** creates its string object just below the last
allocation. -/
theorem lit_reaches {e : EExp} {cs : List Int} (h : strLit file e = some cs) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (hdead : m.dead = [])
    (room : (cs.length : Int) < m.lastAddress) :
    ∃ m', StrObj m' m.nextId (m.lastAddress - cs.length) cs ∧ Keeps m m' ∧
      m'.lastAddress = m.lastAddress - cs.length ∧ m'.dead = m.dead ∧ m'.stdout = m.stdout ∧
      ReturnConst.Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (m.lastAddress - cs.length)))), k, m'⟩ := by
  obtain ⟨ann, l, u, a1, u1, a2, u2, t1, a3, u3, t2, a4, u4, a5, u5, elems, pref, rfl, hm, ht1, ht2,
    hch⟩ := strLit_inv h
  obtain ⟨A1, B1, rfl⟩ := isCharArr_inv ht1
  obtain ⟨A2, B2, rfl⟩ := isCharArr_inv ht2
  obtain ⟨hne, hc, -⟩ := strChars_spec hch
  obtain ⟨c0, cs', rfl⟩ : ∃ c0 cs', cs = c0 :: cs' := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c0 cs' => exact ⟨c0, cs', rfl⟩
  cases elems with
  | nil => simp at hm
  | cons p ps =>
  have hF := elems_eval (labels := labels) env (p :: ps) _ hm
  simp only [List.map_cons] at hF
  cases hF with
  | cons hp hps =>
  cases u2; cases u3
  have hA : PureEval file labels (.mk a1 u1 (.ctor .ivAlignof [.mk a2 () (.val (.ctype
      (charArr A1 B1 ((c0 :: cs').length : Int))))])) env (.object (.integer 1)) :=
    ctor_pe (pure_value a2 _ env) .nil (fun tags => by
      have hl := layout_charArr tags A1 B1 (c0 :: cs').length
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hl
      simp [primitive, Mem.Concrete.alignment, runtimeValue, integer, pure, Except.pure, hl, bind,
        Except.bind]) a1 u1
  have hArr : PureEval file labels (.mk a5 u5 (.ctor .array (p :: ps))) env
      (.object (.array ((c0 :: cs').map fun c => .specified (.integer c)))) :=
    ctor_pe hp hps (fun tags => by
      simp [primitive, pure, Except.pure, bind, Except.bind]
      rw [mapM_comp_ok _ _ (fun c => LoadedValue.specified (ObjectValue.integer c)) ?hf]
      · intro x; rfl) a5 u5
  have hV := ctor_pe (c := .specified)
    (w := .loaded (.specified (.array ((c0 :: cs').map fun c => .specified (.integer c))))) hArr .nil (fun tags => by simp [primitive, pure, Except.pure]) a4 u4
  have hT := pure_value (file := file) (labels := labels) a3 (.ctype (charArr A2 B2 ((c0 :: cs').length : Int))) env
  clear hp hps hArr hm ht1 ht2 hch
  generalize c0 :: cs' = cs at *
  let M := SeqReach.focusMemory ann m
  obtain ⟨fn, fl, fd, fo⟩ := focus_fields ann m
  let tags : Mem.Concrete.Tags := ⟨file.tagDefs, M.enumTypes⟩
  obtain ⟨m', hcr, hstr, hkeep, hlast, -, hdead', hout⟩ := createReadOnly_str tags M A2 B2 cs hne hc
    (by rw [fl]; exact room) (by rw [fd, hdead]; simp) pref
  have fn' : M.nextId = m.nextId := fn
  have fl' : M.lastAddress = m.lastAddress := fl
  rw [fn', fl'] at hcr hstr
  rw [fl'] at hlast
  obtain ⟨r, hr⟩ : ∃ r, request file labels ⟨.apply (.memory (.createReadOnly pref))
      [.object (.integer 1), .ctype (charArr A2 B2 (cs.length : Int)),
        .loaded (.specified (.array (cs.map fun c => .specified (.integer c))))], k, M⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.unatomic, bind, Except.bind, pure, Except.pure] at hr'
  rw [lml] at hr'
  simp only at hr'
  erw [hcr] at hr'
  simp only at hr'
  have hmem := Actions.memory_reaches (file := file) (labels := labels) (by intro o h; cases h)
    (hr.trans hr'.symm)
  refine ⟨m', hstr, (PrintfStd.keeps_focus ann m).trans hkeep, by rw [hlast], by rw [hdead', fd],
    by rw [hout, fo], ?_⟩
  exact (createReadOnly_enter ann l u _ _ _ pref env k m).trans ((hA _ _).trans
    ((CallReach.arguments_reaches (.cons hT (.cons hV .nil)) (.memory (.createReadOnly pref)) [] _ k M).trans
      hmem))

theorem globalResult_step (x : Sym) (ds : List (Sym × EE)) (args : List String) (env : Env)
    (ls : Labels) (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels ⟨.value v, .globalResult x ds args env ls :: k, m⟩
      ⟨.globals ds args (env.insert x v), k, m⟩ :=
  SeqReach.next_reaches (by intro o; simp) (by simp [request, requestAux, awaitsScheduling])

/-- The literal definitions run in order: each literal points to its string object. -/
theorem lits_reaches (args : List String) : ∀ (ds : List (Sym × EExp)) (ls : List (Sym × List Int)),
    lits file ds = some ls → (ds.map fun d => d.1.key).Nodup →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State),
    m.dead = [] → 2 ^ 47 + 8 + 2 ^ 20 * (ds.length : Int) ≤ m.lastAddress →
    m.lastAddress ≤ 281474976710655 →
    ∃ env' m', m'.stdout = m.stdout ∧ m'.dead = [] ∧ 2 ^ 47 + 8 ≤ m'.lastAddress ∧ Keeps m m' ∧
      (∀ x v, (∀ d ∈ ds, d.1.key ≠ x.key) → env.lookup x = some v → env'.lookup x = some v) ∧
      LitEnv ls env' m' ∧
      ReturnConst.Reaches file labels ⟨.globals ds args env, k, m⟩ ⟨.globals [] args env', k, m'⟩
  | [], ls, h, _, env, k, m, hd, room, _ => by
    simp only [lits, Option.some.injEq] at h
    subst h
    exact ⟨env, m, rfl, hd, by simp at room; omega, Keeps.refl m, fun _ _ _ h => h,
      by intro x cs hx; simp at hx, .refl⟩
  | (x, e) :: ds, ls, h, nd, env, k, m, hd, room, top => by
    simp only [lits] at h
    cases he : strLit file e with
    | none => simp [he] at h
    | some cs =>
      cases hds : lits file ds with
      | none => simp [he, hds] at h
      | some ls' =>
        simp only [he, hds, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have nd' : (ds.map fun d => d.1.key).Nodup := (List.nodup_cons.mp nd).2
        have fresh : ∀ d ∈ ds, d.1.key ≠ x.key := by
          intro d hd' e'
          exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨d, hd', e'⟩)
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, hch⟩ := strLit_inv he
        obtain ⟨-, -, hlen⟩ := strChars_spec hch
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at room
        have hlen' : (cs.length : Int) ≤ 2 ^ 20 := by exact_mod_cast hlen
        obtain ⟨m1, hstr, hk1, hl1, hd1, ho1, r1⟩ := lit_reaches (labels := labels) he env
          (.globalResult x ds args env (Map.ofList (saves e).reverse) :: k) m hd (by omega)
        let ptr : Val := .object (.pointer (.allocated m.nextId (m.lastAddress - cs.length)))
        obtain ⟨env', m', o', d', l', k', look, lit, r'⟩ := lits_reaches args ds ls' hds nd'
          (env.insert x ptr) k m1 (by rw [hd1, hd]) (by rw [hl1]; omega) (by rw [hl1]; omega)
        refine ⟨env', m', by rw [o', ho1], d', l', hk1.trans k', ?_, ?_, ?_⟩
        · intro y v hy hv
          refine look y v (fun d hd => hy d (List.mem_cons_of_mem _ hd)) ?_
          rw [Map.lookup_insert_of_key_ne _ _ (fun h' => hy (x, e) List.mem_cons_self h'.symm)]
          exact hv
        · intro y cs' hy
          rcases List.mem_cons.mp hy with hy | hy
          · cases hy
            exact ⟨m.nextId, m.lastAddress - cs.length, look x ptr fresh (by simp),
              hstr.keeps k', by omega, by omega⟩
          · exact lit y cs' hy
        · exact (Globals.global_reaches x e ds args env k m).trans
            (r1.trans ((globalResult_step x ds args env _ ptr k m1).trans r'))

/-- The `errno` startup from any memory with room below its last allocation: it keeps every
object above, and drops the frames below it. -/
theorem startup_errno_keeps (c : Control) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Keeps m m' ∧ m'.dead = m.dead ∧
      m'.lastAddress = Mem.Concrete.nextIntAddress m ∧
      ReturnConst.Reaches file labels ⟨.startup c, k, m⟩ ⟨c, [.annotations xs], m'⟩ := by
  have bnd := Globals.nextIntAddress_bounds m
  let ptr : Val := .object (.pointer (.allocated m.nextId (Mem.Concrete.nextIntAddress m)))
  let m₁ := Actions.created (.other "errno") [] m
  have live₁ : Mem.Concrete.LiveInt m₁ m.nextId (Mem.Concrete.nextIntAddress m) :=
    Locals.created_live _ _ m hdead
  have km1 : Keeps m m₁ := by
    have keepW : Keeps m (Mem.Concrete.writeRepresentation (Mem.Concrete.nextIntAddress m)
        (Mem.Concrete.plainBytes (List.replicate 4 none)) m) :=
      (Keeps.refl m).write _ _ (by simp [Mem.Concrete.plainBytes]; omega)
    refine Keeps.updateLast ?_ rfl (le_refl _) _
    refine ⟨keepW.enums, ?_, ?_, ?_, keepW.dead, keepW.bytes, keepW.pbytes⟩
    · show m.nextId ≤ m.nextId + 1; omega
    · show Mem.Concrete.nextIntAddress m ≤ m.lastAddress; omega
    · intro j hj
      show (m.allocations.insert m.nextId _).lookup j = _
      rw [Map.lookup_insert_of_key_ne _ _ (show j ≠ m.nextId by omega)]
  have hcreate : ReturnConst.Reaches file labels ⟨.startup c, k, m⟩ ⟨.value ptr, [.startupStore c], m₁⟩ :=
    Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
      simp only [request, requestAux, awaitsScheduling, memoryRequest]
      simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
        integer, Mem.Concrete.allocate_int _ [] m hpos]
      simp [bind, Except.bind, pure, Except.pure, m₁, Actions.created, ptr])
  obtain ⟨r, hr⟩ : ∃ r, request file labels ⟨.value ptr, [.startupStore c], m₁⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory, ptr,
    show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
    Mem.Concrete.store_int _ [] live₁ (show Mem.Concrete.IntRange 0 by unfold Mem.Concrete.IntRange; omega),
    Mem.Concrete.access_int _ [] live₁, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  let m₂ := Locals.stored m₁ m.nextId (Mem.Concrete.nextIntAddress m) 0
  have hstore : ReturnConst.Reaches file labels ⟨.value ptr, [.startupStore c], m₁⟩
      ⟨.value .unit, [.annotations [⟨none, [], true, Mem.Concrete.nextIntAddress m, 4⟩], .startupEnter c], m₂⟩ :=
    Actions.memory_reaches (by intro o h; cases h) hr
  have km2 : Keeps m m₂ := by
    unfold m₂ Locals.stored
    exact (km1.write _ _ (by simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]; omega)).lastUsed _
  obtain ⟨sn, sl, sd, so⟩ := Globals.stored_same m₁ m.nextId (Mem.Concrete.nextIntAddress m) 0
  refine ⟨{m₂ with currentLocation := .other "Driver.drive"}, [⟨none, [], true, Mem.Concrete.nextIntAddress m, 4⟩],
    ?_, km2.location _, ?_, ?_, hcreate.trans (hstore.trans ?_)⟩
  · change m₂.stdout = m.stdout
    rw [so, Actions.created_stdout]
  · change m₂.dead = m.dead
    rw [sd, Locals.created_dead]
  · change m₂.lastAddress = _
    rw [sl, Locals.created_lastAddress]
  · exact Straight.update_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])

end Literal

/-! ## Startup -/

/-- **Startup with string literals.** -/
theorem initial_reaches_body (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {ls : List (Sym × List Int)} (hls : litsOf file = some ls)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m env xs, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧
      m.stdout = "" ∧ LitEnv ls env m ∧ m.dead = [] ∧ 2 ^ 47 ≤ m.lastAddress ∧
      ReturnConst.Reaches file (Map.ofList (saves body).reverse) s
        ⟨.effectExpr body env, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  let m₀ : Mem.Concrete.State := {enumTypes := enums}
  unfold litsOf at hls
  split at hls
  case isFalse => cases hls
  rename_i hc
  obtain ⟨nd, hlen⟩ := hc
  have hlen' : ((definitions file).length : Int) ≤ 2 ^ 20 := by exact_mod_cast hlen
  obtain ⟨env, m₁, o1, d1, l1, -, -, lit1, r1⟩ := lits_reaches (file := file) (labels := labels) args
    (definitions file) ls hls nd ∅ [] m₀ rfl (by show _ ≤ (281474976710655 : Int); omega)
    (by show (281474976710655 : Int) ≤ 281474976710655; omega)
  have bnd := Globals.nextIntAddress_bounds m₁
  obtain ⟨m₂, xs, o2, k2, d2, l2, r2⟩ := startup_errno_keeps (file := file) (labels := labels)
    (.effectExpr body env) [] m₁ (by omega) (by rw [d1]; simp)
  refine ⟨_, m₂, env, xs, ?_, by rw [o2, o1], lit1.keeps k2, by rw [d2, d1], by rw [l2]; omega,
    r1.trans ((Globals.enter_main_reaches args env [] m₁ main decl).trans r2)⟩
  simp [initial, definitions, main, decl]
  refine ⟨?_, rfl⟩
  congr 1

end Silmaril.Compile.Core.Verified.StrLit
