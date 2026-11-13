module

public import Silmaril.Compiler.Core.Verified.Locals.Defs

/-! # The block of one `int` local, as Core statements

The recognisers of the statements of `{ int x = n; return x; }` and `{ int x = n; }` (see
`Locals`) and their Core runs, from every environment, continuation without boundary and
memory with room for one more `int` object. The store and the load leave access annotation
frames; they float below the statement continuation (`annotations_bind_reaches`) or end at
the enclosing `bound`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Locals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory focusMemory_stdout)
open ConvInt (isConvLoadedInt)
open ReturnLit (Eff NoBoundary ReturnLabel lookup_key)
open Mem.Concrete (LiveInt IntRange nextIntAddress)

variable {file : Program} {labels : Labels}

/-! ## Annotation frames -/

theorem annotations_bind_reaches (xs : List Access) (ann : List Annot) (ty : BaseType) (v : Val)
    (b : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels
      ⟨.value v, .annotations xs :: .strongBind (.mk ann (.base (none, ty))) b env :: k, m⟩
      ⟨.effectExpr b env, .annotations xs :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, matchPattern, extendEnv]

theorem annotations_bound_reaches (xs : List Access) (v : Val) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .annotations xs :: .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem annotations_merge_reaches (xs ys : List Access) (v : Val) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .annotations xs :: .annotations ys :: k, m⟩
      ⟨.value v, .annotations (xs ++ ys) :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem wbind_reaches (ann : List Annot) (t : Sym) (ty : BaseType) (v : Val) (b : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .effectBind (.mk ann (.base (some t, ty))) b env :: k, m⟩
      ⟨.effectExpr b (extendEnv [(t, v)] env), k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, matchPattern]

theorem wseq_reaches (ann : List Annot) (pat : Pattern Sym) (a b : EE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.wseq pat a b)) env, k, m⟩
      ⟨.effectExpr a env, .effectBind pat b env :: k, m⟩ := by
  apply next_reaches <;> simp [request, requestAux, awaitsScheduling]

/-! ## Recognisers -/

/-- `create(Ivalignof(int), int)`. -/
def createInt : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ () (.ctor .ivAlignof
      [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int))))))]))
      (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int))))))) _)))) => true
  | _ => false

/-- `let strong t = bound(pure(n)) in store(int, x, conv_loaded_int(int, t))`: the literal
`n`, an `int`. -/
def storeLit (file : File Codec.wireModel Unit Unit) (x : Sym) : Eff → Option Int
  | .mk _ (.sseq (.mk _ (.base (some t, _)))
      (.mk _ (.bound (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))))))
      (.mk _ (.action (.mk .pos (.mk _ _ (.store false
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
        (.mk _ () (.sym x'))
        (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
          .mk _ () (.sym t')])) .na)))))) =>
      if x'.key = x.key ∧ t'.key = t.key ∧ t.key ≠ x.key ∧ isConvLoadedInt file s = true ∧
        -2147483648 ≤ n ∧ n ≤ 2147483647 then some n else none
  | _ => none

/-- `kill(int, x)`. -/
def killInt (x : Sym) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static (.mk _ (.basic (.integer (.signed .int)))))
      (.mk _ () (.sym x')))))) => x'.key = x.key
  | _ => false

/-- `kill(int, x) ; pure(unit)`: the end of the block. -/
def killUnit (x : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) kl (.mk _ (.pure (.mk _ () (.val .unit))))) => killInt x kl
  | _ => false

/-- `let strong u = bound(let weak p = pure(x) in load(int, p)) in
kill(int, x) ; run ret(conv_loaded_int(int, u))`: `return x;`. -/
def retLocal (file : File Codec.wireModel Unit Unit) (ret x : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (some u, _)))
      (.mk _ (.bound (.mk _ (.wseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x''))))
        (.mk _ (.action (.mk .pos (.mk _ _ (.load
          (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
          (.mk _ () (.sym p')) .na)))))))))
      (.mk _ (.sseq (.mk _ (.base (none, _))) kl
        (.mk _ (.run () l [.mk _ () (.call (.sym s)
          [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))))) =>
      x''.key = x.key && p'.key = p.key && u'.key = u.key && decide (u.key ≠ x.key) &&
        l.key = ret.key && isConvLoadedInt file s && killInt x kl
  | _ => false

/-! ## Runs -/

theorem createInt_reaches {e : Eff} (h : createInt e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m', m'.stdout = m.stdout ∧ LiveInt m' m.nextId (nextIntAddress m) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), k, m'⟩ := by
  unfold createInt at h
  split at h
  · rename_i _ ann l u a1 a2 c1 a3 c2 pref
    obtain ⟨lf, hf⟩ := focusMemory_eq ann m
    have hlive := created_live pref c2 (focusMemory ann m) (by rw [hf]; exact hdead)
    have hreach := create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 l u pref
      env k m hpos
    rw [nextIntAddress_focus] at hlive
    rw [hf] at hlive hreach
    exact ⟨_, by rw [Actions.created_stdout], hlive, hreach⟩
  · cases h

theorem storeLit_reaches {x : Sym} {e : Eff} {n : Int} (h : storeLit file x e = some n)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (live : LiveInt m id addr) :
    IntRange n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Slot m' id addr n ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  unfold storeLit at h
  split at h
  · rename_i _ ann pann t ty bann ann' pann' n' sann l u a1 c1 a2 x' a3 s a4 c3 a5 t'
    split at h
    · rename_i cond
      obtain ⟨hx', ht', htx, hs, lo, hi⟩ := cond
      cases h
      refine ⟨⟨lo, hi⟩, ?_⟩
      let v : Val := .loaded (.specified (.integer n))
      let m₁ := focusMemory ann' m
      let env₁ := extendEnv [(t, v)] env
      have hx₁ : env₁.lookup x' = some (.object (.pointer (.allocated id addr))) := by
        rw [ConvInt.lookup_one_other (by rw [hx']; exact fun e => htx e.symm), lookup_key hx']
        exact hx
      have ht₁ : env₁.lookup t' = some v := ConvInt.lookup_one ht'
      have live₁ : LiveInt m₁ id addr := liveInt_focus ann' live
      obtain ⟨xs, hst⟩ := store_reaches (file := file) (labels := labels) sann a1 a2 a3 a4 a5 c1 c3
        l u x' s t' hs env₁ k m₁ hx₁ ht₁ ⟨lo, hi⟩ live₁
      refine ⟨_, xs, ?_, stored_slot (liveInt_focus sann live₁) n, ?_⟩
      · simp [stored_stdout, m₁]
      refine (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans ?_
      refine (ReturnLit.boundLit_reaches bann ann' pann' n env _ m).trans ?_
      exact (ReturnLit.bind_reaches pann t ty v _ env k m₁).trans hst
    · cases h
  · cases h

theorem killInt_reaches {x : Sym} {e : Eff} (h : killInt x e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (live : LiveInt m id addr) :
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold killInt at h
  split at h
  · rename_i _ ann l u c1 a2 x'
    have hx' : env.lookup x' = some (.object (.pointer (.allocated id addr))) := by
      rw [lookup_key (of_decide_eq_true h)]; exact hx
    exact ⟨_, by simp [killed], kill_reaches ann a2 c1 l u x' env k m hx' live⟩
  · cases h

theorem killUnit_reaches {x : Sym} {e : Eff} (h : killUnit x e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (live : LiveInt m id addr) :
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold killUnit at h
  split at h
  · rename_i _ ann pann ty kl uann pann'
    obtain ⟨m₁, out₁, hk⟩ := killInt_reaches h env
      (.strongBind (.mk pann (.base (none, ty))) _ env :: k) m hx live
    refine ⟨focusMemory uann m₁, by simp [out₁], ?_⟩
    refine (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans (hk.trans ?_)
    refine (ReturnConst.wildcard_sequence_reaches file labels pann ty .unit _ env k m₁).trans ?_
    exact (ReturnConst.effect_pure_reaches file labels uann _ env k m₁).trans
      ((ReturnConst.pure_value_reaches file labels pann' .unit env _ _).trans
        (ReturnConst.diagnostic_reaches file labels m₁.currentLocation .unit k _))
  · cases h

theorem retLocal_halts {ret x : Sym} {e : Eff} (h : retLocal file ret x e = true)
    (hret : ReturnLabel labels ret) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ := by
  unfold retLocal at h
  split at h
  · rename_i _ ann pann u ty bann wann ppat p pty pureann pann2 x'' lann ll lu a1 c1 a2 p'
      sann kpann kty kl rann l cann s a3 c3 a4 u'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hx'', hp'⟩, hu'⟩, hux⟩, hl⟩, hs⟩, hkl⟩ := h
    let ptr : Val := .object (.pointer (.allocated id addr))
    let v : Val := .loaded (.specified (.integer n))
    let REST : EE := .mk sann (.sseq (.mk kpann (.base (none, kty))) kl
        (.mk rann (.run () l [.mk cann () (.call (.sym s)
          [.mk a3 () (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))), .mk a4 () (.sym u')])])))
    let LOAD : EE := .mk lann (.action (.mk .pos (.mk ll lu (.load
          (.mk a1 () (.val (.ctype (.mk c1 (.basic (.integer (.signed .int)))))))
          (.mk a2 () (.sym p')) .na))))
    let kR := Frame.strongBind (.mk pann (.base (some u, ty))) REST env :: k
    -- the bound load of `x`
    let m₁ := focusMemory pureann m
    have hxl : env.lookup x'' = some ptr := by rw [lookup_key hx'']; exact hx
    have hp₁ : (extendEnv [(p, ptr)] env).lookup p' = some ptr := ConvInt.lookup_one hp'
    obtain ⟨zs, hld⟩ := load_reaches (file := file) (labels := labels) lann a1 a2 c1 ll lu p'
      (extendEnv [(p, ptr)] env) (.bound :: kR) m₁ hp₁ hn (slot_focus pureann slot)
    let m₂ : Mem.Concrete.State := {focusMemory lann m₁ with lastUsed := some id}
    have live₂ : LiveInt m₂ id addr :=
      liveInt_lastUsed _ (liveInt_focus lann (liveInt_focus pureann slot.live))
    -- `kill(int, x)`, then `run`
    let env₂ := extendEnv [(u, v)] env
    have hx₂ : env₂.lookup x = some ptr := by
      rw [ConvInt.lookup_one_other (fun e => hux e.symm)]; exact hx
    let RUN : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
          [.mk a3 () (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))), .mk a4 () (.sym u')])])
    obtain ⟨m₃, out₃, hkill⟩ := killInt_reaches hkl env₂
      (.strongBind (.mk kpann (.base (none, kty))) RUN env₂ :: k) m₂ hx₂ live₂
    have heval : Eval file (tagsOf file (focusMemory rann m₃)) env₂
        (.inl (.mk cann () (.call (.sym s)
          [.mk a3 () (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))), .mk a4 () (.sym u')])))
        (.inl v) :=
      ConvInt.convLoadedInt_eval (ann := c3) hs hn (.cons .val (.cons (.sym (ConvInt.lookup_one hu')) .nil))
    obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₂ hk (focusMemory rann m₃)
    refine ⟨m', ?_, ?_⟩
    · simp [out, out₃, m₂, m₁]
    refine (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans ?_
    refine (ReturnLit.bound_reaches bann _ env _ m).trans ?_
    refine (wseq_reaches wann _ _ _ env _ m).trans ?_
    refine (ReturnConst.effect_pure_reaches file labels pureann _ env _ m).trans ?_
    refine ((Eval.sound file _ (Eval.sym (ann := pann2) hxl)) labels _ m₁ rfl).trans ?_
    refine (ReturnConst.diagnostic_reaches file labels m.currentLocation ptr _ m₁).trans ?_
    refine (wbind_reaches ppat p pty ptr LOAD env _ m₁).trans ?_
    refine hld.trans ?_
    refine (annotations_bound_reaches zs v kR _).trans ?_
    refine (ReturnLit.bind_reaches pann u ty v REST env k m₂).trans ?_
    refine (ReturnConst.sequence_reaches file labels sann _ _ _ env₂ k m₂).trans ?_
    refine hkill.trans ?_
    refine (ReturnConst.wildcard_sequence_reaches file labels kpann kty .unit RUN env₂ k m₃).trans ?_
    refine (Straight.focus_reaches (m := m₃) Straight.request_run).trans ?_
    exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
  · cases h

end Silmaril.Compile.Core.Verified.Locals
