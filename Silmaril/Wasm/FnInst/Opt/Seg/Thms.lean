module

public import Silmaril.Wasm.FnInst.Opt.Seg.Defs
import Silmaril.Proofs.Wasm.FnInst.Opt.Seg.Basic

@[expose] public section

/-! # The fragment: theorems

The results used by the institution and the rule library (proofs in
`Silmaril.Proofs.Wasm.FnInst.Opt.Seg.Basic`):

* `run_append`, `Out.bind_congr`, `Out.bind_mono`: running a concatenation is sequential
  composition of outcome sets;
* `chk_append`, `chk_frame`, `chk_shift`: the stack checker composes and satisfies the frame
  rule;
* `run_height`: under a typed environment the checker's heights are runtime heights;
* `chk_ft`, `run_ft`, `Env.typed_of_prefix`: added functions change neither typing nor runs of
  code typed before;
* `run_rw`: exchanging a segment pair that runs the same from every state of its hole, at
  typed positions of any code;
* `fsem_typed`, `fsem_total`, `fsem_rewrite`, `den_rewrite`: the module form, the
  peephole-rewrite theorem of the fragment: a pair equivalent at its hole in every completion
  of the least informative model can be exchanged in every body of every well-typed module.
-/

namespace Silmaril.Wasm.FnInst.Opt

section



@[simp] theorem Out.mem_bind {S : Set Out} {k : St → Set Out} {o : Out} :
    o ∈ bind S k ↔ (∃ st, Out.ok st ∈ S ∧ o ∈ k st) ∨ (o ∈ S ∧ o.isOk = false) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.mem_bind

@[simp] theorem Out.isOk_ok (st : St) : (Out.ok st).isOk = true :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.isOk_ok st

@[simp] theorem Out.bind_ok (st : St) (k : St → Set Out) : bind {Out.ok st} k = k st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.bind_ok st k

theorem Out.bind_assoc (S : Set Out) (k : St → Set Out) (l : St → Set Out) :
    bind (bind S k) l = bind S (fun st => bind (k st) l) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.bind_assoc S k l

theorem Out.bind_congr {S : Set Out} {k k' : St → Set Out}
    (h : ∀ st, Out.ok st ∈ S → k st = k' st) : bind S k = bind S k' :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.bind_congr h

theorem Out.bind_mono {S : Set Out} {k k' : St → Set Out}
    (h : ∀ st, Out.ok st ∈ S → k st ⊆ k' st) : bind S k ⊆ bind S k' :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.bind_mono h

theorem Out.bind_mono_left {S S' : Set Out} (hS : S ⊆ S') (k : St → Set Out) :
    bind S k ⊆ bind S' k :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Out.bind_mono_left hS k

@[simp] theorem run_nil (ft : FTypes) (E : Env) (st : St) : run ft E [] st = {.ok st} :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_nil ft E st

@[simp] theorem run_cons (ft : FTypes) (E : Env) (i : Instr) (c : Code) (st : St) :
    run ft E (i :: c) st = Out.bind (step ft E i st) (run ft E c) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_cons ft E i c st

theorem run_append (ft : FTypes) (E : Env) (c d : Code) (st : St) :
    run ft E (c ++ d) st = Out.bind (run ft E c st) (run ft E d) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_append ft E c d st

@[simp] theorem chk_nil (ft : FTypes) (h : ℕ) : chk ft [] h = some h :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_nil ft h

@[simp] theorem chk_cons (ft : FTypes) (i : Instr) (c : Code) (h : ℕ) :
    chk ft (i :: c) h = (hgt ft i h).bind (chk ft c) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_cons ft i c h

theorem chk_append (ft : FTypes) (c d : Code) (h : ℕ) :
    chk ft (c ++ d) h = (chk ft c h).bind (chk ft d) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_append ft c d h

theorem hgt_spec {ft : FTypes} {i : Instr} {h h₂ : ℕ} :
    hgt ft i h = some h₂ ↔ ∃ p q, arity ft i = some (p, q) ∧ p ≤ h ∧ h₂ = h - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.hgt_spec

theorem hgt_frame {ft : FTypes} {i : Instr} {h h' : ℕ} (k : ℕ) (hh : hgt ft i h = some h') :
    hgt ft i (h + k) = some (h' + k) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.hgt_frame k hh

theorem chk_frame {ft : FTypes} {c : Code} {h h' : ℕ} (k : ℕ) (hc : chk ft c h = some h') :
    chk ft c (h + k) = some (h' + k) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_frame k hc

/-- Code typed from `n` to `m` takes height `h ≥ n` to `h - n + m`. -/
theorem chk_shift {ft : FTypes} {c : Code} {n m h : ℕ} (hc : chk ft c n = some m) (hn : n ≤ h) :
    chk ft c h = some (h - n + m) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_shift hc hn

theorem getElem?_of_prefix {α : Type} {l l' : List α} (hp : l <+: l') {i : ℕ} {a : α}
    (h : l[i]? = some a) : l'[i]? = some a :=
  Silmaril.Proofs.Wasm.FnInst.Opt.getElem?_of_prefix hp h

theorem arity_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {i : Instr} {a : ℕ × ℕ}
    (h : arity ft i = some a) : arity ft' i = some a :=
  Silmaril.Proofs.Wasm.FnInst.Opt.arity_of_prefix hp h

theorem hgt_ft {ft ft' : FTypes} (hp : ft <+: ft') {i : Instr} {h h₂ : ℕ}
    (hh : hgt ft i h = some h₂) : hgt ft' i h = some h₂ :=
  Silmaril.Proofs.Wasm.FnInst.Opt.hgt_ft hp hh

theorem chk_ft {ft ft' : FTypes} (hp : ft <+: ft') {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') : chk ft' c h = some h' :=
  Silmaril.Proofs.Wasm.FnInst.Opt.chk_ft hp hc

theorem step_ft {ft ft' : FTypes} (hp : ft <+: ft') (E : Env) {i : Instr} {a : ℕ × ℕ}
    (ha : arity ft i = some a) (st : St) : step ft E i st = step ft' E i st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.step_ft hp E ha st

theorem run_ft {ft ft' : FTypes} (hp : ft <+: ft') (E : Env) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') (st : St) : run ft E c st = run ft' E c st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_ft hp E hc st

theorem Env.typed_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {E : Env} (hE : E.Typed ft') :
    E.Typed ft :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.typed_of_prefix hp hE

theorem Env.typed_mono {ft : FTypes} {E M : Env} (hle : E ≤ M) (hM : M.Typed ft) : E.Typed ft :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.typed_mono hle hM

theorem Env.top_total : Env.top.Total :=
  Silmaril.Proofs.Wasm.FnInst.Opt.Env.top_total

theorem binop_height {f : Val → Val → Val} {st st' : St} {h : ℕ} (hs : st.stack.length = h)
    (ho : binop f st = .ok st') : 2 ≤ h ∧ st'.stack.length = h - 2 + 1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.binop_height hs ho

theorem unop_height {f : Val → Val} {st st' : St} {h : ℕ} (hs : st.stack.length = h)
    (ho : unop f st = .ok st') : 1 ≤ h ∧ st'.stack.length = h - 1 + 1 :=
  Silmaril.Proofs.Wasm.FnInst.Opt.unop_height hs ho

theorem pop1_height {st st' : St} {k : Val → St → St} {d : ℕ}
    (hk : ∀ v s, (k v s).stack.length = s.stack.length + d) (ho : pop1 st k = .ok st') :
    1 ≤ st.stack.length ∧ st'.stack.length = st.stack.length - 1 + d :=
  Silmaril.Proofs.Wasm.FnInst.Opt.pop1_height hk ho

/-- A push of one value, with arity `(0, 1)`. -/
theorem push_arity {st st' : St} {v : Val} {p q : ℕ} (ha : some (0, 1) = some (p, q))
    (ho : Out.ok { st with stack := v :: st.stack } = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.push_arity ha ho

theorem binop_arity {f : Val → Val → Val} {st st' : St} {p q : ℕ}
    (ha : some (2, 1) = some (p, q)) (ho : binop f st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.binop_arity ha ho

theorem unop_arity {f : Val → Val} {st st' : St} {p q : ℕ}
    (ha : some (1, 1) = some (p, q)) (ho : unop f st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.unop_arity ha ho

theorem pop1_arity {st st' : St} {k : Val → St → St} {d p q : ℕ}
    (hk : ∀ v s, (k v s).stack.length = s.stack.length + d) (ha : some (1, d) = some (p, q))
    (ho : pop1 st k = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.pop1_arity hk ha ho

/-- Every deterministic instruction moves the stack height as its arity says. -/
theorem exec1_arity {ft : FTypes} {i : Instr} {p q : ℕ} (ha : arity ft i = some (p, q))
    {st st' : St} (ho : exec1 i st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q :=
  Silmaril.Proofs.Wasm.FnInst.Opt.exec1_arity ha ho

theorem exec1_height {ft : FTypes} {i : Instr} {h h₂ : ℕ} (hh : hgt ft i h = some h₂)
    {st st' : St} (hs : st.stack.length = h) (ho : exec1 i st = .ok st') :
    st'.stack.length = h₂ :=
  Silmaril.Proofs.Wasm.FnInst.Opt.exec1_height hh hs ho

theorem step_height {ft : FTypes} {E : Env} (hE : E.Typed ft) {i : Instr} {h h₂ : ℕ}
    (hh : hgt ft i h = some h₂) {st st' : St} (hs : st.stack.length = h)
    (ho : Out.ok st' ∈ step ft E i st) : st'.stack.length = h₂ :=
  Silmaril.Proofs.Wasm.FnInst.Opt.step_height hE hh hs ho

theorem run_height {ft : FTypes} {E : Env} (hE : E.Typed ft) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') {st st' : St} (hs : st.stack.length = h)
    (ho : Out.ok st' ∈ run ft E c st) : st'.stack.length = h' :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_height hE hc hs ho

/-- **Exchanging a segment pair at typed positions.** If `s` and `s'` run the same from every
state with at least `n` operands, and `s` has stack type `n → m`, then exchanging occurrences
of `s` by `s'` at positions of height at least `n` does not change the run of any code. -/
theorem run_rw {ft : FTypes} {E : Env} (hE : E.Typed ft) {s s' : Code} {n m : ℕ}
    (hs : RunEq ft n E s s')
    (hty : chk ft s n = some m) {h : ℕ} {c c' : Code} (hr : Rw ft s s' n m h c c') :
    ∀ st : St, st.stack.length = h → run ft E c st = run ft E c' st :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_rw hE hs hty hr

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (i : ℕ) :
    (l[i]? = none ∧ l'[i]? = none) ∨ ∃ a b, l[i]? = some a ∧ l'[i]? = some b ∧ R a b :=
  Silmaril.Proofs.Wasm.FnInst.Opt.forall₂_getElem? h i

theorem answers_typed {ft : FTypes} {E : Env} (hE : E.Typed ft) {b : Code} {m : ℕ}
    (hb : chk ft b 0 = some m) {args : List Val} {g : ℕ → Val} {r : List Val} {g' : ℕ → Val}
    (ha : Ans.ret r g' ∈ answers (run ft E b (initSt args g))) : r.length = m :=
  Silmaril.Proofs.Wasm.FnInst.Opt.answers_typed hE hb ha

theorem fsem_zero_typed (M : Mdl) {imp : Env} (himp : imp.Typed M.ft) :
    (fsem M imp 0).Typed M.ft :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_zero_typed M himp

/-- The body case: a defined function answers with its body's final stack, of its result
count. -/
theorem body_typed {M : Mdl} (hM : M.Typed) {E : Env} (hE : E.Typed M.ft) {f n m : ℕ}
    (hf : M.ft[f]? = some (n, m)) (hlt : ¬ f < M.nimp) {b : Code}
    (hb : M.bodies[f - M.nimp]? = some b) {args : List Val} {g : ℕ → Val} {r : List Val}
    {g' : ℕ → Val} (hr : Ans.ret r g' ∈ answers (run M.ft E b (initSt args g))) :
    r.length = m :=
  Silmaril.Proofs.Wasm.FnInst.Opt.body_typed hM hE hf hlt hb hr

theorem fsem_succ_typed {M : Mdl} (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft) {k : ℕ}
    (ih : (fsem M imp k).Typed M.ft) : (fsem M imp (k + 1)).Typed M.ft :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_succ_typed hM himp ih

/-- The semantics of a well-typed module at every call depth is a typed environment. -/
theorem fsem_typed {M : Mdl} (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft) :
    ∀ k, (fsem M imp k).Typed M.ft :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_typed hM himp

theorem step_nonempty {ft : FTypes} {E : Env} (hE : E.Total) (i : Instr) (st : St) :
    (step ft E i st).Nonempty :=
  Silmaril.Proofs.Wasm.FnInst.Opt.step_nonempty hE i st

theorem run_nonempty {ft : FTypes} {E : Env} (hE : E.Total) (c : Code) (st : St) :
    (run ft E c st).Nonempty :=
  Silmaril.Proofs.Wasm.FnInst.Opt.run_nonempty hE c st

theorem answers_nonempty {S : Set Out} (hS : S.Nonempty) : (answers S).Nonempty :=
  Silmaril.Proofs.Wasm.FnInst.Opt.answers_nonempty hS

/-- The semantics of a module at every call depth always answers, when its imports do. -/
theorem fsem_total (M : Mdl) {imp : Env} (himp : imp.Total) : ∀ k, (fsem M imp k).Total :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_total M himp

/-- One more call depth: if the two modules agree at depth `k`, they agree at `k + 1`. -/
theorem fsem_succ_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') {k : ℕ} (ih : fsem M imp k = fsem M' imp k) :
    fsem M imp (k + 1) = fsem M' imp (k + 1) :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_succ_rewrite hs hty hM himp himp' hR ih

/-- **Module rewriting.** A segment pair that runs the same from every state of its hole in
every completion of the least informative model can be exchanged at typed positions in any
bodies of any well-typed module: the module's semantics is unchanged at every call depth. -/
theorem fsem_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') : ∀ k, fsem M imp k = fsem M' imp k :=
  Silmaril.Proofs.Wasm.FnInst.Opt.fsem_rewrite hs hty hM himp himp' hR

/-- The denotations of all functions agree after a module rewrite. -/
theorem den_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') : den M imp = den M' imp :=
  Silmaril.Proofs.Wasm.FnInst.Opt.den_rewrite hs hty hM himp himp' hR

end

end Silmaril.Wasm.FnInst.Opt
