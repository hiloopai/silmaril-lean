module

public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Execution.Runtime
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic

@[expose] public section

/-! # Component-facing interface pieces (towards a `CoreEngine` instance, U29)

The component branch's `CoreEngine` needs, beyond threads/status/resume:

* flat function types: `ofFlatType := V1.FuncType.toDefType` with the partial
  inverse `flatType?` (`flatType?_ofFlatType`);
* a frame-independent extern type with decidable subtyping: `CExternType` with
  `ExternSub {}` (decidability: `ExternSub.decide`);
* store inspection and host allocation: `externType?`, `allocHost`, `memSize?`,
  `memRead?`, `memWrite?`, `tableFunc?`, `memAddrType?`, `tableAddrType?`;
* flat values crossing the boundary (`ofFlat`, `toFlat?`).

A computable `prepare?` (allocation plus segment initialisation, start function
returned rather than run) needs a constant-expression evaluator proved sound
against `EvalExpr`; it is left to U17/U29 and is not declared here.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- Flat function types become Core defined types. -/
def ofFlatType (ft : V1.FuncType) : DefType := ft.toDefType

def numOf? : CValType → Option NumType
  | .num t => some t
  | _ => none

/-- The flat function type of a defined type, if it is one. -/
def flatType? (d : DefType) : Option V1.FuncType := do
  let (ps, rs) ← d.funcType?
  let ft : V1.FuncType := ⟨← ps.mapM numOf?, ← rs.mapM numOf?⟩
  if ft.toDefType = d then some ft else none

theorem mapM_numOf?_map (ts : List NumType) : (ts.map Ty.num).mapM numOf? = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ih, numOf?]

theorem funcType?_ofFlatType (ft : V1.FuncType) :
    (ofFlatType ft).funcType? = some (ft.params.map Ty.num, ft.results.map Ty.num) := by
  simp [ofFlatType, DefType.funcType?, V1.FuncType.toDefType_expand]

theorem flatType?_ofFlatType (ft : V1.FuncType) : flatType? (ofFlatType ft) = some ft := by
  simp only [flatType?, funcType?_ofFlatType, Option.bind_eq_bind, Option.bind_some,
    mapM_numOf?_map]
  simp [ofFlatType]

/-- A flat (numeric) value as a Core value. -/
def ofFlat (v : Silmaril.Wasm.Execution.Runtime.Value) : Val := .num ⟨v.type, v.bits⟩

def toFlat? : Val → Option Silmaril.Wasm.Execution.Runtime.Value
  | .num v => some ⟨v.type, v.bits⟩
  | _ => none

@[simp] theorem toFlat?_ofFlat (v : Silmaril.Wasm.Execution.Runtime.Value) :
    toFlat? (ofFlat v) = some v := rfl

/-- The (closed, frame-independent) type of an external address. -/
def externType? (s : Store H) : ExternAddr → Option CExternType
  | .tag a => s.tags[a]?.map fun ti => .tag ti.type
  | .global a => s.globals[a]?.map fun gi => .global gi.type
  | .mem a => s.mems[a]?.map fun mi => .mem mi.type
  | .table a => s.tables[a]?.map fun ti => .table ti.type
  | .func a => s.funcs[a]?.map fun fi => .func fi.type

/-- Import matching in the empty context. -/
abbrev ExternSubClosed (a b : CExternType) : Prop := ExternSub {} a b

/-- Allocate a host function of a flat type. -/
def allocHost (s : Store H) (ft : V1.FuncType) (h : H) : Store H × Nat :=
  allocFunc s (ofFlatType ft) (.host h) {}

def memSize? (s : Store H) (a : Nat) : Option Nat := s.mems[a]?.map fun mi => mi.bytes.size

def memAddrType? (s : Store H) (a : Nat) : Option AddrType := s.mems[a]?.map fun mi => mi.type.address

def tableAddrType? (s : Store H) (a : Nat) : Option AddrType :=
  s.tables[a]?.map fun ti => ti.type.address

def memRead? (s : Store H) (a start len : Nat) : Option ByteArray := do
  let mi ← s.mems[a]?
  Silmaril.Wasm.Execution.Memory.readBytes mi.bytes start len

def memWrite? (s : Store H) (a start : Nat) (bytes : ByteArray) : Option (Store H) := do
  let mi ← s.mems[a]?
  let b ← Silmaril.Wasm.Execution.Memory.writeBytes mi.bytes start bytes
  return s.setMem a { mi with bytes := b }

/-- `none` = out of bounds, `some none` = null or non-function reference. -/
def tableFunc? (s : Store H) (t i : Nat) : Option (Option Nat) := do
  let ti ← s.tables[t]?
  let r ← ti.refs[i]?
  return match r with
    | .func a => some a
    | _ => none

/-! ## Flat-value adapter (CoreEngine uses `FlatValue`) -/

/-- Store-free invocation with flat arguments. -/
def Thread.invokeFlat (a : Nat) (args : List Silmaril.Wasm.Execution.Runtime.Value) : Thread :=
  Thread.invoke a (args.map ofFlat)

/-- Status with flat values: a value result with a non-flat value, or a callout
with non-flat arguments, is reported as `none` (never happens for flat-typed
functions on valid stores: `status_flat`). -/
noncomputable def statusFlat (o : GrowOracle) (s : Store H) (t : Thread) :
    Option (Status H × List Silmaril.Wasm.Execution.Runtime.Value) :=
  match status o s t with
  | .returned (.values vs) => (vs.mapM toFlat?).map fun fvs => (.returned (.values vs), fvs)
  | .callout h args => (args.mapM toFlat?).map fun fargs => (.callout h args, fargs)
  | st => some (st, [])

theorem flatType?_sound {d : DefType} {ft : V1.FuncType} (h : flatType? d = some ft) :
    ofFlatType ft = d := by
  unfold flatType? at h
  simp only [Option.bind_eq_bind] at h
  cases hd : d.funcType? with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨ps, rs⟩
    simp only [hd, Option.bind_some] at h
    cases hp : ps.mapM numOf? with
    | none => simp [hp] at h
    | some ps' =>
      cases hr : rs.mapM numOf? with
      | none => simp [hp, hr] at h
      | some rs' =>
        simp only [hp, hr, Option.bind_some] at h
        split at h
        · rename_i heq; simp only [Option.some.injEq] at h; subst h; exact heq
        · simp at h

theorem forall₂_ofFlat {s : Store H} (args : List Silmaril.Wasm.Execution.Runtime.Value) :
    List.Forall₂ (ValOk s) (args.map ofFlat) ((args.map (·.type)).map Ty.num) := by
  induction args with
  | nil => exact .nil
  | cons v vs ih => exact .cons (ValOk.num ⟨v.type, v.bits⟩) ih

theorem status_returned_values {o : GrowOracle} {s : Store H} {t : Thread} {vs : List Val}
    (h : status o s t = .returned (.values vs)) : (t.config s).code = vals vs := by
  unfold status at h
  simp only at h
  split at h
  · rename_i hex
    simp only [Status.returned.injEq, CallResult.values.injEq] at h
    subst h
    exact hex.choose_spec
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h

theorem sub_num_inv {Δ : TypeCtx} {t : CValType} {n : NumType} (h : Sub Δ t (.num n)) :
    t = .num n ∨ t = .botv := by
  cases h
  · exact .inl rfl
  · exact .inr rfl

theorem flat_of_typed {s : Store H} {Δ : TypeCtx} :
    ∀ {vs : List Val} {ts : List CValType} {ns : List NumType},
      List.Forall₂ (ValOk s) vs ts → ResultSub Δ ts (ns.map Ty.num) →
      ∃ fvs, vs.mapM toFlat? = some fvs ∧ fvs.map (·.type) = ns
  | [], [], [], .nil, _ => ⟨[], rfl, rfl⟩
  | [], _, _ :: _, .nil, hs => by cases hs
  | v :: vs, t :: ts, n :: ns, .cons hv hvs, hs => by
    cases hs with
    | cons hsub hsubs =>
      obtain ⟨fvs, h1, h2⟩ := flat_of_typed hvs hsubs
      rcases sub_num_inv hsub with rfl | rfl
      · cases hv with
        | num nv =>
          refine ⟨⟨nv.type, nv.bits⟩ :: fvs, ?_, ?_⟩
          · simp [List.mapM_cons, toFlat?, h1]
          · simp [h2]
      · cases hv
  | _ :: _, _ :: _, [], .cons _ _, hs => by cases hs

/-! ### Inverting the typing of a value sequence against numeric results

`AdminsOk.vals_inv` needs a well-formed type context (for transitivity of
subtyping). Against numeric result types subtyping collapses to "equal or
`botv`", which is transitive outright, so no context well-formedness is needed. -/

/-- Equal, or `botv` on the left. -/
def BotLe (a b : CValType) : Prop := a = b ∨ a = .botv

/-- A numeric value type or `botv`. -/
def NumOrBot (u : CValType) : Prop := (∃ n, u = .num n) ∨ u = .botv

theorem BotLe.trans {a b c : CValType} (h₁ : BotLe a b) (h₂ : BotLe b c) : BotLe a c := by
  rcases h₁ with rfl | rfl
  · exact h₂
  · exact .inr rfl

theorem sub_botv_inv {Δ : TypeCtx} {t : CValType} (h : Sub Δ t .botv) : t = .botv := by
  cases h
  rfl

theorem f2_split {α β : Type _} {R : α → β → Prop} :
    ∀ {a b : List α} {l : List β}, List.Forall₂ R (a ++ b) l →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R a l₁ ∧ List.Forall₂ R b l₂
  | [], _, l, h => ⟨[], l, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hx h =>
    let ⟨l₁, l₂, e, h₁, h₂⟩ := f2_split h
    ⟨_ :: l₁, l₂, by rw [e]; rfl, .cons hx h₁, h₂⟩

theorem f2_app {α β : Type _} {R : α → β → Prop} :
    ∀ {a b : List α} {c d : List β}, List.Forall₂ R a c → List.Forall₂ R b d →
      List.Forall₂ R (a ++ b) (c ++ d)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons hx h, h' => .cons hx (f2_app h h')

theorem sub_botLe_f2 {Δ : TypeCtx} :
    ∀ {a b c : List CValType}, List.Forall₂ (Sub Δ) a b → List.Forall₂ BotLe b c →
      (∀ z ∈ c, NumOrBot z) → List.Forall₂ BotLe a c
  | [], [], [], .nil, .nil, _ => .nil
  | x :: _, y :: _, z :: _, .cons hxy hs, .cons hyz hs', hc => by
    refine .cons ?_ (sub_botLe_f2 hs hs' fun w hw => hc w (List.mem_cons_of_mem _ hw))
    have hz := hc z List.mem_cons_self
    rcases hyz with rfl | rfl
    · rcases hz with ⟨n, rfl⟩ | rfl
      · rcases sub_num_inv hxy with rfl | rfl
        · exact .inl rfl
        · exact .inr rfl
      · exact .inr (sub_botv_inv hxy)
    · exact .inr (sub_botv_inv hxy)

theorem AdminsOk.vals_num_aux {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ vs, as = vals vs →
      ∀ us, (∀ u ∈ us, NumOrBot u) → List.Forall₂ BotLe it.results us →
      ∃ ts, List.Forall₂ (ValOk s) vs ts ∧ List.Forall₂ BotLe (it.params ++ ts) us
  | _, _, _, .nil, vs, e, us, _, hr => by
    have : vs = [] := List.map_eq_nil_iff.mp e.symm
    subst this
    exact ⟨[], .nil, by simpa using hr⟩
  | _, _, _, .single h, vs, e, us, _, hr => by
    obtain ⟨v, rfl, hv⟩ := List.map_eq_singleton_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hres⟩ := AdminOk.toAdmin_inv h
    rw [hres] at hr
    exact ⟨[t], .cons hv .nil, by rw [hp]; exact hr⟩
  | _, _, _, .cons ha _ hs, vs, e, us, hu, hr => by
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hres⟩ := AdminOk.toAdmin_inv ha
    obtain ⟨ts', hv', r⟩ := AdminsOk.vals_num_aux hs vs' e'.symm us hu hr
    simp only at hp hres
    subst hp hres
    exact ⟨t :: ts', .cons hv hv', by simpa using r⟩
  | _, _, _, .seq h₁ _ h₂, vs, e, us, hu, hr => by
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨ts₂, v₂, r₂⟩ := AdminsOk.vals_num_aux h₂ vs₂ e₂.symm us hu hr
    obtain ⟨u₁, u₂, rfl, r₂a, r₂b⟩ := f2_split r₂
    obtain ⟨ts₁, v₁, r₁⟩ := AdminsOk.vals_num_aux h₁ vs₁ e₁.symm u₁
      (fun u hu' => hu u (List.mem_append_left _ hu')) r₂a
    refine ⟨ts₁ ++ ts₂, f2_app v₁ v₂, ?_⟩
    rw [← List.append_assoc]
    exact f2_app r₁ r₂b
  | _, _, _, .sub h hs _, vs, e, us, hu, hr => by
    obtain ⟨hpar, hres, -⟩ := hs
    obtain ⟨ts, hv, r⟩ := AdminsOk.vals_num_aux h vs e us hu (sub_botLe_f2 hres hr hu)
    obtain ⟨u₁, u₂, rfl, r₁, r₂⟩ := f2_split r
    exact ⟨ts, hv, f2_app (sub_botLe_f2 hpar r₁ fun z hz => hu z (List.mem_append_left _ hz)) r₂⟩
  | _, _, _, .frame h _, vs, e, us, hu, hr => by
    obtain ⟨u₀, u₂, rfl, r₀, r₂⟩ := f2_split hr
    obtain ⟨ts, hv, r⟩ := AdminsOk.vals_num_aux h vs e u₂
      (fun u h' => hu u (List.mem_append_right _ h')) r₂
    refine ⟨ts, hv, ?_⟩
    simp only [List.append_assoc]
    exact f2_app r₀ r

theorem botLe_resultSub {Δ : TypeCtx} :
    ∀ {ns : List NumType} {ts : List CValType}, List.Forall₂ BotLe ts (ns.map Ty.num) →
      ResultSub Δ ts (ns.map Ty.num)
  | [], _, h => by
    simp only [List.map_nil, List.forall₂_nil_right_iff] at h
    subst h
    exact .nil
  | n :: ns, _, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons h hs =>
      refine .cons ?_ (botLe_resultSub hs)
      rcases h with rfl | rfl
      · exact .num
      · exact .botv

/-- **Milestone (flat law).** Invoking a function of flat type with flat arguments
on a valid store, every reachable returned result consists of flat values. -/
theorem status_flat {o : GrowOracle} {s s' : Store H} {a : Nat} {fi : FuncInst H}
    {ft : V1.FuncType} {args : List Silmaril.Wasm.Execution.Runtime.Value} {t : Thread}
    {vs : List Val} (hs : StoreOk s) (hf : s.funcs[a]? = some fi)
    (hft : flatType? fi.type = some ft) (hargs : args.map (·.type) = ft.params)
    (h : Relation.ReflTransGen (Internal o) (s, Thread.invokeFlat a args) (s', t))
    (hr : status o s' t = .returned (.values vs)) :
    ∃ fvs, vs.mapM toFlat? = some fvs ∧ fvs.map (·.type) = ft.results := by
  have hty : fi.type = ofFlatType ft := (flatType?_sound hft).symm
  have hexp : Expand fi.type (.func (Ty.ofList (ft.params.map Ty.num))
      (Ty.ofList (ft.results.map Ty.num))) := by
    rw [Expand.iff, hty]; exact V1.FuncType.toDefType_expand ft
  have hargsOk : List.Forall₂ (ValOk s) (args.map ofFlat)
      (Ty.ofList (ft.params.map Ty.num)).toList := by
    rw [Ty.toList_ofList, ← hargs]
    exact forall₂_ofFlat args
  have hinv : InvokeOk s a (args.map ofFlat) := ⟨fi, _, _, hf, hexp, hargsOk⟩
  obtain ⟨fi', ps', rs', hf', hexp', hok⟩ := invoke_ok hs hinv
  rw [hf] at hf'
  cases hf'
  have hrs : rs' = Ty.ofList (ft.results.map Ty.num) := by
    rw [Expand.iff] at hexp hexp'
    rw [hexp] at hexp'
    simp only [Option.some.injEq, Ty.func.injEq] at hexp'
    exact hexp'.2.symm
  subst hrs
  rw [Ty.toList_ofList] at hok
  have hinit : StoreOk s ∧ ThreadOk s (Thread.invokeFlat a args) (ft.results.map Ty.num) :=
    ⟨hs, hok⟩
  have key : ∀ y, Relation.ReflTransGen (Internal o) (s, Thread.invokeFlat a args) y →
      StoreOk y.1 ∧ ThreadOk y.1 y.2 (ft.results.map Ty.num) := by
    intro y hy
    induction hy with
    | refl => exact hinit
    | tail _ hstep ih =>
      obtain ⟨hs₁, ht₁⟩ := ih
      obtain ⟨hs₂, ht₂, -⟩ := Internal.preserves hs₁ ht₁ hstep
      exact ⟨hs₂, ht₂⟩
  have hfin : StoreOk s' ∧ ThreadOk s' t (ft.results.map Ty.num) := key _ h
  obtain ⟨-, C, -, hadm⟩ := hfin
  rw [status_returned_values hr] at hadm
  obtain ⟨ts', hvs, hsub⟩ := AdminsOk.vals_num_aux hadm _ rfl (ft.results.map Ty.num)
    (fun u hu => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hu
      exact .inl ⟨n, rfl⟩)
    (List.forall₂_same.mpr fun _ _ => .inl rfl)
  exact flat_of_typed (Δ := {}) hvs (botLe_resultSub (by simpa using hsub))

/-- A thread whose code is a host-call redex is at a callout. -/
theorem status_callout_of {o : GrowOracle} {s : Store H} {t : Thread} {E : Ctx} {a : Nat} {h : H}
    {args : List Val} (hv : ∀ vs, (t.config s).code ≠ vals vs)
    (ht : (t.config s).code ≠ [.trap]) (hth : ∀ a, (t.config s).code ≠ throwing a)
    (hd : decompose? s (t.config s).code = some (E, a, h, args)) :
    status o s t = .callout h args := by
  unfold status
  have h1 : ¬ ∃ vs, (t.config s).code = vals vs := fun ⟨vs, h⟩ => hv vs h
  have h3 : ¬ ∃ a, (t.config s).code = throwing a := fun ⟨a, h⟩ => hth a h
  simp only [h1, h3, ht, dite_false, ite_false, hd]

/-- `decompose?` at a top-level `CALL_REF` of a host function. -/
theorem decompose?_top {s : Store H} {pre : List Val} {a : Nat} {c : Admin} {rest : List Admin}
    {h : H} {n : Nat} (hc : c.isCallRef = true) (ha : hostArity? s a = some (h, n))
    (hn : n ≤ pre.length) :
    decompose? s (vals (pre ++ [.ref (.func a)]) ++ c :: rest) =
      some (.top (pre.take (pre.length - n)) rest, a, h, pre.drop (pre.length - n)) := by
  have hcv : c.val? = none := by
    rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> first | rfl | cases hc |
      (cases i <;> first | rfl | cases hc)
  have hsp := Det.splitVals_vals_cons (vs := pre ++ [.ref (.func a)]) hcv rest
  rw [decompose?]
  split
  · rename_i heq; rw [hsp] at heq; simp at heq; obtain ⟨_, rfl, _⟩ := heq; cases hc
  · rename_i heq; rw [hsp] at heq; simp at heq; obtain ⟨_, rfl, _⟩ := heq; cases hc
  · rename_i heq; rw [hsp] at heq; simp at heq; obtain ⟨_, rfl, _⟩ := heq; cases hc
  · rename_i heq
    rw [hsp] at heq
    simp only [Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp [hc, ha, hn]
  · rename_i heq; rw [hsp] at heq; simp at heq

theorem allocHost_callout {o : GrowOracle} (s : Store H) (ft : V1.FuncType) (h : H)
    (args : List Val) (hargs : args.length = ft.params.length) :
    status o (allocHost s ft h).1 (Thread.invoke (allocHost s ft h).2 args) = .callout h args := by
  have hfa : (allocHost s ft h).1.funcs[(allocHost s ft h).2]? =
      some ⟨ofFlatType ft, {}, .host h⟩ := by
    simp [allocHost, allocFunc]
  have hcode : ((Thread.invoke (allocHost s ft h).2 args).config (allocHost s ft h).1).code =
      vals (args ++ [.ref (.func (allocHost s ft h).2)]) ++ [.callRefType (ofFlatType ft)] := by
    simp [Thread.invoke, Thread.config, invoke, hfa, Val.toAdmin]
  have hne : ∀ (vs : List Val) (a : Admin) (l : List Admin), a.val? = none →
      ((Thread.invoke (allocHost s ft h).2 args).config (allocHost s ft h).1).code ≠
        vals vs ++ a :: l → True := fun _ _ _ _ _ => trivial
  clear hne
  have harity : hostArity? (allocHost s ft h).1 (allocHost s ft h).2 = some (h, args.length) := by
    simp [hostArity?, hfa, funcType?_ofFlatType, hargs]
  apply status_callout_of (E := .top [] []) (a := (allocHost s ft h).2)
  · intro vs hv
    rw [hcode] at hv
    exact Det.vals_ne_append_cons (e := .callRefType (ofFlatType ft)) (t := []) rfl hv.symm
  · rw [hcode]; intro hv
    have := congrArg List.getLast? hv
    simp at this
  · intro a hv
    rw [hcode] at hv
    have := congrArg List.getLast? hv
    simp [throwing] at this
  · rw [hcode, decompose?_top (n := args.length) (by rfl) harity le_rfl]
    simp

end Silmaril.Wasm.SingleThreaded
