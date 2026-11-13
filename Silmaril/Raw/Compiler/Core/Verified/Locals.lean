module

public import Silmaril.Compiler.Core.Verified.Actions.Defs

/-! # `main` with one `int` local initialised by a literal

Cerberus elaborates the block `{ int x = n; return x; }` (and `{ int x = n; }`) to

```
let strong x = create(Ivalignof(int), int) in
  { let strong t = bound(pure(n)) in store(int, x, conv_loaded_int(int, t)) } ;
  ( { let strong u = bound(let weak p = pure(x) in load(int, p)) in
        kill(int, x) ; run ret(conv_loaded_int(int, u)) } ; kill(int, x) ; pure(unit)
  | kill(int, x) ; pure(unit) )
```

`local file ret e` recognises these shapes syntactically and returns the literal and whether
the block returns `x`. The Core side (`local_reaches`): the `create` is answered by the
concrete memory with a fresh, live `int` object (`Actions.create_apply`, with the address
budget of `StartupMem`), the store writes `n` into it, the load reads `n` back
(`Mem.Concrete.load_int` on the bytes the store wrote), the `kill` ends it, and the `run`
leaves with `n`; a block without `return` reaches `unit`, then the return label's default `0`.

The Lir side keeps the local in a register: `r3 := n` for the store, `r0 := r3` for the load
of the `return`, `r0 := 0` for the fall-off default; `OpsLink.link_sound` gives the exit.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Locals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf argState)
open ReturnConst (focusMemory focusMemory_stdout)
open ConvInt (isConvLoadedInt IsInt intTy)
open Mem.Concrete (LiveInt PlainAt IntRange nextIntAddress)

variable {file : Program} {labels : Labels}

/-! ## Memory facts -/

/-- A focus only changes the current location. -/
theorem focusMemory_eq (ann : List Annot) (m : Mem.Concrete.State) :
    ∃ l, focusMemory ann m = {m with currentLocation := l} := by
  unfold focusMemory
  split
  · split
    · exact ⟨m.currentLocation, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨m.currentLocation, rfl⟩

theorem tagsOf_focus (ann : List Annot) (m : Mem.Concrete.State) :
    tagsOf file (focusMemory ann m) = tagsOf file m := by
  obtain ⟨l, h⟩ := focusMemory_eq ann m
  rw [h]; rfl

/-- What the slot of a local holding `n` satisfies in memory `m`. -/
structure Slot (m : Mem.Concrete.State) (id addr n : Int) : Prop where
  live : LiveInt m id addr
  plain : PlainAt m addr
  bytes : Mem.Concrete.fetchBytes 4 addr m.bytes = Mem.Concrete.encodeInteger 4 n

theorem liveInt_with {m m' : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (hd : m'.dead = m.dead) (ha : m'.allocations = m.allocations) : LiveInt m' id addr := by
  obtain ⟨alive, found⟩ := h
  exact ⟨by rw [hd]; exact alive, by rw [ha]; exact found⟩

theorem liveInt_focus {m : Mem.Concrete.State} {id addr : Int} (ann : List Annot)
    (h : LiveInt m id addr) : LiveInt (focusMemory ann m) id addr := by
  obtain ⟨l, hl⟩ := focusMemory_eq ann m
  rw [hl]; exact liveInt_with h rfl rfl

theorem slot_focus {m : Mem.Concrete.State} {id addr n : Int} (ann : List Annot)
    (h : Slot m id addr n) : Slot (focusMemory ann m) id addr n := by
  obtain ⟨l, hl⟩ := focusMemory_eq ann m
  obtain ⟨live, plain, bytes⟩ := h
  rw [hl]
  exact ⟨liveInt_with live rfl rfl, plain, bytes⟩

theorem slot_lastUsed {m : Mem.Concrete.State} {id addr n : Int} (u : Option Int)
    (h : Slot m id addr n) : Slot {m with lastUsed := u} id addr n := by
  obtain ⟨live, plain, bytes⟩ := h
  exact ⟨liveInt_with live rfl rfl, plain, bytes⟩

theorem liveInt_lastUsed {m : Mem.Concrete.State} {id addr : Int} (u : Option Int)
    (h : LiveInt m id addr) : LiveInt {m with lastUsed := u} id addr :=
  liveInt_with h rfl rfl

/-- A byte written below the fetched range does not change it. -/
theorem fetch_writeByte_below (n : Nat) {a c : Int} (h : a < c) (b : Mem.Concrete.Byte)
    (xs : Map Int Mem.Concrete.Byte) :
    Mem.Concrete.fetchBytes n c (Mem.Concrete.writeByte a b xs) = Mem.Concrete.fetchBytes n c xs := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.Concrete.fetchBytes, Mem.Concrete.readByte, Mem.Concrete.writeByte]
    rw [Map.lookup_insert_of_key_ne _ _ (show MapKey.key c ≠ MapKey.key a from
      fun e => by change c = a at e; omega)]
    have := ih (c := c + 1) (by omega)
    simp only [Mem.Concrete.writeByte] at this
    rw [this]

/-- Reading back the bytes of a plain representation. -/
theorem fetch_write (bs : List Mem.Concrete.Byte) (a : Int) (s : Mem.Concrete.State) :
    Mem.Concrete.fetchBytes bs.length a
      (Mem.Concrete.writeRepresentation a (Mem.Concrete.plainBytes bs) s).bytes = bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [Mem.Concrete.plainBytes, List.map_cons, Mem.Concrete.writeRepresentation,
      List.length_cons, Mem.Concrete.fetchBytes]
    rw [fetch_writeByte_below _ (by omega)]
    have := ih (a + 1)
    simp only [Mem.Concrete.plainBytes] at this
    rw [this]
    simp [Mem.Concrete.readByte, Mem.Concrete.writeByte]

/-- A plain representation leaves no pointer-copy metadata on its bytes. -/
theorem plain_write (bs : List Mem.Concrete.Byte) (a : Int) (s : Mem.Concrete.State) (i : Nat)
    (hi : i < bs.length) :
    (Mem.Concrete.writeRepresentation a (Mem.Concrete.plainBytes bs) s).pointerBytes.lookup
      (a + i) = none := by
  induction bs generalizing a i with
  | nil => simp at hi
  | cons b bs ih =>
    simp only [Mem.Concrete.plainBytes, List.map_cons, Mem.Concrete.writeRepresentation]
    cases i with
    | zero =>
      simp only [Map.lookup, Map.erase]
      have e : MapKey.key (a + ((0 : Nat) : Int)) = MapKey.key a := by
        change a + ((0 : Nat) : Int) = a
        simp
      rw [e]
      exact Finmap.lookup_erase _ _
    | succ i =>
      have := ih (a + 1) i (by simpa using hi)
      simp only [Mem.Concrete.plainBytes] at this
      rw [show a + ((i + 1 : Nat) : Int) = a + 1 + i by push_cast; ring]
      simp only [Map.lookup, Map.erase] at this ⊢
      rw [Finmap.lookup_erase_ne (by change a + 1 + i ≠ a; omega)]
      exact this

/-! ## Requests of the memory actions -/

theorem request_create {ann : List Annot} {l : Loc} {u : Unit} {al ty : PE} {pref : Prefix}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} :
    request file labels ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.create al ty pref))))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr al env) (.arguments (.memory (.create pref)) [] [ty] env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr al env))
        (.arguments (.memory (.create pref)) [] [ty] env :: k) := by
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr al env) (.arguments (.memory (.create pref)) [] [ty] env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr al env))
        (.arguments (.memory (.create pref)) [] [ty] env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem alignof_int (tags : Mem.Concrete.Tags) (c : List Annot) :
    primitive (.ctor .ivAlignof) [.ctype (Mem.Concrete.intType c)] tags = .ok (.object (.integer 4)) := by
  have hl := Mem.Concrete.layout_intType tags c
  unfold Mem.Concrete.intType at hl ⊢
  simp [primitive, Mem.Concrete.alignment, hl, integer, bind, Except.bind, pure, Except.pure]

theorem request_store {ann : List Annot} {l : Loc} {u : Unit} {ty p v : PE}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} :
    request file labels ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .store) [] [p, v] env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .store) [] [p, v] env :: k) := by
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr ty env) (.arguments (.memory .store) [] [p, v] env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .store) [] [p, v] env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem request_load {ann : List Annot} {l : Loc} {u : Unit} {ty p : PE}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} :
    request file labels ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load ty p .na))))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .load) [] [p] env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .load) [] [p] env :: k) := by
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr ty env) (.arguments (.memory .load) [] [p] env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .load) [] [p] env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

theorem request_kill {ann : List Annot} {l : Loc} {u : Unit} {ty : Ctype} {p : PE}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} :
    request file labels ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.kill (.static ty) p))))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.arguments (.memory (.kill ty)) [] [] env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments (.memory (.kill ty)) [] [] env :: k) := by
  simp only [request, requestAux, awaitsScheduling, arguments]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.arguments (.memory (.kill ty)) [] [] env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments (.memory (.kill ty)) [] [] env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

/-- A focused memory action: focus, evaluate the operands, apply. -/
theorem action_reaches {ann : List Annot} {e : ExprNode Codec.wireModel Unit Unit Sym}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} {op : Prim} {p : PE} {rest : List PE}
    {vs : List Val}
    (h : request file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.arguments op [] rest env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.arguments op [] rest env :: k))
    (hev : Eval file (tagsOf file m) env (.inr (p :: rest)) (.inr vs)) :
    Reaches file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ ⟨.apply op vs, k, focusMemory ann m⟩ :=
  (Straight.focus_reaches h).trans (by
    have hs := (Eval.sound file _ hev) labels op [] k (focusMemory ann m) (tagsOf_focus ann m)
    simpa [argState] using hs)

/-- `int`, as an operand. -/
abbrev intVal (a c : List Annot) : PE := .mk a () (.val (.ctype (.mk c (.basic (.integer (.signed .int))))))

theorem eval_intVal (tags : Mem.Concrete.Tags) (env : Env) (a c : List Annot) :
    Eval file tags env (.inl (intVal a c)) (.inl (.ctype (Mem.Concrete.intType c))) := .val

/-! ## The four actions on an `int` local -/

theorem nextIntAddress_focus (ann : List Annot) (m : Mem.Concrete.State) :
    nextIntAddress (focusMemory ann m) = nextIntAddress m := by
  obtain ⟨l, hl⟩ := focusMemory_eq ann m
  rw [hl]; rfl

theorem updateLastAllocation_lastAddress (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).lastAddress = s.lastAddress := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem updateLastAllocation_dead (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).dead = s.dead := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem writeRepresentation_dead (a : Int) (bs : Mem.Concrete.Representation)
    (s : Mem.Concrete.State) : (Mem.Concrete.writeRepresentation a bs s).dead = s.dead := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape a bs s
  rw [h]

theorem created_live (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State)
    (hdead : m.nextId ∉ m.dead) :
    LiveInt (Actions.created pref ann m) m.nextId (nextIntAddress m) := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape (nextIntAddress m)
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  refine ⟨?_, ?_⟩
  · simp [Actions.created, updateLastAllocation_dead, writeRepresentation_dead, hdead]
  · let A : Mem.Concrete.Allocation :=
      { base := nextIntAddress m, size := 4, objectType := some (Mem.Concrete.intType ann)
        readonlyKind := Mem.Concrete.readonlyKind pref }
    refine ⟨A, ?_, rfl, rfl, rfl, rfl⟩
    simp [Actions.created, Mem.Concrete.updateLastAllocation]
    rfl

theorem created_lastAddress (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (Actions.created pref ann m).lastAddress = nextIntAddress m := by
  simp [Actions.created, updateLastAllocation_lastAddress]

theorem created_dead (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (Actions.created pref ann m).dead = m.dead := by
  simp [Actions.created, updateLastAllocation_dead,
    writeRepresentation_dead]

/-- `create(Ivalignof(int), int)`. -/
theorem create_reaches (ann a1 a2 a3 c1 c2 : List Annot) (l : Loc) (u : Unit) (pref : Prefix)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.create (.mk a1 () (.ctor .ivAlignof [intVal a2 c1])) (intVal a3 c2) pref))))) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated (focusMemory ann m).nextId
        (nextIntAddress m)))), k, Actions.created pref c2 (focusMemory ann m)⟩ := by
  have hev : Eval file (tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [intVal a2 c1]), intVal a3 c2])
      (.inr [.object (.integer 4), .ctype (Mem.Concrete.intType c2)]) :=
    .cons (.ctor (.cons (eval_intVal _ env a2 c1) .nil) (alignof_int _ c1))
      (.cons (eval_intVal _ env a3 c2) .nil)
  refine (action_reaches request_create hev).trans ?_
  rw [← nextIntAddress_focus ann m]
  exact Actions.create_apply pref c2 k _ (by rw [nextIntAddress_focus]; exact hpos)

/-- The memory after a store of `n` into the slot at `addr`. -/
def stored (m : Mem.Concrete.State) (id addr n : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m with lastUsed := some id}

theorem stored_slot {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr) (n : Int) :
    Slot (stored m id addr n) id addr n := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  have hlen : (Mem.Concrete.encodeInteger 4 n).length = 4 := Mem.Concrete.encodeInteger_length 4 n
  refine ⟨?_, ?_, ?_⟩
  · unfold stored; rw [hw]; exact liveInt_with h rfl rfl
  · intro i hi
    exact plain_write _ addr m i (by omega)
  · have := fetch_write (Mem.Concrete.encodeInteger 4 n) addr m
    rw [hlen] at this
    exact this

theorem stored_stdout (m : Mem.Concrete.State) (id addr n : Int) :
    (stored m id addr n).stdout = m.stdout := by
  simp [stored, Actions.writeRepresentation_stdout]

/-- `store(int, x, conv_loaded_int(int, t))` with `x` a live `int` slot and `t = n`. -/
theorem store_reaches (ann a1 a2 a3 a4 a5 c1 c3 : List Annot) (l : Loc) (u : Unit) (x s t : Sym)
    (hs : isConvLoadedInt file s = true) (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (ht : env.lookup t = some (.loaded (.specified (.integer n)))) (hn : IntRange n)
    (live : LiveInt m id addr) :
    ∃ xs, Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.store false (intVal a1 c1) (.mk a2 () (.sym x))
          (.mk a3 () (.call (.sym s) [intVal a4 c3, .mk a5 () (.sym t)])) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations xs :: k, stored (focusMemory ann m) id addr n⟩ := by
  have hev : Eval file (tagsOf file m) env
      (.inr [intVal a1 c1, .mk a2 () (.sym x),
        .mk a3 () (.call (.sym s) [intVal a4 c3, .mk a5 () (.sym t)])])
      (.inr [.ctype (Mem.Concrete.intType c1), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]) :=
    .cons (eval_intVal _ env a1 c1) (.cons (.sym hx)
      (.cons (ConvInt.convLoadedInt_eval (ann := c3) hs hn
        (.cons (eval_intVal _ env a4 c3) (.cons (.sym ht) .nil))) .nil))
  obtain ⟨xs, hst⟩ := Actions.store_apply (file := file) (labels := labels) c1 k
    (liveInt_focus ann live) hn
  exact ⟨xs, (action_reaches request_store hev).trans hst⟩

/-- `load(int, p)` of the slot holding `n`. -/
theorem load_reaches (ann a1 a2 c1 : List Annot) (l : Loc) (u : Unit) (p : Sym)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hp : env.lookup p = some (.object (.pointer (.allocated id addr))))
    (hn : IntRange n) (slot : Slot m id addr n) :
    ∃ xs, Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.load (intVal a1 c1) (.mk a2 () (.sym p)) .na))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), .annotations xs :: k,
        {focusMemory ann m with lastUsed := some id}⟩ := by
  have hev : Eval file (tagsOf file m) env (.inr [intVal a1 c1, .mk a2 () (.sym p)])
      (.inr [.ctype (Mem.Concrete.intType c1), .object (.pointer (.allocated id addr))]) :=
    .cons (eval_intVal _ env a1 c1) (.cons (.sym hp) .nil)
  obtain ⟨live, plain, bytes⟩ := slot_focus ann slot
  obtain ⟨xs, hld⟩ := Actions.load_apply (file := file) (labels := labels) c1 k live plain hn bytes
  exact ⟨xs, (action_reaches request_load hev).trans hld⟩

/-- The memory after the `kill` of the slot `id`. -/
def killed (m : Mem.Concrete.State) (id : Int) : Mem.Concrete.State :=
  { m with allocations := m.allocations.erase id, dead := id :: m.dead, lastUsed := some id }

/-- `kill(int, x)` of a live slot. -/
theorem kill_reaches (ann a2 c1 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt m id addr) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static (Mem.Concrete.intType c1)) (.mk a2 () (.sym x))))))) env, k, m⟩
      ⟨.value .unit, k, killed (focusMemory ann m) id⟩ := by
  have hev : Eval file (tagsOf file m) env (.inr [.mk a2 () (.sym x)])
      (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym hx) .nil
  exact (action_reaches request_kill hev).trans
    (Actions.kill_apply c1 k (liveInt_focus ann live))

end Silmaril.Compile.Core.Verified.Locals
