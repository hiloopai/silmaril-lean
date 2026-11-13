module

public import Silmaril.Compiler.Core.Verified.ArgvMem.Defs
public import Silmaril.Compiler.Core.Verified.CfgArgvMem.Defs
public import Silmaril.Compiler.Core.Verified.LoopMainSound.Defs
public import Silmaril.Compiler.Core.Verified.CfgGlobals.Defs
public import Silmaril.Compiler.Core.Verified.PrintfArg.Defs
/-! # The start of `main(argc, argv)` with slots

`ArgvMem.initial_reaches_body_mem` reaches `main`'s body with the argument objects. The control-flow
graph machine of `CfgArgv` also reads `argc` as an `int` slot and creates its locals below the
argument objects, so it needs more of the startup memory (`initial_reaches_slots`): the `argc`
parameter object is a slot holding `argc` (`Locals.Slot`), the four bytes of `argc` lie between the
`argv` parameter object and the pointer array, the strings above the array
(`CfgArgvMem.StrAbove`), and the frontier is below every object, aligned, and far from zero.
`startObjects_args_sep` is `StartupArgs.startObjects_args` with these separation facts.

`creates_reaches_room`: creating the locals of `main`'s block (`LoopMain.creates`) from such a
memory (`Room`) keeps the slots, and each new local's four bytes lie below the frontier it started
from.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvStart

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open Silmaril.Cerberus.Core.StartupArgs
open Mem.Concrete (Tags Pointer MemoryValue Failure Byte Representation typeLayout allocateTyped
  storeTyped accessTyped loadTyped updateLastAllocation readonlyKind unatomic writeRepresentation
  plainBytes encodeInteger decodeInteger represent readByte fetchBytes registeredIntegerLayout
  registeredInteger integerLayout representationBounds encodeAddress representPointer nextIntAddress)
open StateMem (Local Inv ptr)
open StateStmt (Keys isFresh)
open StateExpr (Key)
open ReturnLit (Eff)
open LoopMain (creates)
open ArgvMem (Objs)

/-! ## The startup objects -/

theorem startObjects_args_sep (tags : Tags) (args : List String) (h : ∀ s ∈ args, Chars s)
    (hn : args.length < 2147483648) (loc : Loc) (main argc argv : Sym) (m : Mem.Concrete.State)
    (hdead : m.dead = []) (htop : m.lastAddress ≤ 281474976710655)
    (hroom : strRoom args + 8 * (args.length + 1) + 64 < m.lastAddress) :
    ∃ qs B C V m', startObjects tags m (args.map strObject ++
        [arrObject args.length loc main argv, argcObject args.length loc main argc,
         argvObject args.length loc main argv]) [] =
        .ok (qs ++ [.allocated (m.nextId + args.length) B, .allocated (m.nextId + args.length + 1) C,
          .allocated (m.nextId + args.length + 2) V], m') ∧
      Grows m m' ∧ m'.nextId = m.nextId + args.length + 3 ∧ m'.dead = [] ∧
      m.lastAddress - strRoom args - 8 * (args.length + 1) - 32 ≤ m'.lastAddress ∧
      StrPtrs m' m.nextId args qs ∧ ArrAt m' (m.nextId + args.length) B qs ∧
      IntAt m' (m.nextId + args.length + 1) C args.length ∧
      PtrAt m' (m.nextId + args.length + 2) V (m.nextId + args.length) B ∧
      0 < B ∧ B + 8 * (args.length + 1) ≤ 281474976710655 ∧ m'.lastAddress = V ∧ V < C ∧ C < B ∧
      V + 8 ≤ C ∧ C + 4 ≤ B ∧
      ∀ (i : Nat) (b : Int), qs[i]? = some (.allocated (m.nextId + i) b) → B + 8 * (args.length + 1) ≤ b := by
  have hr0 : 0 ≤ strRoom args := Int.natCast_nonneg _
  obtain ⟨qs, m1, hs, g1, hn1, hl1, hptrs⟩ := startObjects_strings tags args m [] h hdead htop (by omega)
  have hlen : qs.length = args.length := hptrs.1
  have hlenI : (qs.length : Int) = args.length := by rw [hlen]
  have hq : ∀ q ∈ qs, ∃ id b, q = .allocated id b ∧ 0 ≤ b ∧ b < 18446744073709551616 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨b, hb, -, -, hbtop, hbpos⟩ := hptrs.2 i args[i] (by
      rw [List.getElem?_eq_getElem (by omega)])
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hb
    exact ⟨_, b, hb, by omega, by omega⟩
  have hd1 : m1.dead = [] := by rw [g1.dead, hdead]
  set B := nextBase m1 (((qs.length : Int) + 1) * 8) 8 with hB
  obtain ⟨hB1, hB2⟩ := nextBase_ge m1 (((qs.length : Int) + 1) * 8) 8 (by norm_num)
  obtain ⟨m2, hcs2, g2, hn2, hl2, harr⟩ := createStore_array tags m1 qs loc main argv hq hd1 (by omega)
  have hd2 : m2.dead = [] := by rw [g2.dead, hd1]
  set C := nextBase m2 4 4 with hC
  obtain ⟨hC1, hC2⟩ := nextBase_ge m2 4 4 (by norm_num)
  obtain ⟨m3, hcs3, g3, hn3, hl3, hint⟩ := createStore_argc tags m2 args.length hn loc main argc hd2
    (by omega)
  have hd3 : m3.dead = [] := by rw [g3.dead, hd2]
  set V := nextBase m3 8 8 with hV
  obtain ⟨hV1, hV2⟩ := nextBase_ge m3 8 8 (by norm_num)
  obtain ⟨m4, hcs4, g4, hn4, hl4, hptr⟩ := createStore_argv tags m3 args.length (m1.nextId) B
    (by omega) (by omega) loc main argv hd3 (by omega)
  refine ⟨qs, B, C, V, m4, ?_, g1.trans (g2.trans (g3.trans g4)), by rw [hn4, hn3, hn2, hn1]; ring,
    by rw [g4.dead, hd3], by omega, ?_, ?_, ?_, ?_, by omega, by omega, hl4, by omega, by omega,
    by omega, by omega, ?_⟩
  · rw [startObjects_append, hs]
    simp only [List.nil_append, bind, Except.bind, startObjects, arrObject, Startup.contents]
    have e1 : (.array (qs.map (.pointer Startup.charType) ++
        [.pointer Startup.charType (.null Startup.charType)]) : MemoryValue) = arrValue qs := rfl
    simp only [pure, Except.pure, e1]
    rw [show (⟨.mk [] (.array Startup.charPointer (some (args.length + 1))), .pointers,
      .source loc [main, argv]⟩ : Startup.Object) = arrObject qs.length loc main argv by rw [hlen]; rfl,
      hcs2]
    simp only [argcObject]
    rw [show (⟨Startup.intType, .literal (.integer (.signed .int) args.length), .source loc [main, argc]⟩ :
      Startup.Object) = argcObject args.length loc main argc from rfl, hcs3]
    simp only [argvObject]
    rw [← hB]
    rw [List.getElem?_append_left (by simp [hlen]), List.getElem?_append_right (by omega),
      hlen, Nat.sub_self]
    simp only [List.getElem?_cons_zero]
    rw [show (⟨Startup.argvType, .arrayPointer args.length, .source loc [main, argv]⟩ :
      Startup.Object) = argvObject args.length loc main argv from rfl, hcs4]
    simp only [hn1, hn2, hn3, List.append_assoc, List.cons_append, List.nil_append, ← hC, ← hV]
    congr 3; ring_nf
  · refine ⟨hlen, fun i s hi => ?_⟩
    obtain ⟨b, hb, hstr, hlast, hbtop, hbpos⟩ := hptrs.2 i s hi
    exact ⟨b, hb, hstr.grows (g2.trans (g3.trans g4)) (by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega) hlast,
      (g2.trans (g3.trans g4)).last.trans hlast, hbtop, hbpos⟩
  · rw [← hn1]
    exact harr.grows (g3.trans g4) (by omega) (by rw [hl2])
  · rw [show m.nextId + args.length + 1 = m2.nextId by rw [hn2, hn1]]
    exact hint.grows g4 (by omega) (by rw [hl3])
  · rw [show m.nextId + args.length + 2 = m3.nextId by rw [hn3, hn2, hn1]; ring,
      show m.nextId + args.length = m1.nextId by rw [hn1]]
    exact hptr
  · intro i b hb
    have hi : i < args.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1; omega
    obtain ⟨b', hb', -, hlast, -, -⟩ := hptrs.2 i args[i] (List.getElem?_eq_getElem hi)
    rw [hb, Option.some.injEq, Pointer.allocated.injEq] at hb'
    obtain ⟨-, rfl⟩ := hb'
    have : (qs.length : Int) = args.length := hlenI
    omega


/-- `errno` is the next 4-byte object. -/
theorem createErrno_next (tags : Tags) (m : Mem.Concrete.State) (hdead : m.dead = [])
    (hpos : 0 < nextBase m 4 4) :
    ∃ p m', createErrno tags m = .ok (p, m') ∧ Grows m m' ∧ m'.nextId = m.nextId + 1 ∧
      m'.lastAddress = nextBase m 4 4 := by
  obtain ⟨m', hcs, g, hn, hl, -⟩ := createStore_spec ∅ m errnoObject (.integer (.signed .int) 0)
    (StartupReach.layout_int ∅) (by simp [errnoObject, StartupReach.intTy]) (by norm_num) (by norm_num)
    hpos (by simp [hdead]) (n := .integer (.signed .int) 0) rfl
    (fun s => represent_signedInt 63 ∅ s (n := 0) (by norm_num) (by norm_num))
    (by simp [plainBytes, length_encodeInteger])
  exact ⟨_, m', (createErrno_eq tags m).trans hcs, g, hn, hl⟩

/-- An `int` startup object is a slot. -/
theorem IntAt.slot {m : Mem.Concrete.State} {id C n : Int} (h : IntAt m id C n) : Locals.Slot m id C n := by
  obtain ⟨⟨⟨r, hr, hb, hs, ha⟩, hd⟩, bytes, plain, ro⟩ := h
  exact ⟨⟨hd, r, hr, hb, hs, ha, ro r hr⟩, plain, bytes⟩

/-- **`main(argc, argv)` starts with the slot of `argc` and the argument objects above the
frontier.** -/
theorem initial_reaches_slots (file : Program) (enums : Map Sym IntegerType) (args : List String)
    (h : Spec.ArgsOk args) {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {argc argv : Sym}
    {tc tv : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body))
    (normal : file.callingConvention = .normal) :
    ∃ s labels xs qs V C B m, initial file enums args = .ok (s, labels) ∧
      StartupReach.Reaches file labels s ⟨.effectExpr body
        (extendEnv [(argc, .object (.pointer (.allocated (args.length + 1) C))),
          (argv, .object (.pointer (.allocated (args.length + 2) V)))] ∅),
        [.annotations xs], m⟩ ∧
      m.stdout = "" ∧ Objs m args (args.length + 2) V args.length B qs ∧
      Locals.Slot m (args.length + 1) C args.length ∧ m.dead = [] ∧ args.length + 3 ≤ m.nextId ∧
      m.lastAddress ≤ V ∧ V + 8 ≤ C ∧ C + 4 ≤ B ∧ CfgArgvMem.StrAbove args B qs ∧
      140737488355328 ≤ m.lastAddress ∧ m.lastAddress % 4 = 0 := by
  have hc := ArgvReloc.chars_of_argsOk h
  have hroom := ArgvReloc.room_of_argsOk h
  have hr0 : 0 ≤ strRoom args := Int.natCast_nonneg _
  let m0 : Mem.Concrete.State := {enumTypes := enums}
  obtain ⟨qs, B, C, V, m1, hs, g, hn, hd, hpos, hptrs, harr, hint, hptr, hB0, hBtop, hlV, hVC, hCB,
    hV8, hC4, habove⟩ :=
    startObjects_args_sep file.tagDefs args hc (by omega) loc sym argc argv m0 rfl (by simp [m0]) (by
      simp [m0]; omega)
  have hn0 : m0.nextId = 0 := rfl
  simp only [hn0, Int.zero_add] at hs hn harr hint hptr hptrs habove
  obtain ⟨hb1, hb2⟩ := nextBase_ge m1 4 4 (by norm_num)
  have hlast : (281474976710655 : Int) - 4096 - 32 ≤ m1.lastAddress := by
    change (281474976710655 : Int) - _ - _ - _ ≤ _ at hpos; omega
  obtain ⟨pe, m2, herrno, g2, hn2, hl2⟩ := createErrno_next ⟨file.tagDefs, m1.enumTypes⟩ m1 hd (by omega)
  obtain ⟨s, labels, xs, hinit, hreach⟩ := initial_reaches_body_args file enums args nodefs main decl normal
    (objects_ok' args hc loc sym argc argv) hs herrno
  have hpv := Argc.paramValues_tail qs (.allocated args.length B) (.allocated (args.length + 1) C)
    (.allocated (args.length + 2) V)
  rw [hpv] at hreach
  have hlen : qs.length = args.length := hptrs.1
  have hnext : m1.nextId = args.length + 3 := by rw [hn]
  refine ⟨s, labels, xs, qs, V, C, B, _, hinit, hreach, by simpa [m0] using g2.stdout.trans g.stdout,
    ?_, ?_, by simp [g2.dead, hd], by simp [hn2, hnext], by simp [hl2]; omega, hV8, hC4,
    fun i b hb => habove i b (by simpa using hb), by simp [hl2]; omega, by simp only [hl2, nextBase]; omega⟩
  · refine Objs.reads (m := m2) ⟨?_, ?_, ?_, hB0, hBtop⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl⟩⟩
    · exact hptr.grows g2 (by omega) (by omega)
    · exact harr.grows g2 (by omega) (by omega)
    · refine ⟨hlen, fun i str hstr => ?_⟩
      obtain ⟨b, hq, hat, hlb, htop, hbpos⟩ := hptrs.2 i str hstr
      have hi : i < args.length := (List.getElem?_eq_some_iff.mp hstr).1
      exact ⟨b, hq, hat.grows g2 (by omega) hlb, g2.last.trans hlb, htop, hbpos⟩
  · have := IntAt.slot (hint.grows g2 (by omega) (by omega))
    exact ⟨⟨this.live.alive, this.live.found⟩, this.plain, this.bytes⟩

/-! ## Creating the locals -/

/-- The memory before creating locals: no dead objects, the slots `ls` below the next identifier
and above the frontier, which is aligned with room for `K` slots. -/
structure Room (m : Mem.Concrete.State) (ls : List Local) (K : Nat) : Prop where
  dead : m.dead = []
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr
  aligned : m.lastAddress % 4 = 0
  room : 4 * ((K : Int) - ls.length + 1) < m.lastAddress

variable {file : Program} {labels : Labels}

/-- Creating locals keeps the slots; each new local lies below the frontier. -/
theorem creates_reaches_room (xs : List Sym) (e : Eff) {ys : List Sym} {e' : Eff}
    (h : creates xs e = some (ys, e')) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    {K : Nat} (fresh : Room m ls K) (hK : ys.length ≤ K) (k : List Frame) :
    ∃ env' m' ls', Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.effectExpr e' env', k, m'⟩ ∧
      Inv env' m' ls' ds ∧ Keys ls' ys ∧ m'.stdout = m.stdout ∧ Room m' ls' K ∧
      m'.lastAddress ≤ m.lastAddress ∧ (∀ l ∈ ls', l ∈ ls ∨ l.addr + 4 ≤ m.lastAddress) ∧
      StrMem.Keeps m m' ∧ ∀ y : Sym, isFresh ys y = true → env'.lookup y = env.lookup y := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold creates at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
      have hsub := (CfgGlobals.creates_sublist (xs ++ [x]) rest h).length_le
      simp only [List.length_append, List.length_singleton] at hsub
      have hnext : nextIntAddress m = m.lastAddress - 4 := by
        have := fresh.aligned
        simp only [nextIntAddress]; omega
      have hpos : 0 < nextIntAddress m := by
        have := fresh.room
        rw [hnext]; omega
      let REST := rest
      let K' := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      have create := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
        pref env K' m hpos
      rw [State.focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let m₁ := Actions.created pref c2 (ReturnConst.focusMemory ann m)
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := ReturnLit.bind_reaches (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) ds := by
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
            rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
          · obtain rfl := List.mem_singleton.mp hl
            have := Locals.created_live pref c2 (ReturnConst.focusMemory ann m)
              (by rw [State.focus_dead, fresh.dead, State.focus_nextId]; simp)
            rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
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
        · intro q d hd
          obtain ⟨ok, l, hl, hk, slot⟩ := inv.defs q d hd
          refine ⟨ok, l, List.mem_append_left _ hl, hk, ?_⟩
          exact (Globals.held_created pref c2
            (Globals.held_focus ann ⟨slot, ids l hl, addrs l hl⟩)).slot
      have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls]
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Room m₁ (ls ++ [nl]) K := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [Locals.created_dead, State.focus_dead, fresh.dead]
        · intro l hl
          rw [State.created_nextId, State.focus_nextId]
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
        · rw [last₁]; have := fresh.aligned; omega
        · rw [last₁, List.length_append, List.length_singleton]
          have := fresh.room
          push_cast at this ⊢
          omega
      obtain ⟨env', m', ls', reach, inv', hls', out', fresh', below', news', keeps', look'⟩ :=
        creates_reaches_room (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ hK k
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      have keeps₁ : StrMem.Keeps m m₁ := by
        obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
        have k₀ : StrMem.Keeps m (ReturnConst.focusMemory ann m) := by
          rw [hl]; exact (StrMem.Keeps.refl m).location l
        exact k₀.trans (PrintfArg.created_keeps pref c2 _)
      have hxys : x ∈ ys := (CfgGlobals.creates_sublist (xs ++ [x]) rest h).subset (by simp)
      refine ⟨env', m', ls', (ReturnConst.sequence_reaches file labels a _ _ REST env k m).trans
        (create.trans (bind.trans reach)), inv', hls', out'.trans out, fresh', by omega, ?_,
        keeps₁.trans keeps', fun y hy => by
          rw [look' y hy, ConvInt.lookup_one_other]
          intro e
          have := List.all_eq_true.mp hy x hxys
          simp [e] at this⟩
      intro l hl
      rcases news' l hl with hl | hl
      · rcases List.mem_append.mp hl with hl | hl
        · exact .inl hl
        · obtain rfl := List.mem_singleton.mp hl
          right
          show nextIntAddress m + 4 ≤ m.lastAddress
          omega
      · right; omega
    next => cases h
  next =>
    cases h
    exact ⟨env, m, ls, .refl, inv, hls, rfl, fresh, le_rfl, fun l hl => .inl hl, StrMem.Keeps.refl m,
      fun _ _ => rfl⟩
termination_by sizeOf e

end Silmaril.Compile.Core.Verified.ArgvStart
