module

public import Silmaril.Proofs.Project.CompilesTo.O0Segments

/-!
# The entry segment of gcc `-O0` leaf code

From the System V call to the first statement point: the machine runs the prologue
(`push %rbp; mov %rsp,%rbp`) and spills the integer arguments into their frame slots
(`spills_run`); the Core enters the procedure body, creates the body's `int` locals
(`creates_run`) and enters the first statement. `FnData.segment_entry` puts them together;
every hypothesis is a decidable fact about the `FnData`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.X86 (Reg)
open Silmaril.X86.Ext (Mem Sz HoldsLE Stored leBytes)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open StateMem (Inv Defined defsOf update ptr)

/-! ## The prologue -/

/-- `push %rbp; mov %rsp,%rbp` from a System V entry: the frame invariant holds after it, and
every register but `rsp` and `rbp` is the entry one. -/
theorem prologue {F : FnData} {args : Silmaril.X86.SystemV.CApi.Arguments F.sig.arguments} {x0 : MState}
    (he : MachineEntry F.sig F.addr F.code F.frame args x0)
    (haddr : F.addr + F.code.length < 2 ^ 64) (hfr : 8 ≤ F.frame) (hlen : 4 ≤ F.code.length)
    (hpush : Silmaril.X86.Open.decode ((F.code.drop 0).take 1) = some (.base (.push .rbp), 1))
    (hmov : Silmaril.X86.Open.decode ((F.code.drop 1).take 3) =
      some (.base (.mov .q (.reg .rbp) .rsp), 3)) :
    ∃ m1 m2, Silmaril.X86.Open.step x0 = some m1 ∧ Silmaril.X86.Open.step m1 = some m2 ∧
      m1.core.rip = BitVec.ofNat 64 (F.addr + 1) ∧
      m1.core.read .rsp = x0.core.read .rsp - 8#64 ∧
      m2.core.rip = BitVec.ofNat 64 (F.addr + 4) ∧ Frame0 F.addr F.code F.frame x0 m2 ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → m2.core.read r = x0.core.read r) := by
  have hroom : F.frame ≤ (x0.core.read .rsp).toNat := he.room
  have hsub : (x0.core.read .rsp - 8#64).toNat = (x0.core.read .rsp).toNat - 8 := by
    rw [BitVec.toNat_sub]; have := (x0.core.read .rsp).isLt; simp; omega
  have hw : x0.memory.Permitted .write (x0.core.read .rsp - 8#64).toNat 8 := by
    rw [hsub]; exact permitted_sub he.rw.2 (by omega) (by omega) (by omega)
  obtain ⟨after, hpushed, hstored⟩ :=
    Silmaril.X86.Ext.pushWord_isSome (s := x0.core) (v := x0.core.read .rbp) hw
  have hrip0 : x0.core.rip = BitVec.ofNat 64 (F.addr + 0) := by rw [Nat.add_zero]; exact he.rip
  let c1 : Silmaril.X86.State := { x0.core.write .rsp (x0.core.read .rsp - 8#64) with
    rip := BitVec.ofNat 64 (F.addr + 0 + 1) }
  have hs1 : Silmaril.X86.Open.step x0 = some ⟨c1, after⟩ := by
    refine Silmaril.X86.Open.step_of_listed he.loaded (rip_add hrip0) (by omega) hpush ?_
    simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec]
    rw [hpushed]
    simp [Silmaril.X86.Ext.retire, rip_next hrip0, c1]
  have hl1 : Silmaril.X86.Ext.Loaded after (BitVec.ofNat 64 F.addr) F.code := by
    refine Silmaril.X86.Ext.Loaded.of_stored he.loaded hstored ?_
    have ha : (BitVec.ofNat 64 F.addr).toNat = F.addr := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [ha, hsub, Silmaril.X86.length_encodeWords_singleton]
    rcases he.apart with h | h
    · left; omega
    · right; omega
  have hrip1 : c1.rip = BitVec.ofNat 64 (F.addr + 1) := by show BitVec.ofNat 64 (F.addr + 0 + 1) = _; rfl
  let c2 : Silmaril.X86.State := { Sz.q.write c1 .rbp (Sz.q.read c1 .rsp) with
    rip := BitVec.ofNat 64 (F.addr + 1 + 3) }
  have hs2 : Silmaril.X86.Open.step ⟨c1, after⟩ = some ⟨c2, after⟩ := by
    refine Silmaril.X86.Open.step_of_listed hl1 (rip_add hrip1) (by omega) hmov ?_
    simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      rip_next hrip1, c2]
  have hc1rsp : c1.read .rsp = x0.core.read .rsp - 8#64 :=
    Silmaril.X86.State.read_write_same x0.core .rsp (x0.core.read .rsp - 8#64)
  have hc2rbp : c2.read .rbp = x0.core.read .rsp - 8#64 := by
    show (Sz.q.write c1 .rbp (Sz.q.read c1 .rsp)).read .rbp = _
    simp [Sz.write, Sz.read, hc1rsp]
  have hc2rsp : c2.read .rsp = x0.core.read .rsp - 8#64 := by
    show (Sz.q.write c1 .rbp (Sz.q.read c1 .rsp)).read .rsp = _
    simp only [Sz.write]
    rw [Silmaril.X86.State.read_write_other _ _ _ _ (by decide)]
    exact hc1rsp
  have hc2other : ∀ r, r ≠ .rsp → r ≠ .rbp → c2.read r = x0.core.read r := by
    intro r h1 h2
    show (Sz.q.write c1 .rbp (Sz.q.read c1 .rsp)).read r = _
    simp only [Sz.write]
    rw [Silmaril.X86.State.read_write_other _ _ _ _ h2]
    show (x0.core.write .rsp _).read r = _
    rw [Silmaril.X86.State.read_write_other _ _ _ _ h1]
  refine ⟨⟨c1, after⟩, ⟨c2, after⟩, hs1, hs2, hrip1, hc1rsp, rfl, ?_, hc2other⟩
  refine ⟨hl1, he.abi, he.room, he.rw, he.apart, hc2rbp, hc2rsp, ?_, ?_, ?_⟩
  · show after.readWith .read _ 8 = _
    have hr : x0.memory.Permitted .read (x0.core.read .rsp - 8#64).toNat
        (encodeWords [x0.core.read .rbp]).length := by
      rw [hsub, Silmaril.X86.length_encodeWords_singleton]
      exact permitted_sub he.rw.1 (by omega) (by omega) (by omega)
    have := hstored.readWith_self (access := .read) hr
    rw [Silmaril.X86.length_encodeWords_singleton, hsub] at this
    exact this
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hc2other _ (by decide) (by decide)
  · refine (Memory.WritesWithin.refl x0.memory _).step hstored fun off hoff => ?_
    rw [Silmaril.X86.length_encodeWords_singleton] at hoff
    rw [hsub]
    exact ⟨by omega, by omega⟩

/-! ## The argument spills -/

/-- The spills from offset `o`: each `(r, d, n)` is `mov %r32, d(%rbp)` (three bytes), with
`d = -n`. Decided by the kernel. -/
def spillsAt (code : List Byte) : Nat → List (Reg × BitVec 32 × Nat) → Bool
  | _, [] => true
  | o, (r, d, _) :: sp =>
    decide (Silmaril.X86.Open.decode ((code.drop o).take 3) =
      some (.base (.mov .d (.mem (Mem.ofReg .rbp none d)) r), 3)) && spillsAt code (o + 3) sp

/-- **The argument spills run**: from offset `o`, each spill stores the low half of its register
into its slot, `n` bytes below the saved `rbp`, keeping the frame, every register (but `rip`) and
every other slot; the states between two spills are no cut points. -/
theorem spills_run (F : FnData) (k0 : List Frame) (x0 : MState)
    (haddr : F.addr + F.code.length < 2 ^ 64) (hpts : ∀ q ∈ F.points, q.off < F.code.length) :
    ∀ (sp : List (Reg × BitVec 32 × Nat)) (o : Nat) (m : MState), sp ≠ [] →
      Frame0 F.addr F.code F.frame x0 m → m.core.rip = BitVec.ofNat 64 (F.addr + o) →
      spillsAt F.code o sp = true →
      (∀ x ∈ sp, x.2.1.signExtend 64 = -(BitVec.ofNat 64 x.2.2) ∧ 4 ≤ x.2.2 ∧
        x.2.2 + 8 ≤ F.frame) →
      sp.Pairwise (fun x y => x.2.2 + 4 ≤ y.2.2 ∨ y.2.2 + 4 ≤ x.2.2) →
      (∀ i, 0 < i → i < sp.length → ∀ q ∈ F.points, q.off ≠ o + 3 * i) →
      o + 3 * sp.length ≤ F.code.length →
      ∃ m', Hop (F.corr Silmaril.X86.Open.isa k0).tgtStep
          ((F.corr Silmaril.X86.Open.isa k0).tgtCut x0) m m' ∧
        m'.core.rip = BitVec.ofNat 64 (F.addr + o + 3 * sp.length) ∧
        (∀ r, m'.core.read r = m.core.read r) ∧ Frame0 F.addr F.code F.frame x0 m' ∧
        (∀ x ∈ sp, HoldsLE m'.memory ((x0.core.read .rsp).toNat - 8 - x.2.2) 4
          (((m.core.read x.1).setWidth 32).setWidth 64)) ∧
        (∀ a (v : BitVec 64), (∀ x ∈ sp, a + 4 ≤ (x0.core.read .rsp).toNat - 8 - x.2.2 ∨
            (x0.core.read .rsp).toNat - 8 - x.2.2 + 4 ≤ a) →
          HoldsLE m.memory a 4 v → HoldsLE m'.memory a 4 v)
  | [], _, _, h, _, _, _, _, _, _, _ => absurd rfl h
  | (r, d, n) :: rest, o, m, _, hf, hrip, hsp, hdisp, hpw, hmid, hfit => by
    simp only [spillsAt, Bool.and_eq_true, decide_eq_true_eq] at hsp
    obtain ⟨hdec, hrest⟩ := hsp
    obtain ⟨hd, hn4, hnf⟩ := hdisp (r, d, n) (by simp)
    dsimp only at hd hn4 hnf
    have hlen : o + 3 ≤ F.code.length := by simp only [List.length_cons] at hfit; omega
    obtain ⟨after, hs, hstored⟩ := step_store32 hf hrip hlen hdec hd hn4 hnf
    have hrsp0 := hf.rsp0
    let m1 : MState := ⟨{ m.core with rip := BitVec.ofNat 64 (F.addr + o + 3) }, after⟩
    have hf1 : Frame0 F.addr F.code F.frame x0 m1 :=
      hf.store haddr hstored (by omega) (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
        rfl rfl (fun _ _ => rfl)
    have hown : HoldsLE after ((x0.core.read .rsp).toNat - 8 - n) 4
        (((m.core.read r).setWidth 32).setWidth 64) :=
      Silmaril.X86.Ext.HoldsLE.of_stored_self hstored (hf.readable (by omega) (by omega) (by omega))
    have hother : ∀ a (v : BitVec 64), (a + 4 ≤ (x0.core.read .rsp).toNat - 8 - n ∨
        (x0.core.read .rsp).toNat - 8 - n + 4 ≤ a) → HoldsLE m.memory a 4 v → HoldsLE after a 4 v :=
      fun a v ha hv => Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored hv
        (by rw [Silmaril.X86.Ext.length_leBytes]; exact ha)
    cases rest with
    | nil =>
      refine ⟨m1, .one hs, by simp [m1], fun _ => rfl, hf1, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact hown
      · intro a v ha hv
        exact hother a v (ha (r, d, n) (by simp)) hv
    | cons y rest' =>
      have hrip1 : m1.core.rip = BitVec.ofNat 64 (F.addr + (o + 3)) := by
        show BitVec.ofNat 64 (F.addr + o + 3) = _; rw [Nat.add_assoc]
      have hnc : ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x0 m1 :=
        F.notCut (o := o + 3) hrip1 (fun q hq => by
            have := hmid 1 (by omega) (by simp) q hq; omega)
          (by simp only [List.length_cons] at hfit; omega) hpts haddr hf1.rsp
      obtain ⟨m', hop, hrip', hregs, hf', hholds, hkeep⟩ := spills_run F k0 x0 haddr hpts
        (y :: rest') (o + 3) m1 (by simp) hf1 hrip1 hrest
        (fun x hx => hdisp x (List.mem_cons_of_mem _ hx)) (List.pairwise_cons.mp hpw).2
        (fun i hi1 hi2 q hq => by
          have := hmid (i + 1) (by omega) (by simp only [List.length_cons] at hi2 ⊢; omega) q hq
          omega)
        (by simp only [List.length_cons] at hfit ⊢; omega)
      refine ⟨m', .more hs hnc hop, ?_, fun r' => (hregs r').trans rfl, hf', ?_, ?_⟩
      · rw [hrip']; simp only [List.length_cons]; congr 1; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · refine hkeep _ _ (fun z hz => ?_) hown
          have hz' := (List.pairwise_cons.mp hpw).1 z hz
          obtain ⟨-, hz4, hzf⟩ := hdisp z (List.mem_cons_of_mem _ hz)
          dsimp only at hz' ⊢
          omega
        · exact hholds x hx
      · intro a v ha hv
        exact hkeep a v (fun x hx => ha x (List.mem_cons_of_mem _ hx))
          (hother a v (ha (r, d, n) (by simp)) hv)

/-! ## Creating the body's locals -/

/-- The parts of `sseq x (create(Ivalignof(int), int)) rest`. -/
def createParts : EE → Option (Sym × EE)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
      if Locals.createInt cr = true then some (x, rest) else none
  | _ => none

theorem createParts_inv {e rest : EE} {x : Sym} (h : createParts e = some (x, rest)) :
    ∃ a p ty cr, e = .mk a (.sseq (.mk p (.base (some x, ty))) cr rest) ∧
      Locals.createInt cr = true := by
  unfold createParts at h
  split at h
  · split at h
    · rename_i hcr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, _, _, _, rfl, hcr⟩
    · cases h
  · cases h

/-- `blk` creates the `int` locals `xs` in order (`sseq x (create(…)) …`), then is the result. -/
def afterCreates : List Sym → EE → Option EE
  | [], e => some e
  | x :: xs, e =>
    match createParts e with
    | some (x', rest) => if x'.key = x.key then afterCreates xs rest else none
    | none => none

section Creates

variable {file : Program} {labels : Labels}

/-- **The creates run**: each creates a fresh `int` object below the others, bound to its symbol,
without a definition. -/
theorem creates_run : ∀ (xs : List Sym) (blk rest : EE), afterCreates xs blk = some rest →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State) (ls : List Local) (ds : Defs),
    Inv env m ls ds → Alloc m ls → 4 * xs.length + 4 < m.lastAddress →
    (ls.map (·.sym.key) ++ xs.map (·.key)).Nodup →
    ∃ (env' : Env) (m' : Mem.Concrete.State) (news : List Local),
      SeqReach.Reaches file labels ⟨.effectExpr blk env, k, m⟩ ⟨.effectExpr rest env', k, m'⟩ ∧
      news.map (·.sym.key) = xs.map (·.key) ∧ Inv env' m' (ls ++ news) ds ∧
      Alloc m' (ls ++ news) ∧ m'.lastAddress = m.lastAddress - 4 * xs.length
  | [], blk, rest, h, env, k, m, ls, ds, inv, al, _, _ => by
    simp only [afterCreates, Option.some.injEq] at h
    subst h
    exact ⟨env, m, [], .refl, rfl, by simpa using inv, by simpa using al, by simp⟩
  | x :: xs, blk, rest, h, env, k, m, ls, ds, inv, al, hroom, hnd => by
    simp only [afterCreates] at h
    split at h
    · rename_i x' rest0 hparts
      split at h
      · rename_i hxk
        obtain ⟨a, p, ty, cr, rfl, hcr⟩ := createParts_inv hparts
        have hfx : ∀ l ∈ ls, l.sym.key ≠ x'.key := by
          intro l hl he
          rw [hxk] at he
          have h1 : l.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl
          have h2 : x.key ∈ (x :: xs).map (·.key) := by simp
          exact (List.nodup_append.mp hnd).2.2 _ h1 _ h2 he
        obtain ⟨m1, r1, inv1, al1, last1⟩ := create_extends (file := file) (labels := labels)
          (ann := a) (p := p) (ty := ty) (rest := rest0) (k := k) hcr inv al (by omega) hfx
        have hnd1 : ((ls ++ [(⟨x', m.nextId, Mem.Concrete.nextIntAddress m⟩ : Local)]).map
            (·.sym.key) ++ xs.map (·.key)).Nodup := by
          simpa [hxk, List.append_assoc] using hnd
        obtain ⟨env', m', news, r2, hkeys, inv2, al2, last2⟩ := creates_run xs rest0 rest h _ k m1
          _ ds inv1 al1 (by rw [last1]; simp only [List.length_cons] at hroom; omega) hnd1
        refine ⟨env', m', (⟨x', m.nextId, Mem.Concrete.nextIntAddress m⟩ : Local) :: news,
          r1.trans r2, ?_,
          by simpa [List.append_assoc] using inv2, by simpa [List.append_assoc] using al2, ?_⟩
        · simp [hkeys, hxk]
        · rw [last2, last1]; simp only [List.length_cons]; omega
      · cases h
    · cases h

end Creates

/-! ## Arguments, parameters and slots -/

theorem intArgRegs_ne (i : Nat) :
    (Silmaril.X86.sysv64.intArgRegs[i]?.getD .rax) ≠ .rsp ∧
      (Silmaril.X86.sysv64.intArgRegs[i]?.getD .rax) ≠ .rbp := by
  cases h : Silmaril.X86.sysv64.intArgRegs[i]? with
  | none => exact ⟨by decide, by decide⟩
  | some r =>
    have hm := List.mem_of_getElem? h
    simp only [Option.getD_some]
    have : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9] := hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- The `int` arguments of a System V call in their registers. -/
theorem argsAt_regs {x0 : MState} :
    ∀ {kinds : List Silmaril.X86.SystemV.CApi.Scalar} (args : Silmaril.X86.SystemV.CApi.Arguments kinds) (base : Nat),
    (∀ k ∈ kinds, k = .int32) → Silmaril.X86.SystemV.ArgumentsAt x0 args base →
    ∀ i, i < kinds.length → base + i < 6 →
      ∃ w : BitVec 32,
        (x0.core.read (Silmaril.X86.sysv64.intArgRegs[base + i]?.getD .rax)).setWidth 32 = w ∧
        (Silmaril.Project.Shapes.C.argValues args)[i]? = some w.toInt
  | _, .nil, _, _, _, i, hi, _ => absurd hi (by simp)
  | _, .cons (kind := kind) v tail, base, hk, hat, i, hi, hb => by
    obtain rfl : kind = .int32 := hk kind (by simp)
    obtain ⟨⟨word, hword, henc⟩, hrest⟩ := hat
    cases i with
    | zero =>
      refine ⟨v, ?_, by simp [Silmaril.Project.Shapes.C.argValues, Silmaril.X86.SystemV.CApi.Scalar.signed]⟩
      unfold Silmaril.X86.SystemV.ArgumentWord at hword
      cases hreg : Silmaril.X86.sysv64.intArgRegs[base]? with
      | none =>
        have : Silmaril.X86.sysv64.intArgRegs.length ≤ base := List.getElem?_eq_none_iff.mp hreg
        have h6 : Silmaril.X86.sysv64.intArgRegs.length = 6 := rfl
        omega
      | some reg =>
        rw [hreg] at hword
        simp only [Option.getD_some, hword]
        exact henc
    | succ i =>
      obtain ⟨w, h1, h2⟩ := argsAt_regs tail (base + 1) (fun k hk' => hk k (by simp [hk'])) hrest i
        (by simp only [List.length_cons] at hi; omega) (by omega)
      refine ⟨w, by rw [show base + (i + 1) = base + 1 + i by omega]; exact h1, ?_⟩
      simpa [Silmaril.Project.Shapes.C.argValues] using h2

theorem paramDefs_some {params : List (Sym × Ctype)} {args : List Int} {q : StateExpr.Key}
    {d : IntExpr.Term} (h : Silmaril.Project.Shapes.C.CFn.paramDefs params args q = some d) :
    ∃ (i : Nat) (pr : Sym × Ctype) (n : Int), params[i]? = some pr ∧ args[i]? = some n ∧
      pr.1.key = q ∧ d = .lit n := by
  unfold Silmaril.Project.Shapes.C.CFn.paramDefs at h
  obtain ⟨⟨pr, n⟩, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  have hq := List.find?_some hfind
  simp only [beq_iff_eq] at hq
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfind)
  simp only [List.getElem_zip, Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  simp only [List.length_zip] at hi
  refine ⟨i, pr, n, ?_, ?_, hq, rfl⟩
  · rw [List.getElem?_eq_getElem (by omega), h1]
  · rw [List.getElem?_eq_getElem (by omega), h2]

theorem paramDefs_isSome {params : List (Sym × Ctype)} {args : List Int} {q : StateExpr.Key}
    (hq : q ∈ params.map (·.1.key)) (hlen : args.length = params.length) :
    (Silmaril.Project.Shapes.C.CFn.paramDefs params args q).isSome = true := by
  unfold Silmaril.Project.Shapes.C.CFn.paramDefs
  rw [Option.isSome_map]
  obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpr
  refine List.find?_isSome.mpr ⟨(params[i], args[i]'(by omega)), ?_, by simp⟩
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

theorem argValues_length :
    ∀ {kinds : List Silmaril.X86.SystemV.CApi.Scalar} (args : Silmaril.X86.SystemV.CApi.Arguments kinds),
      (Silmaril.Project.Shapes.C.argValues args).length = kinds.length
  | _, .nil => rfl
  | _, .cons _ tail => by simp [Silmaril.Project.Shapes.C.argValues, argValues_length tail]

/-- The spills match the parameters: one per parameter, in the System V register order, each
into the slot of its parameter's object. Decided by the kernel. -/
def spillSlots (params : List (Sym × Ctype)) (objs : List Slot)
    (sp : List (Reg × BitVec 32 × Nat)) : Bool :=
  sp.length == params.length && decide (sp.length ≤ 6) &&
    (List.range sp.length).all fun i =>
      match sp[i]?, params[i]? with
      | some (r, _, n), some pr =>
          decide (r = Silmaril.X86.sysv64.intArgRegs[i]?.getD .rax) &&
            objs.all fun o => decide (o.sym.key ≠ pr.1.key ∨ (o.off = -((n : Int) + 16) ∧ o.size = 4))
      | _, _ => false

theorem spillSlots_sound {params : List (Sym × Ctype)} {objs : List Slot}
    {sp : List (Reg × BitVec 32 × Nat)} (h : spillSlots params objs sp = true) :
    sp.length = params.length ∧ sp.length ≤ 6 ∧ ∀ i, i < sp.length → ∃ r d n pr,
      sp[i]? = some (r, d, n) ∧ params[i]? = some pr ∧
      r = Silmaril.X86.sysv64.intArgRegs[i]?.getD .rax ∧
      ∀ o ∈ objs, o.sym.key = pr.1.key → o.off = -((n : Int) + 16) ∧ o.size = 4 := by
  simp only [spillSlots, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hlen, h6⟩, hall⟩ := h
  refine ⟨hlen, h6, fun i hi => ?_⟩
  have hi' := hall i hi
  split at hi'
  · rename_i r d n pr hsp hpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hi'
    obtain ⟨hr, hobjs⟩ := hi'
    refine ⟨r, d, n, pr, hsp, hpr, hr, fun o ho hk => ?_⟩
    have := hobjs o ho
    rcases this with h | h
    · exact absurd hk h
    · exact h
  · cases hi'

/-! ## The entry segment -/

/-- **The entry segment of an `-O0` leaf is simulated.** From the System V call (point 0) to the
first statement point: the Core enters the body `sseq(blk, save)`, creates the block's `int`
locals `xs` and enters the first statement; the machine runs the prologue and spills the
`int` arguments into their parameters' slots (`sp`). At the first point the parameters are
defined with the argument values and in their slots; the new locals have no definition. -/
theorem FnData.segment_entry (F : FnData) {p0 q : Point} {a0 : List Annot} {pat0 : Pattern Sym}
    {blk save : EE} {xs : List Sym} {a1 : List Annot} {pat1 : Pattern Sym} {rest1 : EE}
    {objs : List Slot} {sp : List (Reg × BitVec 32 × Nat)}
    (hp : F.points[0]? = some p0) (hk0 : p0.kind = .entry) (hf0 : p0.frag = F.body)
    (hq : F.points[1]? = some q) (hqk : q.kind = .slots (some (pat1, rest1, true)) objs)
    (hbody : F.body = .mk a0 (.sseq pat0 blk save))
    (hcr : afterCreates xs blk = some (.mk a1 (.sseq pat1 q.frag rest1)))
    (hkeys : objs.map (·.sym.key) = F.params.map (·.1.key) ++ xs.map (·.key))
    (hnodup : (F.params.map (·.1.key) ++ xs.map (·.key)).Nodup)
    (hroom : 4 * xs.length + 8 ≤ 4096)
    (hsig : ∀ k ∈ F.sig.arguments, k = .int32)
    (hdefs : ∀ o ∈ objs, o.defined = true → o.sym.key ∈ F.params.map (·.1.key))
    (hslots : spillSlots F.params objs sp = true)
    (hsp : spillsAt F.code 4 sp = true)
    (hdisp : ∀ x ∈ sp, x.2.1.signExtend 64 = -(BitVec.ofNat 64 x.2.2) ∧ 4 ≤ x.2.2 ∧
      x.2.2 + 8 ≤ F.frame)
    (hpw : sp.Pairwise (fun x y => x.2.2 + 4 ≤ y.2.2 ∨ y.2.2 + 4 ≤ x.2.2))
    (hsp0 : sp ≠ []) (hqoff : q.off = 4 + 3 * sp.length)
    (hmid : ∀ r ∈ F.points, r.off ≠ 1 ∧ r.off ≠ 4)
    (hmid' : ∀ i < sp.length, 0 < i → ∀ r ∈ F.points, r.off ≠ 4 + 3 * i)
    (hpush : Silmaril.X86.Open.decode ((F.code.drop 0).take 1) = some (.base (.push .rbp), 1))
    (hmov : Silmaril.X86.Open.decode ((F.code.drop 1).take 3) =
      some (.base (.mov .q (.reg .rbp) .rsp), 3))
    (hfr : 8 ≤ F.frame) (hfit : 4 + 3 * sp.length ≤ F.code.length)
    (hpts : ∀ r ∈ F.points, r.off < F.code.length) (haddr : F.addr + F.code.length < 2 ^ 64) :
    F.Segment Silmaril.X86.Open.isa 0 := by
  intro k0 x0 s x hs hx hr _
  obtain ⟨p1, hp1, env1, hctl⟩ := hs
  obtain ⟨p2, hp2, hholds⟩ := hr
  obtain ⟨p3, hp3, -⟩ := hx
  rw [hp, Option.some.injEq] at hp1 hp2 hp3
  subst hp1 hp2 hp3
  rw [hk0] at hholds
  obtain ⟨rfl, args, hme, hstack, env, hctl', hlen, ls, hlskeys, inv, hroomA⟩ := hholds
  rcases s with ⟨c, st, mem⟩
  simp only at hctl hstack hctl'
  subst hctl hstack
  rw [hf0] at hctl'
  injection hctl' with _ henv
  subst henv
  -- The Core run.
  have hroomA' : 4096 < mem.lastAddress := hroomA.room
  obtain ⟨env', mem', news, rcr, hnews, inv', al', last'⟩ := creates_run (file := F.file)
    (labels := F.labels) xs blk _ hcr env1
    (.strongBind pat0 save env1 :: .procedureReturn F.bodyLabels :: k0) mem ls
    (Silmaril.Project.Shapes.C.CFn.paramDefs F.params (Silmaril.Project.Shapes.C.argValues args)) inv (AllocRoom.alloc hroomA) (by omega)
    (by rw [hlskeys]; exact hnodup)
  have reach : SeqReach.Reaches F.file F.labels
      ⟨.effectExpr p0.frag env1, .procedureReturn F.bodyLabels :: k0, mem⟩
      ⟨.effectExpr q.frag env', .strongBind pat1 rest1 env' ::
        .strongBind pat0 save env1 :: .procedureReturn F.bodyLabels :: k0, mem'⟩ := by
    rw [hf0, hbody]
    exact (ReturnConst.sequence_reaches F.file F.labels a0 pat0 blk save env1 _ mem).trans
      (rcr.trans (ReturnConst.sequence_reaches F.file F.labels a1 pat1 q.frag rest1 env' _ mem'))
  -- The machine run.
  have hsplen0 : 0 < sp.length := List.length_pos_of_ne_nil hsp0
  have hlen4 : 4 ≤ F.code.length := by omega
  obtain ⟨m1, m2, hs1, hs2, hrip1, hrsp1, hrip2, hf2, hregs2⟩ :=
    prologue hme haddr hfr hlen4 hpush hmov
  obtain ⟨m', hop, hrip', hregs', hf', hholds', -⟩ :=
    spills_run F k0 x haddr hpts sp 4 m2 hsp0 hf2 hrip2 hsp hdisp hpw
      (fun i h0 hi => hmid' i hi h0) hfit
  have hnc1 : ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x m1 :=
    F.notCut (o := 1) hrip1 (fun r hr => (hmid r hr).1) (by omega) hpts haddr hrsp1
  have hnc2 : ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x m2 :=
    F.notCut (o := 4) hrip2 (fun r hr => (hmid r hr).2) (by omega) hpts haddr hf2.rsp
  have hrip'' : m'.core.rip = BitVec.ofNat 64 (F.addr + q.off) := by
    rw [hrip', hqoff, Nat.add_assoc]
  obtain ⟨hsplen, hsp6, hspi⟩ := spillSlots_sound hslots
  have hrsp0 : F.frame ≤ (x.core.read .rsp).toNat := hf2.rsp0
  refine ⟨_, m', ⟨transGen_of_reaches reach (state_ne_of_length (by simp)),
      Or.inl ⟨1, q, hq, env', rfl⟩⟩, ⟨.more hs1 hnc1 (.more hs2 hnc2 hop),
      Or.inl ⟨1, q, hq, hrip''⟩⟩, Or.inl ⟨1, ⟨q, hq, env', rfl⟩, ⟨q, hq, hrip''⟩, q, hq, ?_⟩⟩
  rw [hqk]
  refine ⟨hf', q.frag, env', env', [.strongBind pat0 save env1], rfl, by simp [contFrames], ?_,
    fun _ _ _ _ => rfl, ls ++ news, Silmaril.Project.Shapes.C.CFn.paramDefs F.params (Silmaril.Project.Shapes.C.argValues args), inv',
    al'.budget (by rw [last']; omega), ?_, fun o ho => ⟨fun hd => ?_, fun d hd => ?_⟩⟩
  · intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    simp [FnData.Boundary]
  · rw [List.map_append, hlskeys, hnews, hkeys]
  · exact paramDefs_isSome (hdefs o ho hd) hlen
  · obtain ⟨i, pr, n, hpr, hn, hkey, rfl⟩ := paramDefs_some hd
    have hi : i < sp.length := by
      rw [hsplen]; exact (List.getElem?_eq_some_iff.mp hpr).1
    obtain ⟨r, dd, nn, pr', hspr, hpr', hr, hoff⟩ := hspi i hi
    rw [hpr, Option.some.injEq] at hpr'
    subst hpr'
    obtain ⟨hoffo, hsizeo⟩ := hoff o ho hkey.symm
    have hmem : (r, dd, nn) ∈ sp := List.mem_of_getElem? hspr
    obtain ⟨-, -, hnf⟩ := hdisp (r, dd, nn) hmem
    dsimp only at hnf
    have hslot := hholds' (r, dd, nn) hmem
    dsimp only at hslot
    have hkinds : i < F.sig.arguments.length := by
      rw [← argValues_length args]; exact (List.getElem?_eq_some_iff.mp hn).1
    obtain ⟨w, hw, hwv⟩ := argsAt_regs args 0 hsig hme.args i hkinds (by omega)
    rw [hn, Option.some.injEq] at hwv
    subst hwv
    rw [Nat.zero_add] at hw
    obtain ⟨hne1, hne2⟩ := intArgRegs_ne i
    rw [← hr] at hw hne1 hne2
    rw [hregs2 r hne1 hne2, hw] at hslot
    show HoldsLE m'.memory (slotAddr x o) o.size _
    rw [slotAddr_eq hoffo (by omega), hsizeo]
    refine holdsLE_of_low ?_ hslot
    simp only [IntExpr.Term.val]
    rw [ofInt_setWidth32, BitVec.ofInt_toInt]
    apply BitVec.eq_of_toNat_eq
    simp

end Silmaril.Project.CompilesTo

end
