module

public import Silmaril.Compiler.Core.Verified.PrintfStd.Defs
public import Silmaril.Compiler.Core.Verified.PrintfDecimal.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # The std.core printf call with variadic arguments

Reading the null-terminated format and forwarding the variadic argument list
are independent of the conversions. The formatting premise describes the
canonical builtin and records its preservation of live objects and allocation
state. No source program is executed by a compiler definition here.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfVariadic

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open PrintfStd StrMem
open SeqReach (pure_symbol)

variable {file : Program} {labels : Labels}

/-- Existing integer slots survive a call that preserves all older objects. The
bounds relate the slot to the preserved region; `Slot` alone does not carry them. -/
theorem slot_keeps {m m' : Mem.Concrete.State} {id addr n : Int}
    (slot : Locals.Slot m id addr n) (below : id < m.nextId) (above : m.lastAddress ≤ addr)
    (keep : Keeps m m') : Locals.Slot m' id addr n := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [keep.dead id below]
    exact slot.live.alive
  · obtain ⟨a, ha, hbase, hsize, hatomic, hro⟩ := slot.live.found
    exact ⟨a, by rw [keep.alloc id below]; exact ha, hbase, hsize, hatomic, hro⟩
  · intro i hi
    rw [keep.pbytes _ (by omega)]
    exact slot.plain i hi
  · have fetch : ∀ (size : Nat) (addr₁ : Int), m.lastAddress ≤ addr₁ →
        Mem.Concrete.fetchBytes size addr₁ m'.bytes = Mem.Concrete.fetchBytes size addr₁ m.bytes := by
      intro size
      induction size with
      | zero => intros; rfl
      | succ size ih =>
        intro addr₁ ha
        simp only [Mem.Concrete.fetchBytes, Mem.Concrete.readByte]
        rw [keep.bytes addr₁ ha, ih (addr₁ + 1) (by omega)]
    rw [fetch 4 addr above]
    exact slot.bytes

/-- Forward arbitrary typed variadic pointers through `printf_proxy`, after
loading the format argument object and scanning the format string. -/
theorem proxy_format_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s) {cs : List Int}
    (hcs : StringFormat cs) {m : Mem.Concrete.State} {fid faddr sid saddr : Int}
    (hp : PtrObj m fid faddr sid saddr) (hstr : StrObj m sid saddr cs) (outer : Env)
    (k : List Frame) (bt : BaseType) (args : PrintArgs) (text : String)
    (format : ∀ m₁, Keeps m m₁ → SameAlloc m m₁ →
      ∃ finish, printFormat ⟨file.tagDefs, m₁.enumTypes⟩ (cs.dropLast.length + 1)
        (cs.dropLast.map fun c => Char.ofNat c.toNat) args m₁ = .ok (text, finish) ∧
        finish.stdout = m₁.stdout ∧ Keeps m₁ finish ∧ SameAlloc m₁ finish) :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.procedure outer) [.loaded (.specified (.pointer (.function proxy))),
        .object (.pointer (.allocated fid faddr)), .list bt (args.map fun a => .tuple [.ctype a.1, .object (.pointer a.2)])], k, m⟩
      ⟨.value (.loaded (.specified (.integer text.length))), .annotations zs :: k, m'⟩ ∧
      m'.stdout = m.stdout ++ text ∧ Keeps m m' ∧ SameAlloc m m' := by
  obtain ⟨rfl, hfun, -, -, ⟨d, hl, hb⟩, -, -, -, -⟩ := stdOf_spec hs
  unfold proxyBody at hb
  split at hb
  case h_2 => cases hb
  rename_i dx loc mk ty tp btp as bas body
  have ord : libraryCall file s.proxy = none := by simp [libraryCall, hfun]
  let PF : Val := .object (.pointer (.allocated fid faddr))
  let L0 : Val := .list bt (args.map fun a => .tuple [.ctype a.1, .object (.pointer a.2)])
  have resolved : procedureBody file s.proxy [PF, L0] = .ok (body, [(tp, PF), (as, L0)]) := by
    rw [CallReach.stdlib_procedure_body hl rfl]; rfl
  unfold proxyCheck at hb
  obtain ⟨⟨fp_, e1, r1⟩, q1, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨tp', q2, hb⟩ := bind_some hb
  obtain ⟨⟨fp_', fp, r2⟩, q3, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨xs, e2, r3⟩, q4, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨lfs, fp'⟩, q5, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨ret, e3, r4⟩, q6, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨⟨xs', as'⟩, q7, hb⟩ := bind_some hb; try dsimp only at hb
  obtain ⟨ret', q8, hb⟩ := bind_some hb
  split at hb
  case isFalse => cases hb
  rename_i hc
  cases hb
  obtain ⟨hd, k1, k2, k3, k4, k5, k6⟩ := hc
  obtain ⟨B0, P0, b0, rfl⟩ := sseqOf_inv q1
  obtain ⟨A1, l1, U1, a2, u2, t, a3, u3, rfl, ht⟩ := loadOf_inv q2
  obtain ⟨B4, a5, u5, sa, pa, bfp, ua, up, no, rfl⟩ := specCase_inv q3
  obtain ⟨B5, P5, b5, rfl⟩ := sseqOf_inv q4
  obtain ⟨A6, U6, a7, u7, rfl⟩ := procOne_inv q5
  obtain ⟨B7, P7, b7, rfl⟩ := sseqOf_inv q6
  obtain ⟨A8, U8, a9, u9, a10, u10, rfl⟩ := procPrintf_inv q7
  obtain ⟨B11, a12, u12, rfl⟩ := pureSym_inv q8
  have nd := distinct_nodup hd
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    or_false, not_or] at nd
  obtain ⟨⟨n_ta, -, -, -, -⟩, ⟨n_afp_, n_afp, n_axs, -⟩, -⟩ := nd
  let E : Env := extendEnv [(tp, PF), (as, L0)] outer
  let m2 : Mem.Concrete.State := {SeqReach.focusMemory A1 m with lastUsed := some fid}
  let mc := SeqReach.focusMemory A6 (SeqReach.focusMemory B4 m2)
  have kc : Keeps m mc := ((keeps_focus A1 m).lastUsed _).trans
    ((keeps_focus B4 m2).trans (keeps_focus A6 _))
  have c1 := (CallReach.dispatch_reaches (labels := labels) false ord resolved outer k m).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    ((loadPtr_reaches A1 a2 a3 l1 U1 u2 u3 ht hp
      (by rw [ReturnLit.lookup_key k1]; simp [extendEnv, PF]) _).trans
    ((v_strongBind _ rfl _ _).trans
    ((SeqReach.specified_case_reaches B4 sa ua (.mk pa (.base (some fp, bfp))) up
      (pure_symbol a5 fp_' _ _ (by rw [ReturnLit.lookup_key k2]; exact lk_same rfl _ _)) rfl _ m2).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    (proc_apply A6 U6 s.lfs (.cons (pure_symbol a7 fp' _ _ (lk_same k3 _ _)) .nil) _ _))))))
  obtain ⟨m4, zs, r4, kp4, o4, s4⟩ := bridge c1 (lfs_string_reaches hs hcs s.lfs rfl _ _ _ (hstr.keeps kc))
  have hasl : ∀ v w : Val, (extendEnv [(xs, v)] (extendEnv [(fp, w)]
      (extendEnv [(fp_, .loaded (.specified (.pointer (.allocated sid saddr))))] E))).lookup as' = some L0 := by
    intro v w
    rw [ReturnLit.lookup_key k5, lk_other n_axs, lk_other n_afp, lk_other n_afp_]
    simp [E, extendEnv, Map.lookup_insert_of_key_ne _ _ (Ne.symm n_ta), L0]
  let m5 := SeqReach.focusMemory A8 m4
  have km5 : Keeps m m5 := (kc.trans kp4).trans (keeps_focus A8 m4)
  have sm5 : SameAlloc m m5 := by
    obtain ⟨t1, t2, t3⟩ := s4
    simp [SameAlloc, m5, t1, t2, t3, m2]
  obtain ⟨finish, fmt, fout, fkeep, falloc⟩ := format m5 km5 sm5
  have r5 := r4.trans ((v_strongBind zs rfl _ _).trans
    ((ExitCall.lift file labels (ExitCall.ra_sseq file labels _ _ _ _) (ExitCall.plain_effectExpr _ _)).trans
    ((printf_enter A8 U8 _ _ _ _ m4).trans
    ((pure_symbol a9 xs' _ _ (lk_same k4 _ _) _ _).trans
    ((CallReach.arguments_reaches (.cons (pure_symbol a10 as' _ L0 (hasl _ _)) .nil)
      (.builtin "printf") [] _ _ _).trans
    ((PrintfFormat.builtin_of_format (file := file) (labels := labels)
      cs.dropLast (fun c hc => by have := hcs.2 c hc; omega) args s.revTy bt _ m5 finish text fmt).trans
    ((SeqReach.strong_bind_reaches rfl _ _).trans
    ((SeqReach.effect_pure_reaches B11 (pure_symbol a12 ret' _ _ (lk_same k6 _ _)) _ _).trans
    ((v_merge _ _ _ _ _).trans (v_return _ _ _ k _))))))))))
  obtain ⟨t1, t2, t3⟩ := sm5
  obtain ⟨f1, f2, f3⟩ := falloc
  refine ⟨_, _, r5, by simp [fout, m5, o4, m2], ?_,
    by simp [SameAlloc, f1, f2, f3, t1, t2, t3]⟩
  exact km5.trans (fkeep.trans ((Keeps.refl finish).stdout _ |>.trans (keeps_focus B11 _)))

/-- A single signed-decimal conversion is valid all the way through the real
std.core proxy and string reader, over arbitrary caller frames and stdout.
The argument value is loaded from its live Core object. -/
theorem proxy_decimal_reaches {s : Std} {proxy : Sym} (hs : stdOf file proxy = some s)
    {cs : List Int} (hcs : StringFormat cs) {m : Mem.Concrete.State}
    {fid faddr sid saddr id addr n : Int}
    (hp : PtrObj m fid faddr sid saddr) (hstr : StrObj m sid saddr cs)
    (slot : Locals.Slot m id addr n) (below : id < m.nextId) (above : m.lastAddress ≤ addr)
    (range : Mem.Concrete.IntRange n) (pre suffix : List Char)
    (hpct : ∀ c ∈ pre, c ≠ '%') (hsct : ∀ c ∈ suffix, c ≠ '%')
    (shape : cs.dropLast.map (fun c => Char.ofNat c.toNat) = pre ++ '%' :: 'd' :: suffix)
    (outer : Env) (k : List Frame) (bt : BaseType) {iann : List Annot} :
    ∃ m' zs, ReturnConst.Reaches file labels
      ⟨.apply (.procedure outer) [.loaded (.specified (.pointer (.function proxy))),
        .object (.pointer (.allocated fid faddr)),
        .list bt [.tuple [.ctype (Mem.Concrete.intType iann),
          .object (.pointer (.allocated id addr))]]], k, m⟩
      ⟨.value (.loaded (.specified (.integer
        (String.ofList pre ++ (toString n ++ String.ofList suffix)).length))),
        .annotations zs :: k, m'⟩ ∧
      m'.stdout = m.stdout ++ (String.ofList pre ++ (toString n ++ String.ofList suffix)) ∧
      Keeps m m' ∧ SameAlloc m m' := by
  apply proxy_format_reaches hs hcs hp hstr outer k bt
    [(Mem.Concrete.intType iann, .allocated id addr)]
    (String.ofList pre ++ (toString n ++ String.ofList suffix))
  intro m₁ keep _
  have slot₁ := slot_keeps slot below above keep
  have load := Mem.Concrete.load_int ⟨file.tagDefs, m₁.enumTypes⟩ iann
    slot₁.live slot₁.plain range slot₁.bytes
  refine ⟨{m₁ with lastUsed := some id}, ?_, rfl, (Keeps.refl m₁).lastUsed _, ⟨rfl, rfl, rfl⟩⟩
  have len : cs.dropLast.length = (pre ++ '%' :: 'd' :: suffix).length := by
    simpa only [List.length_map] using congrArg List.length shape
  rw [len, shape]
  exact PrintfFormat.printFormat_d _ pre suffix hpct hsct m₁ _ iann _ n load

end Silmaril.Compile.Core.Verified.PrintfVariadic
