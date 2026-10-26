module

public import Silmaril.Apps.Sha256sum.Binary.Startup.Cuts
public meta import Lean

/-! # Shared tools for `cmain`'s segment from `AtOptParse` to `AtDigestEntry`

* `cm_ld`/`cm_go`: `sv_go` with the loads of a stored span resolved by address (same span by
  syntactic equality, else disjoint), so that no failed attempt is tried;
* one `List.lookup` equation per listed offset of `Main` and `Call` (so that `simp` never
  unfolds a listing);
* facts of the launch memory: the `.data` words `cmain` reads (`seg3`), the
  `POSIXLY_CORRECT=` pattern (`seg2`), string bytes through a footprint.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext

/-- A narrower load of a stored span reads the low bytes of the stored word. -/
theorem loadN_st_narrow {m m' : Memory} {a : Word} {k j : Nat} {v : Word}
    (h : storeN m a k v = some m') (hj : j ≤ k) (hp : m.Permitted .read a.toNat j) :
    loadN m' a j = some (BitVec.ofNat 64 (leValue ((leBytes v k).take j))) := by
  have frame := storeN_writesOnly h
  have hlen : ((leBytes v k).take j).length = j := by simp; omega
  have hp' : m'.Permitted .read a.toNat j :=
    ((Memory.writesOnly_iff_writesWithin _ _ _ _).mp frame).permitted_iff _ _ _ |>.mpr hp
  have read := Memory.readWith_eq m' .read a.toNat ((leBytes v k).take j) (by rw [hlen]; exact hp')
    (fun i hi => by
      rw [List.getElem_take]
      exact Memory.writeBytes_get h i (by simp at hi ⊢; omega))
  rw [hlen] at read
  simp [loadN, Memory.readBytes, read]

/-- `mov 0x8(%rsp),%ecx` after `mov %rdx,0x8(%rsp)` with `rdx = 0`. -/
theorem loadN_st_zero84 {m m' : Memory} {a : Word} (h : storeN m a 8 0#64 = some m')
    (hp : m.Permitted .read a.toNat 4) : loadN m' a 4 = some 0#64 := by
  rw [loadN_st_narrow h (by decide) hp]
  decide

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

namespace Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

open Lean Elab Tactic Meta

/-- Resolve one load of a produced memory in the goal: through its store, as the same span
(when the addresses agree syntactically) or a disjoint one. -/
meta def ldOnce : TacticM Bool := withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let mut prods : Array (Lean.Expr × Lean.Expr × Lean.Expr × Bool × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    if lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 then
      prods := prods.push (rhs.getArg! 1, d.toExpr, lhs.getArg! 1, false, lhs.getArg! 1)
    else if lhs.isAppOfArity ``Silmaril.X86.Ext.storeN 4 then
      prods := prods.push (rhs.getArg! 1, d.toExpr, lhs.getArg! 1, true, lhs.getArg! 2)
  let isProduced := fun (m : Lean.Expr) => prods.any fun p => p.1 == m
  let some ld := Silmaril.Apps.Sha256sum.Binary.Startup.findLoad g isProduced | return false
  let some (_, h, addr, isSt, kst) := prods.find? fun p => p.1 == ld.getArg! 0 | return false
  let a := ld.getArg! 1
  let same ← if isSt then withReducible (isDefEq addr a) else
    if addr.isAppOfArity ``BitVec.toNat 2 then withReducible (isDefEq (addr.getArg! 1) a)
    else pure false
  let hs ← Term.exprToSyntax h
  let lds ← Term.exprToSyntax ld
  if isSt then
    if same && !(kst == ld.getArg! 2) then
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.Cmain.loadN_st_zero84 $hs (by sv_perm); simp only [e] <;> try clear e)))
    else if same then
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_same $hs (by sv_perm); simp only [e] <;> try clear e)))
    else
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_st_disj $hs (by sv_disj); simp only [e] <;> try clear e)))
  else
    if same then
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_word $hs (by sv_perm); simp only [e] <;> try clear e)))
    else
      evalTactic (← `(tactic| (have e : $lds = _ := Silmaril.Apps.Sha256sum.Binary.Startup.loadN_wb_disj $hs (by sv_disj); simp only [e] <;> try clear e)))
  return true

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

open Lean Elab Tactic in
/-- `cm_ld`: resolve the loads of produced memories in the goal, then the loads with a
context fact. -/
elab "cm_ld" : tactic => do
  for _ in [0:100] do
    if (← getGoals).isEmpty then break
    unless ← Silmaril.Apps.Sha256sum.Binary.Startup.Cmain.ldOnce do break

/-- `cm_split`: split the conjunctions and the stores' `∀ after` of the VC, then close the
leaves `sv_close` knows (code loaded, permissions, `Ro`). -/
macro "cm_split" : tactic => `(tactic| ((repeat' (first | (refine ⟨?_, ?_⟩) | (refine fun (_ : Silmaril.Process.Memory) _ => ?_))) <;> sv_close))

/-- `cm_mem`: `sv_mem`, with its footprint side goals closed by `sv_disj`. -/
macro "cm_mem" : tactic => `(tactic| (sv_mem <;> (try (intro _ _; sv_disj))))

macro "cm_go " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (sv [$ls,*]; cm_split; all_goals (try cm_ld); iterate 40 (all_goals (try (sv [$ls,*]; cm_split; all_goals (try cm_ld))))))


namespace Silmaril.Apps.Sha256sum.Binary.Startup

open Silmaril.X86.Ext (Mem)
open Silmaril.X86.Lift (ix)
open Silmaril.X86

/-! ## The listing lookups, one equation per offset (so that `simp` never unfolds a listing) -/

theorem main_lk_0 : Main.listing.lookup 0 = some (.base (.push (.r15)), 2) := rfl
theorem main_lk_2 : Main.listing.lookup 2 = some (.base (.push (.r14)), 2) := rfl
theorem main_lk_4 : Main.listing.lookup 4 = some (.base (.push (.r13)), 2) := rfl
theorem main_lk_6 : Main.listing.lookup 6 = some (.base (.push (.r12)), 2) := rfl
theorem main_lk_8 : Main.listing.lookup 8 = some (.base (.push (.rbp)), 1) := rfl
theorem main_lk_9 : Main.listing.lookup 9 = some (.base (.push (.rbx)), 1) := rfl
theorem main_lk_10 : Main.listing.lookup 10 = some (.base (.aluI (.q) (.sub) (.reg (.rsp)) 0x000000b8#32), 7) := rfl
theorem main_lk_17 : Main.listing.lookup 17 = some (.base (.load (.q) (.rsi) (Mem.ofReg .rdi none 0x00000000#32)), 3) := rfl
theorem main_lk_20 : Main.listing.lookup 20 = some (.base (.test (.d) (.reg (.rsi)) (.rsi)), 2) := rfl
theorem main_lk_22 : Main.listing.lookup 22 = some (.base (.jcc (.e) 0x000001bf#32), 6) := rfl
theorem main_lk_28 : Main.listing.lookup 28 = some (.base (.mov (.q) (.reg (.r11)) (.rdi)), 3) := rfl
theorem main_lk_31 : Main.listing.lookup 31 = some (.base (.load (.q) (.rdi) (Mem.ofReg .rdi none 0x00000008#32)), 4) := rfl
theorem main_lk_35 : Main.listing.lookup 35 = some (.base (.test (.q) (.reg (.rdi)) (.rdi)), 3) := rfl
theorem main_lk_38 : Main.listing.lookup 38 = some (.base (.jcc (.e) 0x000001af#32), 6) := rfl
theorem main_lk_44 : Main.listing.lookup 44 = some (.base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rdi none 0x00000000#32))), 3) := rfl
theorem main_lk_47 : Main.listing.lookup 47 = some (.base (.mov (.d) (.reg (.r14)) (.rsi)), 3) := rfl
theorem main_lk_50 : Main.listing.lookup 50 = some (.base (.test8 (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_52 : Main.listing.lookup 52 = some (.base (.jcc8 (.e) 0x5d#8), 2) := rfl
theorem main_lk_54 : Main.listing.lookup 54 = some (.base (.mov (.q) (.reg (.rax)) (.rdi)), 3) := rfl
theorem main_lk_57 : Main.listing.lookup 57 = some (.base (.alu (.d) (.xor) (.reg (.rcx)) (.rcx)), 2) := rfl
theorem main_lk_59 : Main.listing.lookup 59 = some (.base (.nop 4), 5) := rfl
theorem main_lk_64 : Main.listing.lookup 64 = some (.base (.cmpI8 (.reg (.rdx)) 0x2f#8), 3) := rfl
theorem main_lk_67 : Main.listing.lookup 67 = some (.base (.jcc8 (.ne) 0x03#8), 2) := rfl
theorem main_lk_69 : Main.listing.lookup 69 = some (.base (.mov (.q) (.reg (.rcx)) (.rax)), 3) := rfl
theorem main_lk_72 : Main.listing.lookup 72 = some (.base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rax none 0x00000001#32))), 4) := rfl
theorem main_lk_76 : Main.listing.lookup 76 = some (.base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4) := rfl
theorem main_lk_80 : Main.listing.lookup 80 = some (.base (.test8 (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_82 : Main.listing.lookup 82 = some (.base (.jcc8 (.ne) 0xec#8), 2) := rfl
theorem main_lk_84 : Main.listing.lookup 84 = some (.base (.test (.q) (.reg (.rcx)) (.rcx)), 3) := rfl
theorem main_lk_87 : Main.listing.lookup 87 = some (.base (.jcc8 (.e) 0x3a#8), 2) := rfl
theorem main_lk_89 : Main.listing.lookup 89 = some (.base (.lea (.q) (.r8) (Mem.ofReg .rcx none 0x00000001#32)), 4) := rfl
theorem main_lk_93 : Main.listing.lookup 93 = some (.base (.mov (.q) (.reg (.rax)) (.r8)), 3) := rfl
theorem main_lk_96 : Main.listing.lookup 96 = some (.base (.alu (.q) (.sub) (.reg (.rax)) (.rdi)), 3) := rfl
theorem main_lk_99 : Main.listing.lookup 99 = some (.base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x06#8), 4) := rfl
theorem main_lk_103 : Main.listing.lookup 103 = some (.base (.jcc8 (.le) 0x2a#8), 2) := rfl
theorem main_lk_105 : Main.listing.lookup 105 = some (.base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2) := rfl
theorem main_lk_107 : Main.listing.lookup 107 = some (.base (.jmp8 0x19#8), 2) := rfl
theorem main_lk_112 : Main.listing.lookup 112 = some (.base (.test8 (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_114 : Main.listing.lookup 114 = some (.base (.jcc (.e) 0x00000271#32), 6) := rfl
theorem main_lk_120 : Main.listing.lookup 120 = some (.base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4) := rfl
theorem main_lk_124 : Main.listing.lookup 124 = some (.base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x07#8), 4) := rfl
theorem main_lk_128 : Main.listing.lookup 128 = some (.base (.jcc (.e) 0x00000263#32), 6) := rfl
theorem main_lk_134 : Main.listing.lookup 134 = some (.base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rcx (some (ix .rax 0x0#2)) 0xfffffffa#32))), 5) := rfl
theorem main_lk_139 : Main.listing.lookup 139 = some (.new (.aluR (.cmp) (.low (.rdx)) (.mem (Mem.ofReg .rax none 0x004060dc#32))), 6) := rfl
theorem main_lk_145 : Main.listing.lookup 145 = some (.base (.jcc8 (.e) 0xdd#8), 2) := rfl
theorem main_lk_147 : Main.listing.lookup 147 = some (.base (.mov (.q) (.reg (.r8)) (.rdi)), 3) := rfl
theorem main_lk_150 : Main.listing.lookup 150 = some (.base (.movsxd (.rsi) (.reg (.rsi))), 3) := rfl
theorem main_lk_153 : Main.listing.lookup 153 = some (.base (.lea (.q) (.r15) (Mem.ofReg .r11 none 0x00000008#32)), 4) := rfl
theorem main_lk_157 : Main.listing.lookup 157 = some (.base (.alu (.d) (.xor) (.reg (.r12)) (.r12)), 3) := rfl
theorem main_lk_160 : Main.listing.lookup 160 = some (.base (.mov (.q) (.mem (Mem.ofRip 0x0000ec89#32)) (.r8)), 7) := rfl
theorem main_lk_167 : Main.listing.lookup 167 = some (.base (.lea (.q) (.rbx) (Mem.ofIndex (some (ix .rsi 0x3#2)) 0x00000008#32)), 8) := rfl
theorem main_lk_175 : Main.listing.lookup 175 = some (.base (.mov (.q) (.mem (Mem.ofRip 0x0000ec72#32)) (.rdi)), 7) := rfl
theorem main_lk_182 : Main.listing.lookup 182 = some (.base (.lea (.q) (.rsi) (Mem.ofReg .r15 (some (ix .rbx 0x0#2)) 0x00000000#32)), 4) := rfl
theorem main_lk_186 : Main.listing.lookup 186 = some (.base (.load (.q) (.rcx) (Mem.ofReg .rsi none 0x00000000#32)), 3) := rfl
theorem main_lk_189 : Main.listing.lookup 189 = some (.base (.test (.q) (.reg (.rcx)) (.rcx)), 3) := rfl
theorem main_lk_192 : Main.listing.lookup 192 = some (.base (.jcc8 (.e) 0x45#8), 2) := rfl
theorem main_lk_194 : Main.listing.lookup 194 = some (.base (.nop 5), 6) := rfl
theorem main_lk_200 : Main.listing.lookup 200 = some (.base (.movI32 (.rdx) 0x00000050#32), 5) := rfl
theorem main_lk_205 : Main.listing.lookup 205 = some (.base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2) := rfl
theorem main_lk_207 : Main.listing.lookup 207 = some (.base (.jmp8 0x24#8), 2) := rfl
theorem main_lk_216 : Main.listing.lookup 216 = some (.base (.test8 (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_218 : Main.listing.lookup 218 = some (.base (.jcc (.e) 0x00000140#32), 6) := rfl
theorem main_lk_224 : Main.listing.lookup 224 = some (.base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4) := rfl
theorem main_lk_228 : Main.listing.lookup 228 = some (.base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x10#8), 4) := rfl
theorem main_lk_232 : Main.listing.lookup 232 = some (.base (.jcc (.e) 0x00000132#32), 6) := rfl
theorem main_lk_238 : Main.listing.lookup 238 = some (.base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rax none 0x004060e8#32))), 7) := rfl
theorem main_lk_245 : Main.listing.lookup 245 = some (.new (.alu (.cmp) (.mem (Mem.ofReg .rcx (some (ix .rax 0x0#2)) 0x00000000#32)) (.low (.rdx))), 3) := rfl
theorem main_lk_248 : Main.listing.lookup 248 = some (.base (.jcc8 (.e) 0xde#8), 2) := rfl
theorem main_lk_250 : Main.listing.lookup 250 = some (.base (.load (.q) (.rcx) (Mem.ofReg .rsi none 0x00000008#32)), 4) := rfl
theorem main_lk_254 : Main.listing.lookup 254 = some (.base (.aluI8 (.q) (.add) (.reg (.rsi)) 0x08#8), 4) := rfl
theorem main_lk_258 : Main.listing.lookup 258 = some (.base (.test (.q) (.reg (.rcx)) (.rcx)), 3) := rfl
theorem main_lk_261 : Main.listing.lookup 261 = some (.base (.jcc8 (.ne) 0xc1#8), 2) := rfl
theorem main_lk_263 : Main.listing.lookup 263 = some (.base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2) := rfl
theorem main_lk_265 : Main.listing.lookup 265 = some (.base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000008#32)) (.r15)), 5) := rfl
theorem main_lk_270 : Main.listing.lookup 270 = some (.base (.movI32 (.r13) 0x00000001#32), 6) := rfl
theorem main_lk_276 : Main.listing.lookup 276 = some (.base (.mov (.q) (.reg (.r15)) (.r11)), 3) := rfl
theorem main_lk_279 : Main.listing.lookup 279 = some (.base (.mov (.d) (.reg (.r11)) (.rax)), 3) := rfl
theorem main_lk_282 : Main.listing.lookup 282 = some (.base (.mov (.d) (.reg (.rcx)) (.r13)), 3) := rfl
theorem main_lk_285 : Main.listing.lookup 285 = some (.base (.alu (.d) (.cmp) (.reg (.r14)) (.r13)), 3) := rfl
theorem main_lk_288 : Main.listing.lookup 288 = some (.base (.jcc8 (.le) 0x17#8), 2) := rfl
theorem main_lk_313 : Main.listing.lookup 313 = some (.base (.mov (.d) (.reg (.rax)) (.r11)), 3) := rfl
theorem main_lk_316 : Main.listing.lookup 316 = some (.base (.mov (.q) (.reg (.r11)) (.r15)), 3) := rfl
theorem main_lk_319 : Main.listing.lookup 319 = some (.base (.load (.q) (.r15) (Mem.ofReg .rsp none 0x00000008#32)), 5) := rfl
theorem main_lk_324 : Main.listing.lookup 324 = some (.base (.movsxd (.rcx) (.reg (.rcx))), 3) := rfl
theorem main_lk_327 : Main.listing.lookup 327 = some (.base (.alu (.q) (.add) (.reg (.rbx)) (.r11)), 3) := rfl
theorem main_lk_330 : Main.listing.lookup 330 = some (.base (.lea (.q) (.rdi) (Mem.ofReg .r15 (some (ix .rcx 0x3#2)) 0x00000000#32)), 4) := rfl
theorem main_lk_334 : Main.listing.lookup 334 = some (.base (.alu (.q) (.cmp) (.reg (.rdi)) (.rbx)), 3) := rfl
theorem main_lk_337 : Main.listing.lookup 337 = some (.base (.jcc8 (.ae) 0x2f#8), 2) := rfl
theorem main_lk_386 : Main.listing.lookup 386 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x00005aa7#32)) 0x00#8), 7) := rfl
theorem main_lk_393 : Main.listing.lookup 393 = some (.base (.jcc (.ne) 0x000000ad#32), 6) := rfl
theorem main_lk_399 : Main.listing.lookup 399 = some (.base (.cmpI8 (.mem (Mem.ofRip 0x00005a8e#32)) 0x0a#8), 7) := rfl
theorem main_lk_406 : Main.listing.lookup 406 = some (.base (.jcc (.e) 0x0000017c#32), 6) := rfl
theorem main_lk_544 : Main.listing.lookup 544 = some (.base (.load (.q) (.rcx) (Mem.ofReg .rsi none 0x00000008#32)), 4) := rfl
theorem main_lk_548 : Main.listing.lookup 548 = some (.base (.aluI8 (.q) (.add) (.reg (.rsi)) 0x08#8), 4) := rfl
theorem main_lk_552 : Main.listing.lookup 552 = some (.base (.movI32 (.r12) 0x00000001#32), 6) := rfl
theorem main_lk_558 : Main.listing.lookup 558 = some (.base (.test (.q) (.reg (.rcx)) (.rcx)), 3) := rfl
theorem main_lk_561 : Main.listing.lookup 561 = some (.base (.jcc (.ne) 0xfffffe91#32), 6) := rfl
theorem main_lk_567 : Main.listing.lookup 567 = some (.base (.jmp 0xfffffecb#32), 5) := rfl
theorem main_lk_745 : Main.listing.lookup 745 = some (.base (.alu (.d) (.xor) (.reg (.rax)) (.rax)), 2) := rfl
theorem main_lk_747 : Main.listing.lookup 747 = some (.base (.jmp8 0x0d#8), 2) := rfl
theorem main_lk_752 : Main.listing.lookup 752 = some (.base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4) := rfl
theorem main_lk_756 : Main.listing.lookup 756 = some (.base (.aluI8 (.q) (.cmp) (.reg (.rax)) 0x03#8), 4) := rfl
theorem main_lk_760 : Main.listing.lookup 760 = some (.base (.jcc8 (.e) 0x15#8), 2) := rfl
theorem main_lk_762 : Main.listing.lookup 762 = some (.base (.movx false (.d) (.b) (.rdx) (.mem (Mem.ofReg .rcx (some (ix .rax 0x0#2)) 0x00000001#32))), 5) := rfl
theorem main_lk_767 : Main.listing.lookup 767 = some (.new (.aluR (.cmp) (.low (.rdx)) (.mem (Mem.ofReg .rax none 0x004060e4#32))), 6) := rfl
theorem main_lk_773 : Main.listing.lookup 773 = some (.base (.jcc (.ne) 0xfffffd8b#32), 6) := rfl
theorem main_lk_779 : Main.listing.lookup 779 = some (.base (.test8 (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_781 : Main.listing.lookup 781 = some (.base (.jcc8 (.ne) 0xe1#8), 2) := rfl
theorem main_lk_783 : Main.listing.lookup 783 = some (.base (.lea (.q) (.r8) (Mem.ofReg .rcx none 0x00000004#32)), 4) := rfl
theorem main_lk_787 : Main.listing.lookup 787 = some (.base (.jmp 0xfffffd7e#32), 5) := rfl
theorem main_lk_792 : Main.listing.lookup 792 = some (.base (.load (.d) (.rdx) (Mem.ofRip 0x00005902#32)), 6) := rfl
theorem main_lk_798 : Main.listing.lookup 798 = some (.base (.test (.d) (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_800 : Main.listing.lookup 800 = some (.base (.jcc (.ns) 0x000001d1#32), 6) := rfl
theorem main_lk_806 : Main.listing.lookup 806 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x00006987#32)) 0x00#8), 7) := rfl
theorem main_lk_813 : Main.listing.lookup 813 = some (.base (.jcc8 (.e) 0x13#8), 2) := rfl
theorem main_lk_834 : Main.listing.lookup 834 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x0000697b#32)) 0x00#8), 7) := rfl
theorem main_lk_841 : Main.listing.lookup 841 = some (.base (.jcc8 (.e) 0x0d#8), 2) := rfl
theorem main_lk_856 : Main.listing.lookup 856 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x00006961#32)) 0x00#8), 7) := rfl
theorem main_lk_863 : Main.listing.lookup 863 = some (.base (.jcc (.e) 0x00000172#32), 6) := rfl
theorem main_lk_895 : Main.listing.lookup 895 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x00006932#32)) 0x00#8), 7) := rfl
theorem main_lk_902 : Main.listing.lookup 902 = some (.base (.jcc (.e) 0x000001d9#32), 6) := rfl
theorem main_lk_1239 : Main.listing.lookup 1239 = some (.base (.aluI8 (.d) (.cmp) (.mem (Mem.ofRip 0x000067de#32)) 0x00#8), 7) := rfl
theorem main_lk_1246 : Main.listing.lookup 1246 = some (.base (.jcc (.e) 0xfffffe9b#32), 6) := rfl
theorem main_lk_1381 : Main.listing.lookup 1381 = some (.base (.test (.d) (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_1383 : Main.listing.lookup 1383 = some (.base (.jcc8 (.ns) 0x08#8), 2) := rfl
theorem main_lk_1385 : Main.listing.lookup 1385 = some (.base (.alu (.d) (.xor) (.reg (.rcx)) (.rcx)), 2) := rfl
theorem main_lk_1387 : Main.listing.lookup 1387 = some (.base (.mov (.d) (.mem (Mem.ofRip 0x000056af#32)) (.rcx)), 6) := rfl
theorem main_lk_1393 : Main.listing.lookup 1393 = some (.base (.test (.d) (.reg (.rax)) (.rax)), 2) := rfl
theorem main_lk_1395 : Main.listing.lookup 1395 = some (.base (.jcc8 (.ne) 0x0d#8), 2) := rfl
theorem main_lk_1397 : Main.listing.lookup 1397 = some (.base (.movI (.q) (.mem (Mem.ofReg .r11 none 0x00000008#32)) 0x00406052#32), 8) := rfl
theorem main_lk_1405 : Main.listing.lookup 1405 = some (.base (.movI32 (.rax) 0x00000001#32), 5) := rfl
theorem main_lk_1410 : Main.listing.lookup 1410 = some (.base (.alu (.d) (.xor) (.reg (.rdx)) (.rdx)), 2) := rfl
theorem main_lk_1412 : Main.listing.lookup 1412 = some (.base (.movI (.d) (.mem (Mem.ofReg .rsp none 0x0000002c#32)) 0x00000001#32), 8) := rfl
theorem main_lk_1420 : Main.listing.lookup 1420 = some (.base (.lea (.q) (.r14) (Mem.ofReg .rsp none 0x00000090#32)), 8) := rfl
theorem main_lk_1428 : Main.listing.lookup 1428 = some (.base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000008#32)) (.rdx)), 5) := rfl
theorem main_lk_1433 : Main.listing.lookup 1433 = some (.base (.mov (.d) (.mem (Mem.ofReg .rsp none 0x00000050#32)) (.rax)), 4) := rfl
theorem main_lk_1437 : Main.listing.lookup 1437 = some (.base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000038#32)) (.r11)), 5) := rfl
theorem main_lk_1442 : Main.listing.lookup 1442 = some (.base (.load (.d) (.rcx) (Mem.ofReg .rsp none 0x00000008#32)), 4) := rfl
theorem main_lk_1446 : Main.listing.lookup 1446 = some (.base (.alu (.d) (.cmp) (.mem (Mem.ofReg .rsp none 0x00000050#32)) (.rcx)), 4) := rfl
theorem main_lk_1450 : Main.listing.lookup 1450 = some (.base (.jcc (.le) 0x00000cf7#32), 6) := rfl
theorem main_lk_1456 : Main.listing.lookup 1456 = some (.base (.load (.q) (.rax) (Mem.ofReg .rsp none 0x00000038#32)), 5) := rfl
theorem main_lk_1461 : Main.listing.lookup 1461 = some (.base (.load (.q) (.rcx) (Mem.ofReg .rsp none 0x00000008#32)), 5) := rfl
theorem main_lk_1466 : Main.listing.lookup 1466 = some (.base (.load (.d) (.rbx) (Mem.ofRip 0x00005674#32)), 6) := rfl
theorem main_lk_1472 : Main.listing.lookup 1472 = some (.base (.load (.q) (.r12) (Mem.ofReg .rax (some (ix .rcx 0x3#2)) 0x00000008#32)), 5) := rfl
theorem main_lk_1477 : Main.listing.lookup 1477 = some (.base (.test (.d) (.reg (.rbx)) (.rbx)), 2) := rfl
theorem main_lk_1479 : Main.listing.lookup 1479 = some (.base (.jcc (.e) 0x000007d2#32), 6) := rfl
theorem call_lk_0 : Call.listing.lookup 0 = some (.base (.mov (.q) (.reg (.rdx)) (.r14)), 3) := rfl
theorem call_lk_3 : Call.listing.lookup 3 = some (.base (.lea (.q) (.rsi) (Mem.ofReg .rsp none 0x00000070#32)), 5) := rfl
theorem call_lk_8 : Call.listing.lookup 8 = some (.base (.mov (.q) (.reg (.rdi)) (.r12)), 3) := rfl
theorem call_lk_11 : Call.listing.lookup 11 = some (.base (.call 0xffffec41#32), 5) := rfl

end Silmaril.Apps.Sha256sum.Binary.Startup


namespace Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext


/-- `cmp m8, r8` (the `Ext8` form `38 /r` with a memory destination). -/
theorem execNew_cmp_mem (a : Silmaril.X86.Ext.Mem) (b : Silmaril.X86.Ext8.BReg) (s : Silmaril.X86.State)
    (m : Memory) (next : Word) :
    Silmaril.X86.Ext8.execNew (.alu .cmp (.mem a) b) s m next =
      retire next ((loadN m (a.addr s next) 1).map fun v =>
        ({ s with flags := Silmaril.X86.Ext.AluOp.flagsN .cmp (v.setWidth 8) (b.read s) }, m)) := by
  simp only [Silmaril.X86.Ext8.execNew, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read]
  cases loadN m (a.addr s next) 1 <;> rfl


theorem ofNat_toNat_mod8 (x : Word) : BitVec.ofNat 64 (x.toNat % 2 ^ (8 * 8)) = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]


theorem seg3_mem : Image.seg3 ∈ Image.image.segments := by simp [Image.image]

theorem seg3_read {m : Memory} (h : Image.image.Mapped m) (off k : Nat) (hk : off + k ≤ 0xa140)
    (hpos : 0 < k) :
    loadN m (BitVec.ofNat 64 (0x409010 + off)) k =
      some (BitVec.ofNat 64 (leValue ((Image.seg3.contents.drop off).take k))) := by
  have := readWith_segment h seg3_mem Image.image_wf (acc := .read) (by decide) off k hk hpos
  unfold loadN Memory.readBytes
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact congrArg (Option.map _) this

theorem seg3_write {m : Memory} (h : Image.image.Mapped m) :
    m.Permitted .write 0x409010 4 :=
  Memory.readWith_permitted (readWith_segment h seg3_mem Image.image_wf (acc := .write) (by decide) 0 4 (by decide) (by decide))

theorem g_binary {m : Memory} (h : Image.image.Mapped m) : loadN m 0x409010#64 4 = some 0xffffffff#64 := by
  rw [show (0x409010#64 : Word) = BitVec.ofNat 64 (0x409010 + 0) from rfl, seg3_read h 0 4 (by decide) (by decide)]
  decide +kernel

theorem g_delim {m : Memory} (h : Image.image.Mapped m) : loadN m 0x409014#64 1 = some 0x0a#64 := by
  rw [show (0x409014#64 : Word) = BitVec.ofNat 64 (0x409010 + 4) from rfl, seg3_read h 4 1 (by decide) (by decide)]
  decide +kernel

theorem g_zero {m : Memory} (h : Image.image.Mapped m) (off : Nat)
    (hoff : off = 0x10 ∨ off = 0x1094 ∨ off = 0x10a4 ∨ off = 0x10a0 ∨ off = 0x109c ∨ off = 0x1098 ∨
      off = 0x14) :
    loadN m (BitVec.ofNat 64 (0x409010 + off)) 4 = some 0#64 := by
  rw [seg3_read h off 4 (by omega) (by decide)]
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel



/-- `"POSIXLY_CORRECT="` and its NUL, at `0x4060e8`. -/
def pat : List Byte := [80, 79, 83, 73, 88, 76, 89, 95, 67, 79, 82, 82, 69, 67, 84, 61, 0]

theorem seg2_pat : (Image.seg2.contents.drop 0xe8).take 17 = pat := by decide +kernel

theorem pat_read {m : Memory} (h : Image.image.Mapped m) :
    m.readWith .read 0x4060e8 17 = some pat := by
  have hr := readWith_segment h seg2_mem Image.image_wf (acc := .read) (by decide) 0xe8 17
    (by decide) (by decide)
  rw [seg2_pat] at hr
  exact hr

theorem pat_load {m : Memory} (h : Image.image.Mapped m) {j : Nat} (hj : j < 16) :
    loadN m (BitVec.ofNat 64 j + 1#64 + 0x4060e8#64) 1 = some ((pat.getD (j + 1) 0).setWidth 64) := by
  have hl : j + 1 < pat.length := by rw [show pat.length = 17 from rfl]; omega
  have hr' := Memory.readBytes_sub_range (memory := m) (address := 0x4060e8) (pat_read h)
    (offset := j + 1) (len := 1) (by omega) (by omega)
  have hq : (BitVec.ofNat 64 j + 1#64 + 0x4060e8#64).toNat = 0x4060e8 + (j + 1) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
    omega
  unfold loadN
  rw [hq, hr', List.take_one, List.head?_drop, List.getElem?_eq_getElem hl]
  simp only [Option.toList_some, Option.map_some, Option.some.injEq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [Silmaril.X86.Ext.leValue, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := (pat[j + 1]).isLt
  simp only [Nat.reducePow, Nat.mul_zero, Nat.add_zero] at this ⊢

theorem pat_ne {i : Nat} (hi : i < 16) : pat.getD i 0 ≠ 0 := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | decide | omega

theorem perm_bound {m : Memory} {acc : Silmaril.Process.Access} {a n : Nat}
    (h : m.Permitted acc a n) : a + n ≤ 2 ^ 64 := by
  unfold Memory.Permitted Memory.checkSpan at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem cstr_len {L : List Byte} {j : Nat} (hl : L.getLast? = some 0)
    (hne : ∀ i < j, L.getD i 0 ≠ 0) : j < L.length := by
  by_contra hj
  have hL : L ≠ [] := by rintro rfl; simp at hl
  have hpos : 0 < L.length := List.length_pos_iff.mpr hL
  have := hne (L.length - 1) (by omega)
  apply this
  rw [List.getLast?_eq_getElem?] at hl
  rw [List.getD_eq_getElem?_getD, hl]; rfl

/-- A byte of a string, through a footprint that misses it. -/
theorem str_load {m0 m : Memory} {W : Nat → Prop} (hww : Memory.WritesWithin m0 m W)
    {p : Word} {L : List Byte} (hs : CString m0 p L)
    (hout : ∀ i < L.length, ¬ W (p.toNat + i)) {j : Nat} (hj : j < L.length) :
    loadN m (p + BitVec.ofNat 64 j) 1 = some ((L.getD j 0).setWidth 64) := by
  have hb := perm_bound (Memory.readWith_permitted hs.2)
  have hq : (p + BitVec.ofNat 64 j).toNat = p.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [loadN_ww hww (fun i hi => by
    rw [hq]; have := hout (j + i) (by omega); simpa [Nat.add_assoc] using this)]
  have hr := Memory.readBytes_sub_range hs.2 (offset := j) (len := 1) hj (by omega)
  unfold loadN
  rw [hq, hr]
  simp only [Option.map_some, Option.some.injEq]
  rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, Silmaril.X86.Ext.leValue, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp

theorem loaded_ww {m0 m : Memory} {W : Nat → Prop} (hww : Memory.WritesWithin m0 m W)
    {b : Word} {code : List Byte} (hl : Loaded m0 b code)
    (hout : ∀ i < code.length, ¬ W (b.toNat + i)) : Loaded m b code := by
  unfold Loaded at hl ⊢
  rw [hww.fetchBytes hout]; exact hl

end Silmaril.Apps.Sha256sum.Binary.Startup.Cmain
