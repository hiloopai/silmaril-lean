module

public import Silmaril.Wasm.Jco.Real.Typed.Defs
public import Silmaril.Wasm.Jco.Styles.Wide.Thms

/-!
# Typed locals: the multi-value shim does not read the initial values of its locals

`mvShim` pops the results of the call into locals `n + 1 …` (`setsRev`) and writes local `n`
(the block pointer) before reading any of them. So its behaviour does not depend on the initial
values of its extra locals, and in particular the typed variant `mvShimT` (locals initialized to
the zeros of the field types) computes what `mvShim` (all `i32` zeros) computes.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real Silmaril.Proofs.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy)

variable (M : CoreInst)

/-- One `local.set` at the end of a block of `k + 1` locals. -/
theorem setsRev_last (pre zs post rs st : List Flat) (z r : Flat) :
    (AInstr.localSet (pre.length + zs.length)).step M
        ⟨pre ++ (zs ++ [z]) ++ post, (rs ++ [r]).reverse ++ st⟩ =
      pure ⟨pre ++ zs ++ (r :: post), rs.reverse ++ st⟩ := by
  have hlt : pre.length + zs.length < (pre ++ (zs ++ [z]) ++ post).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hst : (rs ++ [r]).reverse ++ st = r :: (rs.reverse ++ st) := by simp
  rw [hst, step_localSet M hlt, set_mid]

/-- **Popping results into consecutive locals**, whatever the locals held before. -/
theorem execX_setsRev_any : ∀ (k : Nat) (pre zs post rs st : List Flat), zs.length = k →
    rs.length = k →
    execX M (setsRev pre.length k) ⟨pre ++ zs ++ post, rs.reverse ++ st⟩ =
      pure ⟨pre ++ rs ++ post, st⟩
  | 0, pre, zs, post, rs, st, hz, hr => by
    rw [List.length_eq_zero_iff.mp hz, List.length_eq_zero_iff.mp hr]
    rfl
  | k + 1, pre, zs, post, rs, st, hz, hr => by
    obtain ⟨zs', z, rfl⟩ : ∃ zs' z, zs = zs' ++ [z] :=
      ⟨_, _, (List.dropLast_append_getLast (List.ne_nil_of_length_eq_add_one hz)).symm⟩
    obtain ⟨rs', r, rfl⟩ : ∃ rs' r, rs = rs' ++ [r] :=
      ⟨_, _, (List.dropLast_append_getLast (List.ne_nil_of_length_eq_add_one hr)).symm⟩
    have hz' : zs'.length = k := by simpa using hz
    have hr' : rs'.length = k := by simpa using hr
    have hstep := setsRev_last M pre zs' post rs' st z r
    rw [hz'] at hstep
    have hrest := execX_setsRev_any k pre zs' (r :: post) rs' st hz' hr'
    show (execX M (.base (.localSet (pre.length + k)) :: setsRev pre.length k) _) = _
    rw [execX_cons]
    show ((AInstr.localSet (pre.length + k)).step M _ >>= _) = _
    rw [hstep, RM.pure_bind, hrest]
    simp

/-- The pops of `mvShim`, from any locals. -/
theorem setsRev_head (xs zs rs : List Flat) (z₀ : Flat) (k : Nat) (hz : zs.length = k)
    (hr : rs.length = k) :
    execX M (setsRev (xs.length + 1) k) ⟨xs ++ z₀ :: zs, rs.reverse⟩ =
      pure ⟨xs ++ z₀ :: rs, []⟩ := by
  have h := execX_setsRev_any M k (xs ++ [z₀]) zs [] rs [] hz hr
  simp only [List.length_append, List.length_singleton, List.append_nil,
    List.append_assoc, List.singleton_append] at h
  exact h

/-- Setting local `n` forgets what it held. -/
theorem localSet_forget (xs rs st : List Flat) (z z' : Flat) :
    (AInstr.localSet xs.length).step M ⟨xs ++ z :: rs, st⟩ =
      (AInstr.localSet xs.length).step M ⟨xs ++ z' :: rs, st⟩ := by
  cases st with
  | nil => rfl
  | cons v st =>
    have h1 : xs.length < (xs ++ z :: rs).length := by simp
    have h2 : xs.length < (xs ++ z' :: rs).length := by simp
    rw [step_localSet M h1, step_localSet M h2]
    simp

/-- The allocation block of `mvShim` (`i32.const`, `i32.const`, `call alloc`, `local.set n`)
forgets what local `n` held. -/
theorem allocBlock_forget (alloc : String) (a b : BitVec 32) (rest : List XInstr)
    (xs rs : List Flat) (z z' : Flat) :
    execX M ([.base (.i32Const a), .base (.i32Const b), .base (.call alloc 2),
        .base (.localSet xs.length)] ++ rest) ⟨xs ++ z :: rs, []⟩ =
      execX M ([.base (.i32Const a), .base (.i32Const b), .base (.call alloc 2),
        .base (.localSet xs.length)] ++ rest) ⟨xs ++ z' :: rs, []⟩ := by
  rw [execX_append, execX_append, execX_alloc, execX_alloc, RM.bind_assoc, RM.bind_assoc]
  refine RM.bind_congr fun r => ?_
  have hset : execX M [.base (.localSet xs.length)] ⟨xs ++ z :: rs, r.reverse⟩ =
      execX M [.base (.localSet xs.length)] ⟨xs ++ z' :: rs, r.reverse⟩ := by
    rw [execX_cons, execX_cons]
    show ((AInstr.localSet xs.length).step M _ >>= _) = ((AInstr.localSet xs.length).step M _ >>= _)
    rw [localSet_forget M xs rs r.reverse z z']
  rw [hset]

/-- **`mvShim` after the call forgets the initial values of its extra locals.** -/
theorem mvShim_after_forget (md : Meta) {ts : List ValTy} {ns : List Nat} (xs rs zs : List Flat)
    (z₀ : Flat) (hz : zs.length = ts.length) (hr : rs.length = ts.length) :
    execX M (setsRev (xs.length + 1) ts.length ++
        [.base (.i32Const (BitVec.ofNat 32 (tupleSize ns))),
          .base (.i32Const (BitVec.ofNat 32 (tupleAlign ns))), .base (.call md.alloc 2),
          .base (.localSet xs.length)] ++
        storeFields xs.length (xs.length + 1) 0 ts (fieldOffs 0 ns) ns ++
        [.base (.localGet xs.length)]) ⟨xs ++ z₀ :: zs, rs.reverse⟩ =
      execX M (setsRev (xs.length + 1) ts.length ++
        [.base (.i32Const (BitVec.ofNat 32 (tupleSize ns))),
          .base (.i32Const (BitVec.ofNat 32 (tupleAlign ns))), .base (.call md.alloc 2),
          .base (.localSet xs.length)] ++
        storeFields xs.length (xs.length + 1) 0 ts (fieldOffs 0 ns) ns ++
        [.base (.localGet xs.length)])
        ⟨xs ++ List.replicate (ts.length + 1) (i32n 0), rs.reverse⟩ := by
  have hrep : xs ++ List.replicate (ts.length + 1) (i32n 0) =
      xs ++ i32n 0 :: List.replicate ts.length (i32n 0) := by
    rw [List.replicate_succ]
  have hz0 : (List.replicate ts.length (i32n 0)).length = ts.length := List.length_replicate ..
  simp only [List.append_assoc]
  rw [execX_append, execX_append, hrep, setsRev_head M xs zs rs z₀ _ hz hr,
    setsRev_head M xs _ rs (i32n 0) _ hz0 hr, RM.pure_bind, RM.pure_bind]
  exact allocBlock_forget M md.alloc _ _ _ xs rs z₀ (i32n 0)

/-- The code of `mvShim` after the call. -/
abbrev mvAfter (md : Meta) (n : Nat) (ts : List ValTy) (ns : List Nat) : List XInstr :=
  setsRev (n + 1) ts.length ++
    [.base (.i32Const (BitVec.ofNat 32 (tupleSize ns))),
      .base (.i32Const (BitVec.ofNat 32 (tupleAlign ns))), .base (.call md.alloc 2),
      .base (.localSet n)] ++
    storeFields n (n + 1) 0 ts (fieldOffs 0 ns) ns ++ [.base (.localGet n)]

/-- The body of `mvShim`: the call, then the rest, from any locals after the parameters. -/
theorem mvShim_body (md : Meta) (s : Sig) (ts : List ValTy) (ns : List Nat) (xs zs : List Flat)
    (hx : xs.length = (flatParams s.params).length) :
    execX M (mvShim md s ts ns).body ⟨xs ++ zs, []⟩ =
      (M.call s.name xs >>= fun rs => execX M (mvAfter md xs.length ts ns) ⟨xs ++ zs, rs.reverse⟩) := by
  simp only [mvShim, ← hx]
  rw [append6, execX_append, execX_callAfterGets, RM.bind_assoc]
  simp only [RM.pure_bind]

/-- **The typed multi-value shim computes what `mvShim` computes.** -/
theorem mvShimT_run (md : Meta) (s : Sig) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns) (xs : List Flat)
    (hx : xs.length = (flatParams s.params).length)
    (hR : RM.Returns (M.call s.name xs) fun rs => rs.map (·.type) = ValTy.flatList ts) :
    (mvShimT md s ts ns).run M xs = (mvShim md s ts ns).run M xs := by
  have hfl : (ValTy.flatList ts).length = ts.length := flatList_length hn
  have hz : ((ValTy.flatList ts).map zeroOf).length = ts.length := by simp [hfl]
  have hloc : (mvShimT md s ts ns).tys.map zeroOf =
      zeroOf (.int .i32) :: (ValTy.flatList ts).map zeroOf := rfl
  have hp : (mvShimT md s ts ns).fn.params = (flatParams s.params).length := rfl
  unfold XFnT.run XFn.run
  rw [hloc, hp, show (mvShim md s ts ns).params = (flatParams s.params).length from rfl, ← hx]
  simp only [beq_self_eq_true, RM.check_true, RM.pure_bind]
  rw [show (mvShimT md s ts ns).fn = mvShim md s ts ns from rfl, mvShim_body M md s ts ns xs _ hx,
    mvShim_body M md s ts ns xs _ hx, RM.bind_assoc, RM.bind_assoc]
  refine RM.bind_congr_returns hR fun rs hrs => ?_
  have hr : rs.length = ts.length := by
    rw [← List.length_map (f := (·.type)), hrs, hfl]
  have hlen : (mvShim md s ts ns).locals = ts.length + 1 := rfl
  rw [hlen, mvShim_after_forget M md xs rs _ (zeroOf (.int .i32)) hz hr]

end Silmaril.Proofs.Wasm.Jco.Real
