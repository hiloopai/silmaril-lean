module

public import Silmaril.Proofs.Wasm.Jco.Styles.Spill.Scalar
public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Shim

/-!
# Spilled parameters: what the shim computes after the canonical stores

* `execX_spillLoads_at`: in a state whose memory holds the stored fields, the shim's loads push
  the flat lowering of the parameters;
* **`spillShim_at`**: in such a state the shim is the call of the function on the flat lowering.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.RM
open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst)

theorem checkList_cons {t : ValTy} {ts : List ValTy} {v : Val} {vals : List Val}
    (h : ValTy.checkList (t :: ts) (v :: vals) = true) :
    t.check v = true ∧ ValTy.checkList ts vals = true := by
  simpa [ValTy.checkList] using h

theorem checkList_length : ∀ {ts : List ValTy} {vals : List Val},
    ValTy.checkList ts vals = true → ts.length = vals.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    rw [List.length_cons, List.length_cons, checkList_length (checkList_cons h).2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ValTy.checkList] at h

theorem spillLoads_step {s : M.St} {p : BitVec 32} {t : ValTy} {ts : List ValTy} {o n : Nat}
    {os ns : List Nat} {v : Val} {vals : List Val} {st : List Flat} {r : Flat}
    (ht : scalarSize t = some n) (hv : t.check v = true) (hr : t.lower v = [r])
    (hw0 : (M.mem s).read (p.toNat + o) n = some (leBytes n (normField t r).bits.toNat))
    (ih : execX M (spillLoads ts os ns) ⟨[Flat.i32 p], r :: st⟩ s =
      (pure ⟨[Flat.i32 p], (ValTy.lowerList ts vals).reverse ++ r :: st⟩ : RM M.St Frame) s) :
    execX M (spillLoads (t :: ts) (o :: os) (n :: ns)) ⟨[Flat.i32 p], st⟩ s =
      (pure ⟨[Flat.i32 p], (ValTy.lowerList (t :: ts) (v :: vals)).reverse ++ st⟩ :
        RM M.St Frame) s := by
  have hlow : ValTy.lowerList (t :: ts) (v :: vals) = r :: ValTy.lowerList ts vals := by
    simp [ValTy.lowerList, hr]
  rw [spillLoads, execX_append, hlow]
  simp only [execX, XInstr.step, AInstr.step, List.getElem?_cons_zero, asI32?, RM.ofOption_some,
    RM.pure_bind, RM.bind_assoc]
  rw [bind_at (load_at M hw0), loadVal_store ht hv hr, ih]
  simp

theorem execX_spillLoads_at {s : M.St} {p : BitVec 32} : ∀ (ts : List ValTy) (os ns : List Nat)
    (vals : List Val) (st : List Flat), ts.mapM scalarSize = some ns → os.length = ns.length →
    ValTy.checkList ts vals = true →
    (∀ w ∈ fieldWrites p.toNat ts os ns (ValTy.lowerList ts vals),
      (M.mem s).read w.1 w.2.length = some w.2) →
    execX M (spillLoads ts os ns) ⟨[Flat.i32 p], st⟩ s =
      (pure ⟨[Flat.i32 p], (ValTy.lowerList ts vals).reverse ++ st⟩ : RM M.St Frame) s
  | [], os, ns, vals, st, _, _, hc, _ => by
    have hv : vals = [] := by cases vals <;> simp_all [ValTy.checkList]
    subst hv
    cases os <;> cases ns <;> rfl
  | t :: ts, o :: os, ns, v :: vals, st, hn, hl, hc, hw => by
    obtain ⟨n, ht, ns', hts, rfl⟩ := mapM_cons_some hn
    obtain ⟨hv, hcs⟩ := checkList_cons hc
    obtain ⟨r, hr, -⟩ := lower_scalar ht hv
    have hws : ∀ w ∈ fieldWrites p.toNat (t :: ts) (o :: os) (n :: ns') (r :: ValTy.lowerList ts vals),
        (M.mem s).read w.1 w.2.length = some w.2 := by
      simpa [ValTy.lowerList, hr] using hw
    have hw0 : (M.mem s).read (p.toNat + o) n = some (leBytes n (normField t r).bits.toNat) := by
      simpa [leBytes_length] using hws _ List.mem_cons_self
    exact spillLoads_step M ht hv hr hw0 (execX_spillLoads_at ts os ns' vals (r :: st) hts
      (by simpa using hl) hcs (fun w h => hws w (List.mem_cons_of_mem _ h)))
  | _ :: _, [], ns, _, _, hn, hl, _, _ => by
    obtain ⟨n, _, ns', _, rfl⟩ := mapM_cons_some hn
    simp at hl
  | _ :: _, _ :: _, _, [], _, _, _, hc, _ => by simp [ValTy.checkList] at hc

theorem lowerList_length : ∀ {ts : List ValTy} {vals : List Val} {ns : List Nat},
    ts.mapM scalarSize = some ns → ValTy.checkList ts vals = true →
    (ValTy.lowerList ts vals).length = ts.length
  | [], _, _, _, _ => by simp [ValTy.lowerList]
  | t :: ts, v :: vals, _, hn, hc => by
    obtain ⟨n, ht, ns', hts, rfl⟩ := mapM_cons_some hn
    obtain ⟨r, hr, -⟩ := lower_scalar ht (checkList_cons hc).1
    simp [ValTy.lowerList, hr, lowerList_length hts (checkList_cons hc).2]
  | _ :: _, [], _, _, hc => by simp [ValTy.checkList] at hc

/-- **In a state holding the stored parameters, the spill shim calls the function on their flat
lowering.** -/
theorem spillShim_at (sig : Sig) {ts : List ValTy} {ns : List Nat}
    (hn : ts.mapM scalarSize = some ns) {vals : List Val} (hc : ValTy.checkList ts vals = true)
    {s : M.St} {p : BitVec 32}
    (hw : ∀ w ∈ fieldWrites p.toNat ts (fieldOffs 0 ns) ns (ValTy.lowerList ts vals),
      (M.mem s).read w.1 w.2.length = some w.2) :
    (spillShim sig ts ns).run M [Flat.i32 p] s = M.call sig.name (ValTy.lowerList ts vals) s := by
  have hl := execX_spillLoads_at M ts (fieldOffs 0 ns) ns vals [] hn (fieldOffs_length 0 ns) hc hw
  have hk : ts.length = (ValTy.lowerList ts vals).reverse.length := by
    rw [List.length_reverse, lowerList_length hn hc]
  have hcall : execX M [.base (.call sig.name ts.length)]
      ⟨[Flat.i32 p], (ValTy.lowerList ts vals).reverse ++ []⟩ =
        (M.call sig.name (ValTy.lowerList ts vals) >>= fun rs =>
          pure ⟨[Flat.i32 p], rs.reverse⟩) := by
    rw [List.append_nil, execX_cons, XInstr.step, step_call M _ _ (by simp [hk])]
    simp only [hk, List.take_length, List.reverse_reverse, List.drop_length, List.append_nil,
      RM.bind_assoc, execX, RM.pure_bind]
  unfold XFn.run spillShim
  simp only [List.length_singleton, beq_self_eq_true, RM.check_true, RM.pure_bind,
    List.replicate_zero, List.append_nil]
  rw [execX_append, RM.bind_assoc, bind_at hl, hcall, RM.bind_assoc]
  simp only [RM.pure_bind, List.reverse_reverse, RM.bind_pure]

end Silmaril.Proofs.Wasm.Jco
