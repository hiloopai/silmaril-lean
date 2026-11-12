module

public import Silmaril.Wasm.Jco.Example.Defs
public import Silmaril.Wasm.Jco.Wrap.Thms

/-!
# The litmus instance through the monadic construction

* `exMeta_ofWorld`: the metadata is what `Meta.ofWorld` reads from the resolved WIT world
  `exWorld` (by evaluation);
* `adaptor_exMeta`: the generated adaptor module, instruction by instruction (`cabi_realloc`
  calls `alloc(size, align)`; `add` forwards; `echo` allocates the out-pointer, forwards and
  returns it);
* `exConforms`: the instance has the convention's result types;
* `add_wrap`: for all `a b`, export `add` of `wrap exMeta` returns `a + b` from every state, with
  no other outcome;
* `echo_wrap`: export `echo` on `"jco"` from the empty memory returns `"jco"`, deterministically
  (a closed run of the convention, transported by `wrap_correct`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Example

open Silmaril.Wasm.Component (Flat ValTy Val)

theorem exMeta_ofWorld : Meta.ofWorld exWorld = .ok exMeta := rfl

theorem adaptor_exMeta : (adaptorOf exMeta).funcs = [
    ("cabi_realloc", { params := 4, body := [.localGet 3, .localGet 2, .call "alloc" 2] }),
    ("add", { params := 2, body := [.localGet 0, .localGet 1, .call "add" 2] }),
    ("echo", { params := 2, locals := 1, body := [.i32Const 8, .i32Const 4, .call "alloc" 2,
      .localSet 2, .localGet 0, .localGet 1, .localGet 2, .call "echo" 3, .localGet 2] })] := by
  decide

@[simp] theorem exInst_call : exInst.call = exCall := rfl

theorem exCall_alloc : exCall "alloc" = exAlloc := by simp [exCall]
theorem exCall_add : exCall "add" = exAdd := by simp [exCall]
theorem exCall_echo : exCall "echo" = exEcho := by simp [exCall]

theorem alloc_returns (xs : List Flat) :
    RM.Returns (exCall "alloc" xs) fun r => ∃ p, r = [Flat.i32 p] := by
  rw [exCall_alloc]
  intro m a m' h
  unfold exAlloc at h
  split at h
  · cases h
    exact ⟨_, rfl⟩
  · cases h

theorem echo_returns (xs : List Flat) : RM.Returns (exCall "echo" xs) (· = []) := by
  rw [exCall_echo]
  intro m a m' h
  unfold exEcho at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem exConforms : exMeta.Conforms exInst where
  alloc := alloc_returns
  outPtr := by
    intro s hs hm xs
    have hs' : s = ⟨"echo", [.string], some .string⟩ := by
      simp only [exMeta, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · simp [inMem] at hm
      · rfl
    rw [hs']
    exact echo_returns xs

theorem add_wrap (a b : BitVec 32) :
    (wrap exMeta).callExport exInst "add" [.val (.u32 a), .val (.u32 b)] =
      pure (some (.val (.u32 (a + b)))) := by
  have hadd : exAdd [Flat.i32 a, Flat.i32 b] = pure [Flat.i32 (a + b)] := rfl
  rw [wrap_correct _ _ exConforms]
  simp [Meta.spec, exMeta, Meta.specCall, Meta.specParams, Meta.specParam, ValTy.check,
    ValTy.lower, inMem, exCall_add, hadd, liftResult, ValTy.lift]

theorem det_exAlloc (m : Mem) (size align : BitVec 32) :
    RM.Det (exAlloc [Flat.i32 size, Flat.i32 align]) m
      (.ok [i32n (bump m size.toNat (max align.toNat 1)).1]
        (bump m size.toNat (max align.toNat 1)).2) := fun _ => Iff.rfl

theorem det_exEcho {m m' : Mem} (p l out : BitVec 32)
    (h : m.write out.toNat (le32 p.toNat ++ le32 l.toNat) = some m') :
    RM.Det (exEcho [Flat.i32 p, Flat.i32 l, Flat.i32 out]) m (.ok [] m') := by
  intro o
  show (match m.write out.toNat (le32 p.toNat ++ le32 l.toNat) with
    | some m' => o = Out.ok [] m'
    | none => o = Out.trap) ↔ o = Out.ok [] m'
  rw [h]

/-- Run a deterministic computation step by step. -/
macro "det_run" : tactic => `(tactic| repeat (first
  | (apply RM.det_bind_trap; done)
  | apply RM.det_bind
  | apply RM.det_pure
  | apply RM.det_get
  | apply RM.det_set
  | (apply RM.det_check; rfl)
  | (apply RM.det_ofOption; rfl)
  | apply det_exAlloc
  | (apply det_exEcho; rfl)
  | (simp only [inMem, ↓reduceIte]; done)
  | simp only [inMem, ↓reduceIte, exInst_call, exCall_alloc, exCall_echo, CoreInst.store,
      CoreInst.load, readPair, liftResult]))

/-- The wrapper of the litmus instance echoes `"jco"` from the empty memory, deterministically:
through `wrap_correct`, from a step-by-step run of the C convention. -/
theorem echo_wrap : ∃ m1, RM.Det ((wrap exMeta).callExport exInst "echo" [.string "jco"]) []
    (.ok (some (.string "jco")) m1) := by
  apply Exists.intro
  rw [wrap_correct _ _ exConforms]
  show RM.Det (exMeta.specCall exInst ⟨"echo", [.string], some .string⟩ [.string "jco"]) [] _
  unfold Meta.specCall Meta.specParams Meta.specParam Meta.specBytes
  det_run

end Silmaril.Wasm.Jco.Example
