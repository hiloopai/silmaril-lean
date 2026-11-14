module

public import Silmaril.Semantics.TraceModels.Defs
import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import Silmaril.Proofs.Semantics.TraceModels.OrderedLog.Duration
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Codiagonal
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Naturality
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Uniformity
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Laws
import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Infinite

/-!
# TraceModels

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Concrete Models, §Trace Models
(mapped by content). `PartialWriter` is the case where the output monoid acts on itself.


Theorems about `Silmaril.Semantics.TraceModels.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.TraceModels` and are only pointed at from here.
-/

public section

section

/-! ## Ordered accumulation of logs -/

namespace Silmaril.Elgot

universe u v

namespace ContinuousLog

variable {W : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W]

theorem one_le (w : W) : 1 ≤ w :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.one_le w

theorem mul_iSup {ι : Type v} [Nonempty ι] (w : W) (f : ι → W) :
    w * (⨆ i, f i) = ⨆ i, w * f i :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.mul_iSup w f

theorem iSup_mul {ι : Type v} [Nonempty ι] (f : ι → W) (w : W) :
    (⨆ i, f i) * w = ⨆ i, f i * w := by
  simpa only [← Set.range_comp, sSup_range, Function.comp_def] using
    sSup_mul (Set.range f) (Set.range_nonempty f) w

theorem le_mul_right (a b : W) : a ≤ a * b :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.le_mul_right a b

theorem le_mul_left (a b : W) : b ≤ a * b := by
  simpa only [one_mul] using mul_mono (one_le a) (le_refl b)

end ContinuousLog

namespace ContinuousLog

variable {W : Type u} [Monoid W]

@[simp] theorem prefixProd_zero (ws : ℕ → W) : prefixProd ws 0 = 1 :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_zero ws

@[simp] theorem prefixProd_succ (ws : ℕ → W) (n : ℕ) :
    prefixProd ws (n + 1) = prefixProd ws n * ws n :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_succ ws n

theorem prefixProd_add (ws : ℕ → W) (n k : ℕ) :
    prefixProd ws (n + k) = prefixProd ws n * prefixProd (fun i => ws (n + i)) k :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_add ws n k

theorem prefixProd_blocks (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (n : ℕ) :
    prefixProd (blocks ws cuts) n = prefixProd ws (cuts n) :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_blocks ws cuts hzero hmono n

variable [CompleteLattice W]

theorem prefixProd_le_omegaProduct (ws : ℕ → W) (n : ℕ) :
    prefixProd ws n ≤ omegaProduct ws :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_le_omegaProduct ws n

variable [ContinuousLog W]

theorem prefixProd_monotone (ws : ℕ → W) : Monotone (prefixProd ws) :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_monotone ws

theorem prefixProd_mono {ws vs : ℕ → W} (h : ∀ n, ws n ≤ vs n) (n : ℕ) :
    prefixProd ws n ≤ prefixProd vs n :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_mono h n

theorem omegaProduct_mono {ws vs : ℕ → W} (h : ∀ n, ws n ≤ vs n) :
    omegaProduct ws ≤ omegaProduct vs := iSup_mono (prefixProd_mono h)

/-- Any cofinal sequence of finite observations has the same limit. -/
theorem omegaProduct_eq_iSup_cofinal (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hcofinal : ∀ n, ∃ k, n ≤ cuts k) :
    omegaProduct ws = ⨆ k, prefixProd ws (cuts k) :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_eq_iSup_cofinal ws cuts hcofinal

/-- Removing a finite prefix factors its product on the left of the limit. -/
theorem omegaProduct_split (ws : ℕ → W) (n : ℕ) :
    omegaProduct ws = prefixProd ws n * omegaProduct (fun i => ws (n + i)) :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_split ws n

theorem omegaProduct_unfold (ws : ℕ → W) :
    omegaProduct ws = ws 0 * omegaProduct (fun i => ws (i + 1)) := by
  simpa only [prefixProd_succ, prefixProd_zero, one_mul, Nat.add_comm] using
    omegaProduct_split ws 1

/-- Finite regrouping preserves total logs when the block endpoints are cofinal. -/
theorem omegaProduct_regroup (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hcofinal : ∀ n, ∃ k, n ≤ cuts k) :
    omegaProduct (blocks ws cuts) = omegaProduct ws :=
  Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_regroup ws cuts hzero hmono hcofinal

end ContinuousLog

end Silmaril.Elgot

end

section

/-! ## Extended natural durations -/

namespace Silmaril.Elgot

namespace Duration

@[simp] theorem toAdd_iSup {ι : Sort*} (f : ι → Duration) :
    (⨆ i, f i).toAdd = ⨆ i, (f i).toAdd :=
  Silmaril.Proofs.Semantics.Elgot.Duration.toAdd_iSup f

theorem toAdd_sSup (s : Set Duration) :
    (sSup s).toAdd = ⨆ a ∈ s, a.toAdd :=
  Silmaril.Proofs.Semantics.Elgot.Duration.toAdd_sSup s

instance : ContinuousLog Duration :=
  Silmaril.Proofs.Semantics.Elgot.Duration.instContinuousLog

theorem tick_mul_tick : tick * tick = Multiplicative.ofAdd 2 := rfl

theorem tick_mul_tick_ne_tick : tick * tick ≠ tick := by
  change (2 : ℕ∞) ≠ 1
  exact_mod_cast (by decide : (2 : ℕ) ≠ 1)

@[simp] theorem prefixProd_tick (n : ℕ) :
    ContinuousLog.prefixProd (fun _ => tick) n = Multiplicative.ofAdd (n : ℕ∞) :=
  Silmaril.Proofs.Semantics.Elgot.Duration.prefixProd_tick n

theorem omegaProduct_tick : ContinuousLog.omegaProduct (fun _ => tick) = ⊤ :=
  Silmaril.Proofs.Semantics.Elgot.Duration.omegaProduct_tick

end Duration

end Silmaril.Elgot

end

section

/-! ## Partial computations with persistent output -/

namespace Silmaril.Elgot

universe u

namespace PartialWriter

variable {W A B C : Type u}

@[ext] theorem ext {x y : PartialWriter W A}
    (hv : x.value = y.value) (hw : x.output = y.output) : x = y :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.ext hv hw

@[elab_as_elim] theorem cases_on (x : PartialWriter W A) {p : PartialWriter W A → Prop}
    (hdiverge : ∀ w, p (diverge w)) (hdone : ∀ a w, p (done a w)) : p x :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.cases_on x hdiverge hdone

variable [Monoid W]

@[simp] theorem bind_diverge (w : W) (f : A → PartialWriter W B) :
    bind (diverge w) f = diverge w :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_diverge w f

@[simp] theorem bind_done (a : A) (w : W) (f : A → PartialWriter W B) :
    bind (done a w) f = ⟨(f a).value, w * (f a).output⟩ :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_done a w f

@[simp] theorem pure_def (a : A) : (pure a : PartialWriter W A) = done a 1 :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.pure_def a

@[simp] theorem bind_def (x : PartialWriter W A) (f : A → PartialWriter W B) :
    x >>= f = bind x f :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_def x f

@[simp] theorem bind_pure (x : PartialWriter W A) : bind x (pure : A → PartialWriter W A) = x :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_pure x

@[simp] theorem pure_bind (a : A) (f : A → PartialWriter W B) : bind (pure a) f = f a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.pure_bind a f

theorem bind_assoc (x : PartialWriter W A) (f : A → PartialWriter W B)
    (g : B → PartialWriter W C) : bind (bind x f) g = bind x (fun a => bind (f a) g) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_assoc x f g

noncomputable instance : LawfulMonad (PartialWriter W) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.instLawfulMonad

@[simp] theorem value_pure (a : A) : (pure a : PartialWriter W A).value = pure a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_pure a

@[simp] theorem value_bind (x : PartialWriter W A) (f : A → PartialWriter W B) :
    (x >>= f).value = x.value >>= fun a => (f a).value :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_bind x f

@[simp] theorem output_pure (a : A) : (pure a : PartialWriter W A).output = 1 :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_pure a

/-- Output emitted before a subsequent divergence remains observable. -/
@[simp] theorem done_bind_diverge (a : A) (w v : W) :
    (done a w >>= fun _ => (diverge v : PartialWriter W B)) = diverge (w * v) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.done_bind_diverge a w v

end PartialWriter

end Silmaril.Elgot

end

section

/-! ## PartialWriter.Traces -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

theorem runs_value_iff (f : A → PartialWriter W (B ⊕ A)) (a : A) (b : B) :
    Part.Runs (fun a => (f a).value) a b ↔ ∃ w, Runs f a w b :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.runs_value_iff f a b

namespace Prefix

theorem append {f : A → PartialWriter W (B ⊕ A)} {a b c : A} {v w : W}
    (h : Prefix f a v b) (k : Prefix f b w c) : Prefix f a (v * w) c :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.append h k

theorem append_run {f : A → PartialWriter W (B ⊕ A)} {a z : A} {b : B} {v w : W}
    (h : Prefix f a v z) (k : Runs f z w b) : Runs f a (v * w) b :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.append_run h k

end Prefix

namespace Runs

theorem unique {f : A → PartialWriter W (B ⊕ A)} {a : A} {b c : B} {v w : W}
    (h : Runs f a v b) (k : Runs f a w c) : v = w ∧ b = c :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.unique h k

theorem last {f : A → PartialWriter W (B ⊕ A)} {a : A} {b : B} {v : W}
    (h : Runs f a v b) :
    ∃ w z, Prefix f a w z ∧ Sum.inl b ∈ (f z).value ∧ w * (f z).output = v :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.last h

end Runs

end Silmaril.Elgot.PartialWriter

end

section

/-! ## Iteration with persistent finite and infinite output -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

theorem observations_nonempty (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (observations f a).Nonempty :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.observations_nonempty f a

variable [CompleteLattice W]

theorem le_iterOutput {f : A → PartialWriter W (B ⊕ A)} {a z : A} {w : W}
    (h : Prefix f a w z) : w * (f z).output ≤ iterOutput f a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.le_iterOutput h

theorem iterOutput_le {f : A → PartialWriter W (B ⊕ A)} {a : A} {v : W}
    (h : ∀ w z, Prefix f a w z → w * (f z).output ≤ v) : iterOutput f a ≤ v :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_le h

theorem initial_le_iterOutput (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (f a).output ≤ iterOutput f a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.initial_le_iterOutput f a

theorem iterOutput_stop (f : A → PartialWriter W (B ⊕ A)) (a : A)
    (hstop : ∀ a', Sum.inr a' ∉ (f a).value) : iterOutput f a = (f a).output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_stop f a hstop

variable [ContinuousLog W]

theorem iterOutput_step (f : A → PartialWriter W (B ⊕ A)) {a a' : A}
    (hs : Sum.inr a' ∈ (f a).value) :
    iterOutput f a = (f a).output * iterOutput f a' :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_step f hs

omit [ContinuousLog W] in
@[simp] theorem value_iter (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (iter f a).value = iter (fun a => (f a).value) a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_iter f a

omit [ContinuousLog W] in
@[simp] theorem output_iter (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (iter f a).output = iterOutput f a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_iter f a

theorem fixpoint (f : A → PartialWriter W (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.fixpoint f

/-- A finite successful loop has exactly its finite accumulated output. -/
theorem Runs.iter_eq_done {f : A → PartialWriter W (B ⊕ A)} {a : A} {w : W} {b : B}
    (h : Runs f a w b) : iter f a = PartialWriter.done b w :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.iter_eq_done h

omit [ContinuousLog W] in
theorem mem_value_iter_iff (f : A → PartialWriter W (B ⊕ A)) (a : A) (b : B) :
    b ∈ (iter f a).value ↔ ∃ w, Runs f a w b :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_value_iter_iff f a b

end Silmaril.Elgot.PartialWriter

end

section

/-! ## PartialWriter.Algebra -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W]

@[simp] theorem value_map (f : A → B) (x : PartialWriter W A) :
    (f <$> x).value = f <$> x.value :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_map f x

@[simp] theorem output_map (f : A → B) (x : PartialWriter W A) :
    (f <$> x).output = x.output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_map f x

theorem value_mapReturn (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A) :
    (mapReturn f g a).value =
      mapReturn (fun a => (f a).value) (fun b => (g b).value) a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_mapReturn f g a

theorem mapReturn_inr (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) {a a' : A} (h : Sum.inr a' ∈ (f a).value) :
    mapReturn f g a = done (Sum.inr a') (f a).output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.mapReturn_inr f g h

theorem mem_mapReturn_inr_iff (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a a' : A) :
    Sum.inr a' ∈ (mapReturn f g a).value ↔ Sum.inr a' ∈ (f a).value :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_mapReturn_inr_iff f g a a'

theorem Prefix.mapReturn_iff (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a z : A) (w : W) :
    Prefix (mapReturn f g) a w z ↔ Prefix f a w z :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.mapReturn_iff f g a z w

end Silmaril.Elgot.PartialWriter

end

section

/-! ## Flattening nested partial-writer iteration -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

@[simp] theorem value_flattenBody (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    (flattenBody f a).value = flattenBody (fun a => (f a).value) a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_flattenBody f a

@[simp] theorem output_flattenBody (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    (flattenBody f a).output = (f a).output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_flattenBody f a

theorem mem_flattenBody_continue (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a a' : A) :
    Sum.inr a' ∈ (flattenBody f a).value ↔
      Sum.inl (Sum.inr a') ∈ (f a).value ∨ Sum.inr a' ∈ (f a).value :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_flattenBody_continue f a a'

theorem Prefix.snoc {f : A → PartialWriter W (B ⊕ A)} {a z z' : A} {w : W}
    (h : Prefix f a w z) (hs : Sum.inr z' ∈ (f z).value) :
    Prefix f a (w * (f z).output) z' :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.snoc h hs

theorem Prefix.flatten {f : A → PartialWriter W ((B ⊕ A) ⊕ A)} {a z : A} {w : W}
    (h : Prefix f a w z) : Prefix (flattenBody f) a w z :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten h

theorem Runs.flatten_continue {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a a' : A} {w : W} (h : Runs f a w (.inr a')) :
    Prefix (flattenBody f) a w a' :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.flatten_continue h

variable [CompleteLattice W] [ContinuousLog W]

theorem Prefix.iter_flatten {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (iter f) a w z) :
    Prefix (flattenBody f) a w z :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.iter_flatten h

/-- Continue scanning a flat prefix after already accumulated outer and inner prefixes. -/
theorem Prefix.flatten_decompose_aux {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (flattenBody f) a w z) :
    ∀ {start c : A} {u v : W}, Prefix (iter f) start u c → Prefix f c v a →
      ∃ c' u' v', Prefix (iter f) start u' c' ∧ Prefix f c' v' z ∧ u' * v' = u * v * w :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten_decompose_aux h

/-- Every flat observation crosses finitely many outer boundaries, then observes an inner prefix. -/
theorem Prefix.flatten_decompose {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (flattenBody f) a w z) :
    ∃ c u v, Prefix (iter f) a u c ∧ Prefix f c v z ∧ u * v = w :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten_decompose h

theorem iterOutput_codiagonal (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    iterOutput (iter f) a = iterOutput (flattenBody f) a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_codiagonal f a

theorem codiagonal (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.codiagonal f

end Silmaril.Elgot.PartialWriter

end

section

/-! ## PartialWriter.Naturality -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W]

theorem Runs.iter_mapReturn {f : A → PartialWriter W (B ⊕ A)}
    {a : A} {w : W} {b : B} (h : Runs f a w b) (g : B → PartialWriter W C) :
    iter (mapReturn f g) a = PartialWriter.done b w >>= g :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.iter_mapReturn h g

omit [CompleteLattice W] [ContinuousLog W] in
theorem output_mapReturn_of_no_return (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A)
    (hn : ∀ b, Sum.inl b ∉ (f a).value) :
    (mapReturn f g a).output = (f a).output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_mapReturn_of_no_return f g a hn

omit [ContinuousLog W] in
theorem iterOutput_mapReturn_of_no_return (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A)
    (hn : ∀ b, b ∉ (iter f a).value) :
    iterOutput (mapReturn f g) a = iterOutput f a :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_mapReturn_of_no_return f g a hn

theorem naturality (f : A → PartialWriter W (B ⊕ A)) (g : B → PartialWriter W C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.naturality f g

end Silmaril.Elgot.PartialWriter

end

section

/-! ## PartialWriter.Uniformity -/

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W]

variable (f : A → PartialWriter W (B ⊕ A)) (g : C → PartialWriter W (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))

include comm

theorem uniform_value_comm :
    ((fun a => (f a).value) >=> liftPure (Sum.map id h)) =
      (liftPure h >=> fun c => (g c).value) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniform_value_comm f g h comm

theorem uniform_output (a : A) : (f a).output = (g (h a)).output :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniform_output f g h comm a

theorem Prefix.uniform_forward {a z : A} {w : W} (p : Prefix f a w z) :
    Prefix g (h a) w (h z) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.uniform_forward f g h comm p

theorem Prefix.uniform_reverse {c z : C} {w : W} (p : Prefix g c w z) :
    ∀ a, c = h a → ∃ a', z = h a' ∧ Prefix f a w a' :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.uniform_reverse f g h comm p

variable [CompleteLattice W]

theorem uniformity : iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniformity f g h comm

end Silmaril.Elgot.PartialWriter

end

section

/-! ## Complete Elgot laws for persistent output -/

namespace Silmaril.Elgot.PartialWriter

universe u

noncomputable instance {W : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W] :
    LawfulElgotMonad (PartialWriter W) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.instLawfulElgotMonadOfContinuousLog

end Silmaril.Elgot.PartialWriter

end

section

/-! ## Infinite output streams -/

namespace Silmaril.Elgot.PartialWriter

open ContinuousLog

variable {W : Type} [Monoid W]

theorem Prefix.stream_product (ws : ℕ → W) {a z : ℕ} {w : W}
    (hp : Prefix (stream ws) a w z) : prefixProd ws a * w = prefixProd ws z :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.stream_product ws hp

theorem stream_prefix (ws : ℕ → W) (n : ℕ) :
    Prefix (stream ws) 0 (prefixProd ws n) n :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.stream_prefix ws n

theorem stream_no_run (ws : ℕ → W) {a : ℕ} {w : W} {b : PUnit}
    (hr : Runs (stream ws) a w b) : False :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.stream_no_run ws hr

variable [CompleteLattice W] [ContinuousLog W]

theorem iterOutput_stream (ws : ℕ → W) :
    iterOutput (stream ws) 0 = omegaProduct ws :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_stream ws

/-- Infinite iteration preserves its entire ordered product despite returning no value. -/
theorem iter_stream (ws : ℕ → W) :
    iter (stream ws) 0 = diverge (omegaProduct ws) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iter_stream ws

/-- Repeated emission retains its infinite product without returning a value. -/
theorem iter_emit_forever (w : W) (a : PUnit) :
    iter (fun a : PUnit => done (Sum.inr a : PUnit ⊕ PUnit) w) a =
      diverge (omegaProduct (fun _ => w)) :=
  Silmaril.Proofs.Semantics.Elgot.PartialWriter.iter_emit_forever w a

end Silmaril.Elgot.PartialWriter

end
