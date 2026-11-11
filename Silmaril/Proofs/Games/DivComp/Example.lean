module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.Strategy.Thms

/-!
# Two divergence-free strategies whose composite diverges

`ping` has one operation with one answer. The server `limits ⊤ : empty ↠ ping`
and the client `limits ⊤ : ping ↠ ping` (all legal plays, all infinite legal
plays, no divergence) interact forever after the client is asked a question:
the client calls `ping` again and again and the server answers at once. The
visible play stays `[ask]`, so the composite diverges after it.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.DivComp.Example

open Silmaril.Games

/-- One operation, one answer. -/
def ping : Sig.{0} := ⟨PUnit, fun _ => PUnit⟩

/-- One served request. -/
def srv : List (Move Sig.empty ping) := [.inr (.ask PUnit.unit), .inr (.ans PUnit.unit PUnit.unit)]

/-- One call by the client. -/
def cli : List (Move ping ping) := [.inl (.ask PUnit.unit), .inl (.ans PUnit.unit PUnit.unit)]

/-- The server after `n` requests. -/
def sPlay (n : ℕ) : List (Move Sig.empty ping) := (List.replicate n srv).flatten

/-- The client after being asked and making `n` calls. -/
def tPlay (n : ℕ) : List (Move ping ping) := .inr (.ask PUnit.unit) :: (List.replicate n cli).flatten

theorem zip_play (n : ℕ) : Zip (sPlay n) ((List.replicate n cli).flatten) [] := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    simp only [sPlay, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact .sync _ (.sync _ ih)

theorem zip_tPlay (n : ℕ) : Zip (sPlay n) (tPlay n) [.inr (.ask PUnit.unit)] :=
  .right _ (zip_play n)

theorem path_sPlay (n : ℕ) : Path .idle (sPlay n) .idle := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    simp only [sPlay, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact .cons (.ask _) (.cons (.ret _ _) ih)

theorem path_cli (n : ℕ) :
    Path (.run PUnit.unit) ((List.replicate n cli).flatten) (.run PUnit.unit : Pos ping ping) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons] at ih ⊢
    exact .cons (.call _ _) (.cons (.reply _ _ _) ih)

theorem path_tPlay (n : ℕ) : Path .idle (tPlay n) (.run PUnit.unit) := .cons (.ask _) (path_cli n)

theorem flatten_mono {α : Type} {n : ℕ} (l : List α) : (List.replicate n l).flatten <+:
    (List.replicate (n + 1) l).flatten :=
  ⟨l, by rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]⟩

theorem length_flatten {α : Type} (l : List α) (n : ℕ) :
    ((List.replicate n l).flatten).length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- The divergence-free server. -/
def server : DStrategy Sig.empty ping := DStrategy.limits ⊤

/-- The divergence-free client. -/
def client : DStrategy ping ping := DStrategy.limits ⊤

theorem sPlay_mono : Chain.Mono sPlay := fun _ => flatten_mono _

theorem tPlay_mono : Chain.Mono tPlay := fun _ => List.cons_prefix_cons.2 ⟨rfl, flatten_mono _⟩

theorem sPlay_unbounded : Chain.Unbounded sPlay := fun k =>
  ⟨k, by simp [sPlay, srv]; omega⟩

theorem tPlay_unbounded : Chain.Unbounded tPlay := fun k =>
  ⟨k, by simp [tPlay, cli]; omega⟩

theorem lim_top {E F : Sig.{0}} {c : Chain (Move E F)} (hm : c.Mono) (hu : c.Unbounded)
    (hl : ∀ n, Legal (c n)) : c.lim ∈ (DStrategy.limits (⊤ : Strategy E F)).inf :=
  ⟨Chain.isInfPlay_lim hm hu, fun _ ⟨n, hq⟩ => Strategy.mem_top.2 ((hl n).of_prefix hq)⟩

/-- The infinite chatter of the server and the client. -/
def chatter : DStrategy.InfInteraction server client where
  s := sPlay
  t := tPlay
  p := fun _ => [.inr (.ask PUnit.unit)]
  zip := zip_tPlay
  mem_s n := Strategy.mem_top.2 ⟨_, path_sPlay n⟩
  mem_t n := Strategy.mem_top.2 ⟨_, path_tPlay n⟩
  mono_s := sPlay_mono
  mono_t := tPlay_mono
  mono_p _ := List.prefix_refl _
  unbounded k := ⟨k, by have := sPlay_unbounded k; simp [sPlay, srv] at this ⊢; omega⟩
  lim_s _ := lim_top sPlay_mono sPlay_unbounded fun n => ⟨_, path_sPlay n⟩
  lim_t _ := lim_top tPlay_mono tPlay_unbounded fun n => ⟨_, path_tPlay n⟩

theorem server_div : server.div = ∅ := rfl
theorem client_div : client.div = ∅ := rfl

theorem comp_div : [.inr (.ask PUnit.unit)] ∈ (server.comp client).div := .inr ⟨chatter, fun _ => rfl⟩

end Silmaril.Proofs.Games.DivComp.Example
