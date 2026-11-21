module

public import Silmaril.Process.ImageAccess.Contract.Defs

@[expose] public section

namespace Silmaril.Proofs.Process.ImageAccess

open Silmaril.Process.ImageAccess

theorem wp_bind {α β : Type} {reader : Reader} {post : β → Prop}
    (program : Program α) (next : α → Program β) :
    (program.bind next).wp reader post ↔ program.wp reader (fun value => (next value).wp reader post) := by
  induction program with
  | done value => rfl
  | read request resume ih => simp only [Program.bind, Program.wp, ih]

theorem wp_iff_run {α : Type} {reader : Reader} {post : α → Prop} (program : Program α) :
    program.wp reader post ↔ ∃ value, program.run reader = .ok value ∧ post value := by
  induction program with
  | done value => simp [Program.wp, Program.run]
  | read request next ih =>
    cases eq : reader request with
    | error reason => simp [Program.wp, Program.run, eq]
    | ok bytes => simpa [Program.wp, Program.run, eq] using ih bytes

theorem wp_transfer {α : Type} {target source : Reader} {post : α → Prop}
    (refines : Reader.Refines target source) (program : Program α) :
    program.wp source post → program.wp target post := by
  induction program with
  | done value => exact id
  | read request next ih =>
    rintro ⟨bytes, answer, rest⟩
    exact ⟨bytes, refines request bytes answer, ih bytes rest⟩

end Silmaril.Proofs.Process.ImageAccess
