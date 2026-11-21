module

public import Silmaril.Process.ImageAccess.Contract.Defs
import Silmaril.Proofs.Process.ImageAccess.Contract

@[expose] public section

namespace Silmaril.Process.ImageAccess

theorem Reader.Refines.trans {complex middle simple : Reader}
    (outer : Reader.Refines complex middle) (inner : Reader.Refines middle simple) :
    Reader.Refines complex simple := fun request bytes answer => outer request bytes (inner request bytes answer)

/-- Prove a sequence by using the continuation's WP as the prefix's postcondition. -/
theorem Program.wp_bind {α β : Type} {reader : Reader} {post : β → Prop}
    (program : Program α) (next : α → Program β) :
    (program.bind next).wp reader post ↔ program.wp reader (fun value => (next value).wp reader post) :=
  Proofs.Process.ImageAccess.wp_bind program next

theorem Program.wp_iff_run {α : Type} {reader : Reader} {post : α → Prop} (program : Program α) :
    program.wp reader post ↔ ∃ value, program.run reader = .ok value ∧ post value :=
  Proofs.Process.ImageAccess.wp_iff_run program

theorem Program.wp_transfer {α : Type} {target source : Reader} {post : α → Prop}
    (refines : Reader.Refines target source) (program : Program α) :
    program.wp source post → program.wp target post :=
  Proofs.Process.ImageAccess.wp_transfer refines program

end Silmaril.Process.ImageAccess
