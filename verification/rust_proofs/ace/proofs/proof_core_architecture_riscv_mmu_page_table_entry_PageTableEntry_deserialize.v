From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_architecture_riscv_mmu_page_table_entry_PageTableEntry_deserialize.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_architecture_riscv_mmu_page_table_entry_PageTableEntry_deserialize_proof (π : thread_id) :
  core_architecture_riscv_mmu_page_table_entry_PageTableEntry_deserialize_lemma π.
Proof.
  core_architecture_riscv_mmu_page_table_entry_PageTableEntry_deserialize_prelude.

  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: first [econstructor; eauto | idtac].
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
