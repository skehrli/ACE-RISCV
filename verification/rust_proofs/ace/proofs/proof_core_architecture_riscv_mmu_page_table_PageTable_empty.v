From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_architecture_riscv_mmu_page_table_PageTable_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_architecture_riscv_mmu_page_table_PageTable_empty_proof (π : thread_id) :
  core_architecture_riscv_mmu_page_table_PageTable_empty_lemma π.
Proof.
  core_architecture_riscv_mmu_page_table_PageTable_empty_prelude.

  rep liRStep.
  all: liShow.
  { 
   liInst Hevar_r2
       (make_empty_page_tree paging_system level x'3.(loc_a)).
   liInst Hevar_page_loc x'3.
   liInst Hevar_page_sz (page_table_page_size paging_system level).
    liInst Hevar_page_val
       (zero_page (page_table_page_size paging_system level)).
    rep liRStep. liShow.
  }
  (*all: sidecond_solver.*)
  (*Unshelve. all: sidecond_hammer.*)
  (*Unshelve.*)
  (*Unshelve.*)
  (*1: sidecond_solver.*)
  (*all: rep liRStep.*)
  (*all: liShow.*)
  (*all: sidecond_solver.*)
  (*all: sidecond_hammer.*)
  (*all: lazymatch goal with*)
  (*     | |- ty_has_op_type _ _ => solve_ty_has_op_type*)
  (*     | |- syn_type_compat _ _ => solve_syn_type_compat*)
  (*     end.*)
  (*all: rep liRStep.*)
  (*all: liShow.*)
  (*Unshelve.*)
  (*all: try sidecond_solver.*)
  (*all: try sidecond_hammer.*)
  (*all: liShow.*)
  (*- f_equal. solve_syn_type_eq.*)
  (*- f_equal. solve_syn_type_eq.*)
  (*- rewrite*)
  (*    (page_table_page_size_entry_count paging_system level H164).*)
  (*  done.*)
  (*- apply Forall_Forall_cb.*)
  (*  apply Forall_replicate. done.*)
  (*- unfold zero_page.*)
  (*  rewrite (page_table_page_size_words paging_system level H164).*)
  (*  apply Forall2_serialize_lpte_replicate_not_valid.*)
Qed.
End proof.
