From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_architecture_riscv_mmu_page_table_entry_PageTableEntry_decode_pointer.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma core_architecture_riscv_mmu_page_table_entry_PageTableEntry_decode_pointer_proof (π : thread_id) :
  core_architecture_riscv_mmu_page_table_entry_PageTableEntry_decode_pointer_lemma π.
Proof.
  core_architecture_riscv_mmu_page_table_entry_PageTableEntry_decode_pointer_prelude.

  rep <-! liRStep; liShow.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: first [(rewrite MinInt_eq MaxInt_eq;
      unfold min_int, max_int, int_modulus, int_half_modulus, bits_per_int, bytes_per_int, bits_per_byte;
      cbn;
      lia)
    | (unfold decode_page_table_entry_pointer, wrap_to_it, wrap_unsigned, usize_modulus, int_modulus in *;
      cbn in *;
      done)].
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
