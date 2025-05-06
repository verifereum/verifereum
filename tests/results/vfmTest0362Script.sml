open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0362Theory;
val () = new_theory "vfmTest0362";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0362") $ get_result_defs "vfmTestDefs0362";
val () = export_theory_no_docs ();
