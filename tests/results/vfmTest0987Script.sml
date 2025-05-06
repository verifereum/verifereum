open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0987Theory;
val () = new_theory "vfmTest0987";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0987") $ get_result_defs "vfmTestDefs0987";
val () = export_theory_no_docs ();
