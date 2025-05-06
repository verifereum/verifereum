open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0803Theory;
val () = new_theory "vfmTest0803";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0803") $ get_result_defs "vfmTestDefs0803";
val () = export_theory_no_docs ();
