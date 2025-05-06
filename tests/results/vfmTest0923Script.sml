open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0923Theory;
val () = new_theory "vfmTest0923";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0923") $ get_result_defs "vfmTestDefs0923";
val () = export_theory_no_docs ();
