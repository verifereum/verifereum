open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1974Theory;
val () = new_theory "vfmTest1974";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1974") $ get_result_defs "vfmTestDefs1974";
val () = export_theory_no_docs ();
