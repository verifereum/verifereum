open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1255Theory;
val () = new_theory "vfmTest1255";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1255") $ get_result_defs "vfmTestDefs1255";
val () = export_theory_no_docs ();
