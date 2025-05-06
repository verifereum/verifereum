open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1165Theory;
val () = new_theory "vfmTest1165";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1165") $ get_result_defs "vfmTestDefs1165";
val () = export_theory_no_docs ();
