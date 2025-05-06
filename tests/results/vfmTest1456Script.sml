open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1456Theory;
val () = new_theory "vfmTest1456";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1456") $ get_result_defs "vfmTestDefs1456";
val () = export_theory_no_docs ();
