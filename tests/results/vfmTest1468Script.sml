open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1468Theory;
val () = new_theory "vfmTest1468";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1468") $ get_result_defs "vfmTestDefs1468";
val () = export_theory_no_docs ();
