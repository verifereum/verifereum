open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1401Theory;
val () = new_theory "vfmTest1401";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1401") $ get_result_defs "vfmTestDefs1401";
val () = export_theory_no_docs ();
