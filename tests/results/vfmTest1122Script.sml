open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1122Theory;
val () = new_theory "vfmTest1122";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1122") $ get_result_defs "vfmTestDefs1122";
val () = export_theory_no_docs ();
