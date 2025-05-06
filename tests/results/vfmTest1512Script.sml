open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1512Theory;
val () = new_theory "vfmTest1512";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1512") $ get_result_defs "vfmTestDefs1512";
val () = export_theory_no_docs ();
