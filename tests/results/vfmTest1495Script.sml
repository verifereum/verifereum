open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1495Theory;
val () = new_theory "vfmTest1495";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1495") $ get_result_defs "vfmTestDefs1495";
val () = export_theory_no_docs ();
