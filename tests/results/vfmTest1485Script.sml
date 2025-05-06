open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1485Theory;
val () = new_theory "vfmTest1485";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1485") $ get_result_defs "vfmTestDefs1485";
val () = export_theory_no_docs ();
