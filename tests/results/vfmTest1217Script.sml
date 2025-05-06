open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1217Theory;
val () = new_theory "vfmTest1217";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1217") $ get_result_defs "vfmTestDefs1217";
val () = export_theory_no_docs ();
