open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1230Theory;
val () = new_theory "vfmTest1230";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1230") $ get_result_defs "vfmTestDefs1230";
val () = export_theory_no_docs ();
