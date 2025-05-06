open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1152Theory;
val () = new_theory "vfmTest1152";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1152") $ get_result_defs "vfmTestDefs1152";
val () = export_theory_no_docs ();
