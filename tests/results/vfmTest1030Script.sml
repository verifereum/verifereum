open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1030Theory;
val () = new_theory "vfmTest1030";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1030") $ get_result_defs "vfmTestDefs1030";
val () = export_theory_no_docs ();
