open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1946Theory;
val () = new_theory "vfmTest1946";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1946") $ get_result_defs "vfmTestDefs1946";
val () = export_theory_no_docs ();
