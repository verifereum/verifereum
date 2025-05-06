open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1048Theory;
val () = new_theory "vfmTest1048";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1048") $ get_result_defs "vfmTestDefs1048";
val () = export_theory_no_docs ();
