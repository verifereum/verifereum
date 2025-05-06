open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1431Theory;
val () = new_theory "vfmTest1431";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1431") $ get_result_defs "vfmTestDefs1431";
val () = export_theory_no_docs ();
