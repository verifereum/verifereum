open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1336Theory;
val () = new_theory "vfmTest1336";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1336") $ get_result_defs "vfmTestDefs1336";
val () = export_theory_no_docs ();
