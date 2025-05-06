open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1947Theory;
val () = new_theory "vfmTest1947";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1947") $ get_result_defs "vfmTestDefs1947";
val () = export_theory_no_docs ();
