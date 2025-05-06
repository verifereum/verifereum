open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1540Theory;
val () = new_theory "vfmTest1540";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1540") $ get_result_defs "vfmTestDefs1540";
val () = export_theory_no_docs ();
