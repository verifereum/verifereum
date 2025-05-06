open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1510Theory;
val () = new_theory "vfmTest1510";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1510") $ get_result_defs "vfmTestDefs1510";
val () = export_theory_no_docs ();
