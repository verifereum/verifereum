open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1546Theory;
val () = new_theory "vfmTest1546";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1546") $ get_result_defs "vfmTestDefs1546";
val () = export_theory_no_docs ();
