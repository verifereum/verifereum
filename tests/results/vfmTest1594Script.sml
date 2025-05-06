open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1594Theory;
val () = new_theory "vfmTest1594";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1594") $ get_result_defs "vfmTestDefs1594";
val () = export_theory_no_docs ();
