open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1038Theory;
val () = new_theory "vfmTest1038";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1038") $ get_result_defs "vfmTestDefs1038";
val () = export_theory_no_docs ();
