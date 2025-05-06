open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1202Theory;
val () = new_theory "vfmTest1202";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1202") $ get_result_defs "vfmTestDefs1202";
val () = export_theory_no_docs ();
