open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1437Theory;
val () = new_theory "vfmTest1437";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1437") $ get_result_defs "vfmTestDefs1437";
val () = export_theory_no_docs ();
