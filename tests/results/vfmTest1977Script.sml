open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1977Theory;
val () = new_theory "vfmTest1977";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1977") $ get_result_defs "vfmTestDefs1977";
val () = export_theory_no_docs ();
