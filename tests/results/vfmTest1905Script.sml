open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1905Theory;
val () = new_theory "vfmTest1905";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1905") $ get_result_defs "vfmTestDefs1905";
val () = export_theory_no_docs ();
