open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1894Theory;
val () = new_theory "vfmTest1894";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1894") $ get_result_defs "vfmTestDefs1894";
val () = export_theory_no_docs ();
