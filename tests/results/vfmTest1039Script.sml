open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1039Theory;
val () = new_theory "vfmTest1039";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1039") $ get_result_defs "vfmTestDefs1039";
val () = export_theory_no_docs ();
