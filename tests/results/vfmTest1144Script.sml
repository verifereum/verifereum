open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1144Theory;
val () = new_theory "vfmTest1144";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1144") $ get_result_defs "vfmTestDefs1144";
val () = export_theory_no_docs ();
