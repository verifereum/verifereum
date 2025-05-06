open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1192Theory;
val () = new_theory "vfmTest1192";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1192") $ get_result_defs "vfmTestDefs1192";
val () = export_theory_no_docs ();
