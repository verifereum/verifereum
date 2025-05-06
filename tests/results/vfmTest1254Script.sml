open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1254Theory;
val () = new_theory "vfmTest1254";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1254") $ get_result_defs "vfmTestDefs1254";
val () = export_theory_no_docs ();
