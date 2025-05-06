open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1218Theory;
val () = new_theory "vfmTest1218";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1218") $ get_result_defs "vfmTestDefs1218";
val () = export_theory_no_docs ();
