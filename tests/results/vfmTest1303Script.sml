open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1303Theory;
val () = new_theory "vfmTest1303";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1303") $ get_result_defs "vfmTestDefs1303";
val () = export_theory_no_docs ();
