open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1102Theory;
val () = new_theory "vfmTest1102";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1102") $ get_result_defs "vfmTestDefs1102";
val () = export_theory_no_docs ();
