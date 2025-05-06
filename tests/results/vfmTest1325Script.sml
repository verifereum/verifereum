open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1325Theory;
val () = new_theory "vfmTest1325";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1325") $ get_result_defs "vfmTestDefs1325";
val () = export_theory_no_docs ();
