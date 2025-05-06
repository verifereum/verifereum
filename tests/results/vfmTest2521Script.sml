open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2521Theory;
val () = new_theory "vfmTest2521";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2521") $ get_result_defs "vfmTestDefs2521";
val () = export_theory_no_docs ();
