open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2461Theory;
val () = new_theory "vfmTest2461";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2461") $ get_result_defs "vfmTestDefs2461";
val () = export_theory_no_docs ();
