open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2071Theory;
val () = new_theory "vfmTest2071";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2071") $ get_result_defs "vfmTestDefs2071";
val () = export_theory_no_docs ();
