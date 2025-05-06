open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2353Theory;
val () = new_theory "vfmTest2353";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2353") $ get_result_defs "vfmTestDefs2353";
val () = export_theory_no_docs ();
