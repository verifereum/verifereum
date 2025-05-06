open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2196Theory;
val () = new_theory "vfmTest2196";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2196") $ get_result_defs "vfmTestDefs2196";
val () = export_theory_no_docs ();
