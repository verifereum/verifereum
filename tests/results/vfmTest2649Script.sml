open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2649Theory;
val () = new_theory "vfmTest2649";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2649") $ get_result_defs "vfmTestDefs2649";
val () = export_theory_no_docs ();
