open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2478Theory;
val () = new_theory "vfmTest2478";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2478") $ get_result_defs "vfmTestDefs2478";
val () = export_theory_no_docs ();
