open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2902Theory;
val () = new_theory "vfmTest2902";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2902") $ get_result_defs "vfmTestDefs2902";
val () = export_theory_no_docs ();
