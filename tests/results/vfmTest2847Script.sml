open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2847Theory;
val () = new_theory "vfmTest2847";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2847") $ get_result_defs "vfmTestDefs2847";
val () = export_theory_no_docs ();
