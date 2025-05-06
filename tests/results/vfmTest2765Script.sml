open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2765Theory;
val () = new_theory "vfmTest2765";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2765") $ get_result_defs "vfmTestDefs2765";
val () = export_theory_no_docs ();
