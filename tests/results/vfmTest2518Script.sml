open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2518Theory;
val () = new_theory "vfmTest2518";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2518") $ get_result_defs "vfmTestDefs2518";
val () = export_theory_no_docs ();
