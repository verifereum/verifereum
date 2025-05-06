open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2314Theory;
val () = new_theory "vfmTest2314";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2314") $ get_result_defs "vfmTestDefs2314";
val () = export_theory_no_docs ();
