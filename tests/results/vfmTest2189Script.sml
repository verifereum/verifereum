open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2189Theory;
val () = new_theory "vfmTest2189";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2189") $ get_result_defs "vfmTestDefs2189";
val () = export_theory_no_docs ();
