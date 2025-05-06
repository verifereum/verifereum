open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2779Theory;
val () = new_theory "vfmTest2779";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2779") $ get_result_defs "vfmTestDefs2779";
val () = export_theory_no_docs ();
