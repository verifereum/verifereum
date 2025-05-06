open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2082Theory;
val () = new_theory "vfmTest2082";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2082") $ get_result_defs "vfmTestDefs2082";
val () = export_theory_no_docs ();
