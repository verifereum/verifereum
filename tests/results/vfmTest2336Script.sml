open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2336Theory;
val () = new_theory "vfmTest2336";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2336") $ get_result_defs "vfmTestDefs2336";
val () = export_theory_no_docs ();
