open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2371Theory;
val () = new_theory "vfmTest2371";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2371") $ get_result_defs "vfmTestDefs2371";
val () = export_theory_no_docs ();
