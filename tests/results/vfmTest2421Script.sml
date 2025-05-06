open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2421Theory;
val () = new_theory "vfmTest2421";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2421") $ get_result_defs "vfmTestDefs2421";
val () = export_theory_no_docs ();
