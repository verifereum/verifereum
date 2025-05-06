open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2165Theory;
val () = new_theory "vfmTest2165";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2165") $ get_result_defs "vfmTestDefs2165";
val () = export_theory_no_docs ();
