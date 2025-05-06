open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2564Theory;
val () = new_theory "vfmTest2564";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2564") $ get_result_defs "vfmTestDefs2564";
val () = export_theory_no_docs ();
