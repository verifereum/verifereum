open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2199Theory;
val () = new_theory "vfmTest2199";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2199") $ get_result_defs "vfmTestDefs2199";
val () = export_theory_no_docs ();
