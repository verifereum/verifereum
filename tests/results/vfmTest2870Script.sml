open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2870Theory;
val () = new_theory "vfmTest2870";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2870") $ get_result_defs "vfmTestDefs2870";
val () = export_theory_no_docs ();
