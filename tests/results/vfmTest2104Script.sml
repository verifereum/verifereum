open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2104Theory;
val () = new_theory "vfmTest2104";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2104") $ get_result_defs "vfmTestDefs2104";
val () = export_theory_no_docs ();
