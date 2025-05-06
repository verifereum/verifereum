open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2160Theory;
val () = new_theory "vfmTest2160";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2160") $ get_result_defs "vfmTestDefs2160";
val () = export_theory_no_docs ();
