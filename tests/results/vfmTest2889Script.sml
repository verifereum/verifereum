open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2889Theory;
val () = new_theory "vfmTest2889";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2889") $ get_result_defs "vfmTestDefs2889";
val () = export_theory_no_docs ();
