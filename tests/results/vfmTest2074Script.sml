open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2074Theory;
val () = new_theory "vfmTest2074";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2074") $ get_result_defs "vfmTestDefs2074";
val () = export_theory_no_docs ();
