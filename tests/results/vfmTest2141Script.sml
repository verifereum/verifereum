open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2141Theory;
val () = new_theory "vfmTest2141";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2141") $ get_result_defs "vfmTestDefs2141";
val () = export_theory_no_docs ();
