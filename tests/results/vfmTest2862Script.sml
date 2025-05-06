open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2862Theory;
val () = new_theory "vfmTest2862";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2862") $ get_result_defs "vfmTestDefs2862";
val () = export_theory_no_docs ();
