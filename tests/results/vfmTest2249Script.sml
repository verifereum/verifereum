open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2249Theory;
val () = new_theory "vfmTest2249";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2249") $ get_result_defs "vfmTestDefs2249";
val () = export_theory_no_docs ();
