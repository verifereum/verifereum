open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2264Theory;
val () = new_theory "vfmTest2264";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2264") $ get_result_defs "vfmTestDefs2264";
val () = export_theory_no_docs ();
