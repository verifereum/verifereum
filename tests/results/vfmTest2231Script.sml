open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2231Theory;
val () = new_theory "vfmTest2231";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2231") $ get_result_defs "vfmTestDefs2231";
val () = export_theory_no_docs ();
