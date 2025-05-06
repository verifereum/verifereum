open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2169Theory;
val () = new_theory "vfmTest2169";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2169") $ get_result_defs "vfmTestDefs2169";
val () = export_theory_no_docs ();
