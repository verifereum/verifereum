open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2286Theory;
val () = new_theory "vfmTest2286";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2286") $ get_result_defs "vfmTestDefs2286";
val () = export_theory_no_docs ();
