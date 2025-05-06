open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2225Theory;
val () = new_theory "vfmTest2225";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2225") $ get_result_defs "vfmTestDefs2225";
val () = export_theory_no_docs ();
