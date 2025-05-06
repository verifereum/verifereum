open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2000Theory;
val () = new_theory "vfmTest2000";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2000") $ get_result_defs "vfmTestDefs2000";
val () = export_theory_no_docs ();
