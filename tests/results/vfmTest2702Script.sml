open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2702Theory;
val () = new_theory "vfmTest2702";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2702") $ get_result_defs "vfmTestDefs2702";
val () = export_theory_no_docs ();
