open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2878Theory;
val () = new_theory "vfmTest2878";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2878") $ get_result_defs "vfmTestDefs2878";
val () = export_theory_no_docs ();
