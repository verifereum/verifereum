open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2341Theory;
val () = new_theory "vfmTest2341";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2341") $ get_result_defs "vfmTestDefs2341";
val () = export_theory_no_docs ();
