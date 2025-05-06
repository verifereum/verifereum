open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2425Theory;
val () = new_theory "vfmTest2425";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2425") $ get_result_defs "vfmTestDefs2425";
val () = export_theory_no_docs ();
