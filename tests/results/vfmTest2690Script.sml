open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2690Theory;
val () = new_theory "vfmTest2690";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2690") $ get_result_defs "vfmTestDefs2690";
val () = export_theory_no_docs ();
