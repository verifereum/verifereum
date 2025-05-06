open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2744Theory;
val () = new_theory "vfmTest2744";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2744") $ get_result_defs "vfmTestDefs2744";
val () = export_theory_no_docs ();
