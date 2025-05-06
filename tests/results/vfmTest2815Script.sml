open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2815Theory;
val () = new_theory "vfmTest2815";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2815") $ get_result_defs "vfmTestDefs2815";
val () = export_theory_no_docs ();
