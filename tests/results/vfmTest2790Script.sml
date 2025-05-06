open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2790Theory;
val () = new_theory "vfmTest2790";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2790") $ get_result_defs "vfmTestDefs2790";
val () = export_theory_no_docs ();
