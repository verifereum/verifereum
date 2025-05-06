open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2455Theory;
val () = new_theory "vfmTest2455";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2455") $ get_result_defs "vfmTestDefs2455";
val () = export_theory_no_docs ();
