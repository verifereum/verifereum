open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2244Theory;
val () = new_theory "vfmTest2244";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2244") $ get_result_defs "vfmTestDefs2244";
val () = export_theory_no_docs ();
