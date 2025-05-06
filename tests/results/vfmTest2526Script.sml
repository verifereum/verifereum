open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2526Theory;
val () = new_theory "vfmTest2526";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2526") $ get_result_defs "vfmTestDefs2526";
val () = export_theory_no_docs ();
