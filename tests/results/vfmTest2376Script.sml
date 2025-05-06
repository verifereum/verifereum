open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2376Theory;
val () = new_theory "vfmTest2376";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2376") $ get_result_defs "vfmTestDefs2376";
val () = export_theory_no_docs ();
