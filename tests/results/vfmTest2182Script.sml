open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2182Theory;
val () = new_theory "vfmTest2182";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2182") $ get_result_defs "vfmTestDefs2182";
val () = export_theory_no_docs ();
