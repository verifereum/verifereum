open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2668Theory;
val () = new_theory "vfmTest2668";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2668") $ get_result_defs "vfmTestDefs2668";
val () = export_theory_no_docs ();
