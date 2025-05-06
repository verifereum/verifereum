open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2665Theory;
val () = new_theory "vfmTest2665";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2665") $ get_result_defs "vfmTestDefs2665";
val () = export_theory_no_docs ();
