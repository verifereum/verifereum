open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2689Theory;
val () = new_theory "vfmTest2689";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2689") $ get_result_defs "vfmTestDefs2689";
val () = export_theory_no_docs ();
