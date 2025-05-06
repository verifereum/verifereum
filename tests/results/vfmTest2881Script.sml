open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2881Theory;
val () = new_theory "vfmTest2881";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2881") $ get_result_defs "vfmTestDefs2881";
val () = export_theory_no_docs ();
