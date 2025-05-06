open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2795Theory;
val () = new_theory "vfmTest2795";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2795") $ get_result_defs "vfmTestDefs2795";
val () = export_theory_no_docs ();
