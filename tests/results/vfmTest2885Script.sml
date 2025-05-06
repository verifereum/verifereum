open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2885Theory;
val () = new_theory "vfmTest2885";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2885") $ get_result_defs "vfmTestDefs2885";
val () = export_theory_no_docs ();
