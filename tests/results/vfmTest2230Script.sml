open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2230Theory;
val () = new_theory "vfmTest2230";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2230") $ get_result_defs "vfmTestDefs2230";
val () = export_theory_no_docs ();
