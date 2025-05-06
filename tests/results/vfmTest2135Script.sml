open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2135Theory;
val () = new_theory "vfmTest2135";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2135") $ get_result_defs "vfmTestDefs2135";
val () = export_theory_no_docs ();
