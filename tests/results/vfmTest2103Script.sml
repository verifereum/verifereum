open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2103Theory;
val () = new_theory "vfmTest2103";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2103") $ get_result_defs "vfmTestDefs2103";
val () = export_theory_no_docs ();
