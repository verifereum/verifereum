open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2801Theory;
val () = new_theory "vfmTest2801";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2801") $ get_result_defs "vfmTestDefs2801";
val () = export_theory_no_docs ();
