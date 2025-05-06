open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2917Theory;
val () = new_theory "vfmTest2917";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2917") $ get_result_defs "vfmTestDefs2917";
val () = export_theory_no_docs ();
