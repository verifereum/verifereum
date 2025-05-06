open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2835Theory;
val () = new_theory "vfmTest2835";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2835") $ get_result_defs "vfmTestDefs2835";
val () = export_theory_no_docs ();
