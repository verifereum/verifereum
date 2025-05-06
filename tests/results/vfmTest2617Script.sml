open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2617Theory;
val () = new_theory "vfmTest2617";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2617") $ get_result_defs "vfmTestDefs2617";
val () = export_theory_no_docs ();
