open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2283Theory;
val () = new_theory "vfmTest2283";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2283") $ get_result_defs "vfmTestDefs2283";
val () = export_theory_no_docs ();
