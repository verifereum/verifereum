open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2841Theory;
val () = new_theory "vfmTest2841";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2841") $ get_result_defs "vfmTestDefs2841";
val () = export_theory_no_docs ();
