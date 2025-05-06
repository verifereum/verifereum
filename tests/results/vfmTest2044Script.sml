open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2044Theory;
val () = new_theory "vfmTest2044";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2044") $ get_result_defs "vfmTestDefs2044";
val () = export_theory_no_docs ();
