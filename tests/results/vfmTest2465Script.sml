open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2465Theory;
val () = new_theory "vfmTest2465";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2465") $ get_result_defs "vfmTestDefs2465";
val () = export_theory_no_docs ();
