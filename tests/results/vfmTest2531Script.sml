open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2531Theory;
val () = new_theory "vfmTest2531";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2531") $ get_result_defs "vfmTestDefs2531";
val () = export_theory_no_docs ();
