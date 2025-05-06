open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2516Theory;
val () = new_theory "vfmTest2516";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2516") $ get_result_defs "vfmTestDefs2516";
val () = export_theory_no_docs ();
