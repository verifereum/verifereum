open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2595Theory;
val () = new_theory "vfmTest2595";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2595") $ get_result_defs "vfmTestDefs2595";
val () = export_theory_no_docs ();
