open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2805Theory;
val () = new_theory "vfmTest2805";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2805") $ get_result_defs "vfmTestDefs2805";
val () = export_theory_no_docs ();
