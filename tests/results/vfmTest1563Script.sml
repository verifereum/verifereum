open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1563Theory;
val () = new_theory "vfmTest1563";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1563") $ get_result_defs "vfmTestDefs1563";
val () = export_theory_no_docs ();
