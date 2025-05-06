open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1616Theory;
val () = new_theory "vfmTest1616";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1616") $ get_result_defs "vfmTestDefs1616";
val () = export_theory_no_docs ();
