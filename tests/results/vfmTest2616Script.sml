open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2616Theory;
val () = new_theory "vfmTest2616";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2616") $ get_result_defs "vfmTestDefs2616";
val () = export_theory_no_docs ();
