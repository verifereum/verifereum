open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0616Theory;
val () = new_theory "vfmTest0616";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0616") $ get_result_defs "vfmTestDefs0616";
val () = export_theory_no_docs ();
