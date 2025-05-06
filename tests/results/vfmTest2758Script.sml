open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2758Theory;
val () = new_theory "vfmTest2758";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2758") $ get_result_defs "vfmTestDefs2758";
val () = export_theory_no_docs ();
