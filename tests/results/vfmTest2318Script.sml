open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2318Theory;
val () = new_theory "vfmTest2318";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2318") $ get_result_defs "vfmTestDefs2318";
val () = export_theory_no_docs ();
