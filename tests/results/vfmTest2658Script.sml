open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2658Theory;
val () = new_theory "vfmTest2658";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2658") $ get_result_defs "vfmTestDefs2658";
val () = export_theory_no_docs ();
