open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1605Theory;
val () = new_theory "vfmTest1605";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1605") $ get_result_defs "vfmTestDefs1605";
val () = export_theory_no_docs ();
