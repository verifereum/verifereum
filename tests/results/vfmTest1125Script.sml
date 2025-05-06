open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1125Theory;
val () = new_theory "vfmTest1125";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1125") $ get_result_defs "vfmTestDefs1125";
val () = export_theory_no_docs ();
