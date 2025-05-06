open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1728Theory;
val () = new_theory "vfmTest1728";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1728") $ get_result_defs "vfmTestDefs1728";
val () = export_theory_no_docs ();
