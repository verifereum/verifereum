open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1280Theory;
val () = new_theory "vfmTest1280";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1280") $ get_result_defs "vfmTestDefs1280";
val () = export_theory_no_docs ();
