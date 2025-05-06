open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1260Theory;
val () = new_theory "vfmTest1260";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1260") $ get_result_defs "vfmTestDefs1260";
val () = export_theory_no_docs ();
