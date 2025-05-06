open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1920Theory;
val () = new_theory "vfmTest1920";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1920") $ get_result_defs "vfmTestDefs1920";
val () = export_theory_no_docs ();
