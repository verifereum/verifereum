open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1024Theory;
val () = new_theory "vfmTest1024";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1024") $ get_result_defs "vfmTestDefs1024";
val () = export_theory_no_docs ();
