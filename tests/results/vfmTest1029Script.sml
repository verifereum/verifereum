open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1029Theory;
val () = new_theory "vfmTest1029";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1029") $ get_result_defs "vfmTestDefs1029";
val () = export_theory_no_docs ();
