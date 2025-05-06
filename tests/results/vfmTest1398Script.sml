open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1398Theory;
val () = new_theory "vfmTest1398";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1398") $ get_result_defs "vfmTestDefs1398";
val () = export_theory_no_docs ();
