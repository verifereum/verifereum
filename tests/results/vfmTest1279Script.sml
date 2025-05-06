open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1279Theory;
val () = new_theory "vfmTest1279";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1279") $ get_result_defs "vfmTestDefs1279";
val () = export_theory_no_docs ();
