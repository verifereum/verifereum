open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1788Theory;
val () = new_theory "vfmTest1788";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1788") $ get_result_defs "vfmTestDefs1788";
val () = export_theory_no_docs ();
