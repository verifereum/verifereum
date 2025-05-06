open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1933Theory;
val () = new_theory "vfmTest1933";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1933") $ get_result_defs "vfmTestDefs1933";
val () = export_theory_no_docs ();
