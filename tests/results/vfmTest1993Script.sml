open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1993Theory;
val () = new_theory "vfmTest1993";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1993") $ get_result_defs "vfmTestDefs1993";
val () = export_theory_no_docs ();
