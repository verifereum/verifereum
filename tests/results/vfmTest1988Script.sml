open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1988Theory;
val () = new_theory "vfmTest1988";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1988") $ get_result_defs "vfmTestDefs1988";
val () = export_theory_no_docs ();
