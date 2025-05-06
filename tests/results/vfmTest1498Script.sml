open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1498Theory;
val () = new_theory "vfmTest1498";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1498") $ get_result_defs "vfmTestDefs1498";
val () = export_theory_no_docs ();
