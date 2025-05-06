open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1008Theory;
val () = new_theory "vfmTest1008";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1008") $ get_result_defs "vfmTestDefs1008";
val () = export_theory_no_docs ();
