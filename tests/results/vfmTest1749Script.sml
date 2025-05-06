open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1749Theory;
val () = new_theory "vfmTest1749";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1749") $ get_result_defs "vfmTestDefs1749";
val () = export_theory_no_docs ();
