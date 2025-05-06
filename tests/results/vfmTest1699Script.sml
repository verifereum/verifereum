open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1699Theory;
val () = new_theory "vfmTest1699";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1699") $ get_result_defs "vfmTestDefs1699";
val () = export_theory_no_docs ();
