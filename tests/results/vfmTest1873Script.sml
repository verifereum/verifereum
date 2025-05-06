open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1873Theory;
val () = new_theory "vfmTest1873";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1873") $ get_result_defs "vfmTestDefs1873";
val () = export_theory_no_docs ();
