open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1939Theory;
val () = new_theory "vfmTest1939";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1939") $ get_result_defs "vfmTestDefs1939";
val () = export_theory_no_docs ();
