open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1072Theory;
val () = new_theory "vfmTest1072";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1072") $ get_result_defs "vfmTestDefs1072";
val () = export_theory_no_docs ();
