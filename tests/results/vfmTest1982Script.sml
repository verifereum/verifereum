open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1982Theory;
val () = new_theory "vfmTest1982";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1982") $ get_result_defs "vfmTestDefs1982";
val () = export_theory_no_docs ();
