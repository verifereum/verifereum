open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1508Theory;
val () = new_theory "vfmTest1508";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1508") $ get_result_defs "vfmTestDefs1508";
val () = export_theory_no_docs ();
