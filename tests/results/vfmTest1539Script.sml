open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1539Theory;
val () = new_theory "vfmTest1539";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1539") $ get_result_defs "vfmTestDefs1539";
val () = export_theory_no_docs ();
