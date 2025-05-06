open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1150Theory;
val () = new_theory "vfmTest1150";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1150") $ get_result_defs "vfmTestDefs1150";
val () = export_theory_no_docs ();
