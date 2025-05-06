open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1151Theory;
val () = new_theory "vfmTest1151";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1151") $ get_result_defs "vfmTestDefs1151";
val () = export_theory_no_docs ();
