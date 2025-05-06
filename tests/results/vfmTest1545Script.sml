open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1545Theory;
val () = new_theory "vfmTest1545";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1545") $ get_result_defs "vfmTestDefs1545";
val () = export_theory_no_docs ();
