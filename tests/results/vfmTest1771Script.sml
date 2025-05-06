open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1771Theory;
val () = new_theory "vfmTest1771";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1771") $ get_result_defs "vfmTestDefs1771";
val () = export_theory_no_docs ();
