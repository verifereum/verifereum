open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1372Theory;
val () = new_theory "vfmTest1372";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1372") $ get_result_defs "vfmTestDefs1372";
val () = export_theory_no_docs ();
