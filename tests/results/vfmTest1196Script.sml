open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1196Theory;
val () = new_theory "vfmTest1196";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1196") $ get_result_defs "vfmTestDefs1196";
val () = export_theory_no_docs ();
