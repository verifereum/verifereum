open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1883Theory;
val () = new_theory "vfmTest1883";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1883") $ get_result_defs "vfmTestDefs1883";
val () = export_theory_no_docs ();
