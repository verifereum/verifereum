open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1764Theory;
val () = new_theory "vfmTest1764";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1764") $ get_result_defs "vfmTestDefs1764";
val () = export_theory_no_docs ();
