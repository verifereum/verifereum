open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1501Theory;
val () = new_theory "vfmTest1501";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1501") $ get_result_defs "vfmTestDefs1501";
val () = export_theory_no_docs ();
