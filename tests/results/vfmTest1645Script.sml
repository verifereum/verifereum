open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1645Theory;
val () = new_theory "vfmTest1645";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1645") $ get_result_defs "vfmTestDefs1645";
val () = export_theory_no_docs ();
