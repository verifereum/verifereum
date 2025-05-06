open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1481Theory;
val () = new_theory "vfmTest1481";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1481") $ get_result_defs "vfmTestDefs1481";
val () = export_theory_no_docs ();
