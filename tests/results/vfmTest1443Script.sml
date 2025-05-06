open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1443Theory;
val () = new_theory "vfmTest1443";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1443") $ get_result_defs "vfmTestDefs1443";
val () = export_theory_no_docs ();
