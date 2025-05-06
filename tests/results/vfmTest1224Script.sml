open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1224Theory;
val () = new_theory "vfmTest1224";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1224") $ get_result_defs "vfmTestDefs1224";
val () = export_theory_no_docs ();
