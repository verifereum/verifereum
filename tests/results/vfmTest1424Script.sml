open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1424Theory;
val () = new_theory "vfmTest1424";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1424") $ get_result_defs "vfmTestDefs1424";
val () = export_theory_no_docs ();
