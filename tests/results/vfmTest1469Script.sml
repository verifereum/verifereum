open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1469Theory;
val () = new_theory "vfmTest1469";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1469") $ get_result_defs "vfmTestDefs1469";
val () = export_theory_no_docs ();
