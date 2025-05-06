open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1629Theory;
val () = new_theory "vfmTest1629";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1629") $ get_result_defs "vfmTestDefs1629";
val () = export_theory_no_docs ();
