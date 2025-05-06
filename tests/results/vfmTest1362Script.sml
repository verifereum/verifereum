open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1362Theory;
val () = new_theory "vfmTest1362";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1362") $ get_result_defs "vfmTestDefs1362";
val () = export_theory_no_docs ();
