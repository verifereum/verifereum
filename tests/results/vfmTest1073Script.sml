open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1073Theory;
val () = new_theory "vfmTest1073";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1073") $ get_result_defs "vfmTestDefs1073";
val () = export_theory_no_docs ();
