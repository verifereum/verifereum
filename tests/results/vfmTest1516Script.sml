open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1516Theory;
val () = new_theory "vfmTest1516";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1516") $ get_result_defs "vfmTestDefs1516";
val () = export_theory_no_docs ();
