open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1051Theory;
val () = new_theory "vfmTest1051";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1051") $ get_result_defs "vfmTestDefs1051";
val () = export_theory_no_docs ();
