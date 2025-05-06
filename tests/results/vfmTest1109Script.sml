open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1109Theory;
val () = new_theory "vfmTest1109";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1109") $ get_result_defs "vfmTestDefs1109";
val () = export_theory_no_docs ();
