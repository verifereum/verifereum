open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1153Theory;
val () = new_theory "vfmTest1153";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1153") $ get_result_defs "vfmTestDefs1153";
val () = export_theory_no_docs ();
