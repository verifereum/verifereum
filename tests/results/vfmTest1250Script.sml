open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1250Theory;
val () = new_theory "vfmTest1250";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1250") $ get_result_defs "vfmTestDefs1250";
val () = export_theory_no_docs ();
