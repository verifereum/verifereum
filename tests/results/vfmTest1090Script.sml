open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1090Theory;
val () = new_theory "vfmTest1090";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1090") $ get_result_defs "vfmTestDefs1090";
val () = export_theory_no_docs ();
