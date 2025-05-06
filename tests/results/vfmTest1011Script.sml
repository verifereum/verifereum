open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1011Theory;
val () = new_theory "vfmTest1011";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1011") $ get_result_defs "vfmTestDefs1011";
val () = export_theory_no_docs ();
