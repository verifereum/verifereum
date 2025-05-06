open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1986Theory;
val () = new_theory "vfmTest1986";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1986") $ get_result_defs "vfmTestDefs1986";
val () = export_theory_no_docs ();
