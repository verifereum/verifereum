open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1583Theory;
val () = new_theory "vfmTest1583";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1583") $ get_result_defs "vfmTestDefs1583";
val () = export_theory_no_docs ();
