open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1690Theory;
val () = new_theory "vfmTest1690";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1690") $ get_result_defs "vfmTestDefs1690";
val () = export_theory_no_docs ();
