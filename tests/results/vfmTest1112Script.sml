open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1112Theory;
val () = new_theory "vfmTest1112";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1112") $ get_result_defs "vfmTestDefs1112";
val () = export_theory_no_docs ();
