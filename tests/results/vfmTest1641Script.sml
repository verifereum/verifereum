open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1641Theory;
val () = new_theory "vfmTest1641";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1641") $ get_result_defs "vfmTestDefs1641";
val () = export_theory_no_docs ();
