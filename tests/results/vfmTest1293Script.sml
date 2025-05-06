open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1293Theory;
val () = new_theory "vfmTest1293";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1293") $ get_result_defs "vfmTestDefs1293";
val () = export_theory_no_docs ();
