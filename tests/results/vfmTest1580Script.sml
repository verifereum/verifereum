open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1580Theory;
val () = new_theory "vfmTest1580";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1580") $ get_result_defs "vfmTestDefs1580";
val () = export_theory_no_docs ();
