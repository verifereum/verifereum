open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1682Theory;
val () = new_theory "vfmTest1682";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1682") $ get_result_defs "vfmTestDefs1682";
val () = export_theory_no_docs ();
