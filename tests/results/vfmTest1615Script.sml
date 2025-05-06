open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1615Theory;
val () = new_theory "vfmTest1615";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1615") $ get_result_defs "vfmTestDefs1615";
val () = export_theory_no_docs ();
