open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1777Theory;
val () = new_theory "vfmTest1777";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1777") $ get_result_defs "vfmTestDefs1777";
val () = export_theory_no_docs ();
