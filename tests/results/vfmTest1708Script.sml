open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1708Theory;
val () = new_theory "vfmTest1708";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1708") $ get_result_defs "vfmTestDefs1708";
val () = export_theory_no_docs ();
