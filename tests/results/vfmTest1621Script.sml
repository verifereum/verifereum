open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1621Theory;
val () = new_theory "vfmTest1621";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1621") $ get_result_defs "vfmTestDefs1621";
val () = export_theory_no_docs ();
