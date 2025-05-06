open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1721Theory;
val () = new_theory "vfmTest1721";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1721") $ get_result_defs "vfmTestDefs1721";
val () = export_theory_no_docs ();
