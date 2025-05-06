open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1411Theory;
val () = new_theory "vfmTest1411";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1411") $ get_result_defs "vfmTestDefs1411";
val () = export_theory_no_docs ();
