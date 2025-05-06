open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1881Theory;
val () = new_theory "vfmTest1881";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1881") $ get_result_defs "vfmTestDefs1881";
val () = export_theory_no_docs ();
