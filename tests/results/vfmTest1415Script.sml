open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1415Theory;
val () = new_theory "vfmTest1415";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1415") $ get_result_defs "vfmTestDefs1415";
val () = export_theory_no_docs ();
