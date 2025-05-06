open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1391Theory;
val () = new_theory "vfmTest1391";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1391") $ get_result_defs "vfmTestDefs1391";
val () = export_theory_no_docs ();
