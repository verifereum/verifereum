open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1910Theory;
val () = new_theory "vfmTest1910";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1910") $ get_result_defs "vfmTestDefs1910";
val () = export_theory_no_docs ();
