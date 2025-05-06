open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2910Theory;
val () = new_theory "vfmTest2910";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2910") $ get_result_defs "vfmTestDefs2910";
val () = export_theory_no_docs ();
