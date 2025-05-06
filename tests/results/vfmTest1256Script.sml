open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1256Theory;
val () = new_theory "vfmTest1256";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1256") $ get_result_defs "vfmTestDefs1256";
val () = export_theory_no_docs ();
