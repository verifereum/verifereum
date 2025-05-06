open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1268Theory;
val () = new_theory "vfmTest1268";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1268") $ get_result_defs "vfmTestDefs1268";
val () = export_theory_no_docs ();
