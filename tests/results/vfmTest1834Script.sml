open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1834Theory;
val () = new_theory "vfmTest1834";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1834") $ get_result_defs "vfmTestDefs1834";
val () = export_theory_no_docs ();
