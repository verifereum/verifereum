open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1113Theory;
val () = new_theory "vfmTest1113";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1113") $ get_result_defs "vfmTestDefs1113";
val () = export_theory_no_docs ();
