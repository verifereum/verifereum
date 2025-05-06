open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1207Theory;
val () = new_theory "vfmTest1207";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1207") $ get_result_defs "vfmTestDefs1207";
val () = export_theory_no_docs ();
