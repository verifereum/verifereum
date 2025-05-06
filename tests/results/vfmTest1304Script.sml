open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1304Theory;
val () = new_theory "vfmTest1304";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1304") $ get_result_defs "vfmTestDefs1304";
val () = export_theory_no_docs ();
