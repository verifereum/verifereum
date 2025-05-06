open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1147Theory;
val () = new_theory "vfmTest1147";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1147") $ get_result_defs "vfmTestDefs1147";
val () = export_theory_no_docs ();
