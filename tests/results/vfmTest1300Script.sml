open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1300Theory;
val () = new_theory "vfmTest1300";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1300") $ get_result_defs "vfmTestDefs1300";
val () = export_theory_no_docs ();
