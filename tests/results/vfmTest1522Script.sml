open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1522Theory;
val () = new_theory "vfmTest1522";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1522") $ get_result_defs "vfmTestDefs1522";
val () = export_theory_no_docs ();
