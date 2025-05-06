open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1601Theory;
val () = new_theory "vfmTest1601";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1601") $ get_result_defs "vfmTestDefs1601";
val () = export_theory_no_docs ();
