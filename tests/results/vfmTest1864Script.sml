open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1864Theory;
val () = new_theory "vfmTest1864";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1864") $ get_result_defs "vfmTestDefs1864";
val () = export_theory_no_docs ();
