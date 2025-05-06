open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1536Theory;
val () = new_theory "vfmTest1536";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1536") $ get_result_defs "vfmTestDefs1536";
val () = export_theory_no_docs ();
