open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0733Theory;
val () = new_theory "vfmTest0733";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0733") $ get_result_defs "vfmTestDefs0733";
val () = export_theory_no_docs ();
