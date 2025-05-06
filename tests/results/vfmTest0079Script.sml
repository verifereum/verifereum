open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0079Theory;
val () = new_theory "vfmTest0079";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0079") $ get_result_defs "vfmTestDefs0079";
val () = export_theory_no_docs ();
