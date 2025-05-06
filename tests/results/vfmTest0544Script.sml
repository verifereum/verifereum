open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0544Theory;
val () = new_theory "vfmTest0544";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0544") $ get_result_defs "vfmTestDefs0544";
val () = export_theory_no_docs ();
