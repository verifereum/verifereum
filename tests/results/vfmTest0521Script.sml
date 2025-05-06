open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0521Theory;
val () = new_theory "vfmTest0521";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0521") $ get_result_defs "vfmTestDefs0521";
val () = export_theory_no_docs ();
