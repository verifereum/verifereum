open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0396Theory;
val () = new_theory "vfmTest0396";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0396") $ get_result_defs "vfmTestDefs0396";
val () = export_theory_no_docs ();
