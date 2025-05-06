open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0555Theory;
val () = new_theory "vfmTest0555";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0555") $ get_result_defs "vfmTestDefs0555";
val () = export_theory_no_docs ();
