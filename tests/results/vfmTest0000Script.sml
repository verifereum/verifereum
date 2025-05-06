open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0000Theory;
val () = new_theory "vfmTest0000";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0000") $ get_result_defs "vfmTestDefs0000";
val () = export_theory_no_docs ();
