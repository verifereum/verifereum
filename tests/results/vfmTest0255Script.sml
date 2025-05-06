open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0255Theory;
val () = new_theory "vfmTest0255";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0255") $ get_result_defs "vfmTestDefs0255";
val () = export_theory_no_docs ();
