open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0330Theory;
val () = new_theory "vfmTest0330";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0330") $ get_result_defs "vfmTestDefs0330";
val () = export_theory_no_docs ();
