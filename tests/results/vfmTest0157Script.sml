open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0157Theory;
val () = new_theory "vfmTest0157";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0157") $ get_result_defs "vfmTestDefs0157";
val () = export_theory_no_docs ();
