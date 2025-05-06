open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0433Theory;
val () = new_theory "vfmTest0433";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0433") $ get_result_defs "vfmTestDefs0433";
val () = export_theory_no_docs ();
