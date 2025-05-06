open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0160Theory;
val () = new_theory "vfmTest0160";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0160") $ get_result_defs "vfmTestDefs0160";
val () = export_theory_no_docs ();
