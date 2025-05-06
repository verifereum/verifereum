open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0316Theory;
val () = new_theory "vfmTest0316";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0316") $ get_result_defs "vfmTestDefs0316";
val () = export_theory_no_docs ();
