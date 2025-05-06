open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0352Theory;
val () = new_theory "vfmTest0352";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0352") $ get_result_defs "vfmTestDefs0352";
val () = export_theory_no_docs ();
