open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0430Theory;
val () = new_theory "vfmTest0430";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0430") $ get_result_defs "vfmTestDefs0430";
val () = export_theory_no_docs ();
