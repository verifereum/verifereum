open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0539Theory;
val () = new_theory "vfmTest0539";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0539") $ get_result_defs "vfmTestDefs0539";
val () = export_theory_no_docs ();
