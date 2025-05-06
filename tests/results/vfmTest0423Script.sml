open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0423Theory;
val () = new_theory "vfmTest0423";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0423") $ get_result_defs "vfmTestDefs0423";
val () = export_theory_no_docs ();
