open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0944Theory;
val () = new_theory "vfmTest0944";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0944") $ get_result_defs "vfmTestDefs0944";
val () = export_theory_no_docs ();
