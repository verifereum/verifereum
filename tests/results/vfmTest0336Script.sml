open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0336Theory;
val () = new_theory "vfmTest0336";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0336") $ get_result_defs "vfmTestDefs0336";
val () = export_theory_no_docs ();
