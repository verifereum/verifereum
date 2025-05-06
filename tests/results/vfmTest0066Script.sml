open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0066Theory;
val () = new_theory "vfmTest0066";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0066") $ get_result_defs "vfmTestDefs0066";
val () = export_theory_no_docs ();
