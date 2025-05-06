open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0970Theory;
val () = new_theory "vfmTest0970";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0970") $ get_result_defs "vfmTestDefs0970";
val () = export_theory_no_docs ();
