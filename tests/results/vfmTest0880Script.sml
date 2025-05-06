open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0880Theory;
val () = new_theory "vfmTest0880";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0880") $ get_result_defs "vfmTestDefs0880";
val () = export_theory_no_docs ();
