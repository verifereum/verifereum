open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0887Theory;
val () = new_theory "vfmTest0887";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0887") $ get_result_defs "vfmTestDefs0887";
val () = export_theory_no_docs ();
