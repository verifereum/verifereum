open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0971Theory;
val () = new_theory "vfmTest0971";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0971") $ get_result_defs "vfmTestDefs0971";
val () = export_theory_no_docs ();
