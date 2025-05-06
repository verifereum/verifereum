open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0385Theory;
val () = new_theory "vfmTest0385";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0385") $ get_result_defs "vfmTestDefs0385";
val () = export_theory_no_docs ();
