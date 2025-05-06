open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0894Theory;
val () = new_theory "vfmTest0894";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0894") $ get_result_defs "vfmTestDefs0894";
val () = export_theory_no_docs ();
