open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0457Theory;
val () = new_theory "vfmTest0457";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0457") $ get_result_defs "vfmTestDefs0457";
val () = export_theory_no_docs ();
