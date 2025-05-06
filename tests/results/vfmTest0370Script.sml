open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0370Theory;
val () = new_theory "vfmTest0370";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0370") $ get_result_defs "vfmTestDefs0370";
val () = export_theory_no_docs ();
