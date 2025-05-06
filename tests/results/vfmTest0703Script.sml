open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0703Theory;
val () = new_theory "vfmTest0703";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0703") $ get_result_defs "vfmTestDefs0703";
val () = export_theory_no_docs ();
