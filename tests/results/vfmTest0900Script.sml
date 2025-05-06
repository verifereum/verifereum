open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0900Theory;
val () = new_theory "vfmTest0900";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0900") $ get_result_defs "vfmTestDefs0900";
val () = export_theory_no_docs ();
