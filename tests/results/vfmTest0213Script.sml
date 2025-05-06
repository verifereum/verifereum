open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0213Theory;
val () = new_theory "vfmTest0213";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0213") $ get_result_defs "vfmTestDefs0213";
val () = export_theory_no_docs ();
