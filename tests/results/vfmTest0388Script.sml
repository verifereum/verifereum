open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0388Theory;
val () = new_theory "vfmTest0388";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0388") $ get_result_defs "vfmTestDefs0388";
val () = export_theory_no_docs ();
