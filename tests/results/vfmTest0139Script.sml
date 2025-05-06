open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0139Theory;
val () = new_theory "vfmTest0139";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0139") $ get_result_defs "vfmTestDefs0139";
val () = export_theory_no_docs ();
