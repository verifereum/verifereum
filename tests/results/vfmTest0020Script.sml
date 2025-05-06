open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0020Theory;
val () = new_theory "vfmTest0020";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0020") $ get_result_defs "vfmTestDefs0020";
val () = export_theory_no_docs ();
