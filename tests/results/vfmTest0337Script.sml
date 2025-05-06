open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0337Theory;
val () = new_theory "vfmTest0337";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0337") $ get_result_defs "vfmTestDefs0337";
val () = export_theory_no_docs ();
