open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0384Theory;
val () = new_theory "vfmTest0384";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0384") $ get_result_defs "vfmTestDefs0384";
val () = export_theory_no_docs ();
