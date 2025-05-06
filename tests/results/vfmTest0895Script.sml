open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0895Theory;
val () = new_theory "vfmTest0895";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0895") $ get_result_defs "vfmTestDefs0895";
val () = export_theory_no_docs ();
