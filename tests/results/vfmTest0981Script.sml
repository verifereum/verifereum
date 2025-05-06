open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0981Theory;
val () = new_theory "vfmTest0981";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0981") $ get_result_defs "vfmTestDefs0981";
val () = export_theory_no_docs ();
