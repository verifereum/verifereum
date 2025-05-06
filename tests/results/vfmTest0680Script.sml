open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0680Theory;
val () = new_theory "vfmTest0680";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0680") $ get_result_defs "vfmTestDefs0680";
val () = export_theory_no_docs ();
