open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0038Theory;
val () = new_theory "vfmTest0038";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0038") $ get_result_defs "vfmTestDefs0038";
val () = export_theory_no_docs ();
