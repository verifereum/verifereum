open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0899Theory;
val () = new_theory "vfmTest0899";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0899") $ get_result_defs "vfmTestDefs0899";
val () = export_theory_no_docs ();
