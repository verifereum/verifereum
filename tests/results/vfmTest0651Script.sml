open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0651Theory;
val () = new_theory "vfmTest0651";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0651") $ get_result_defs "vfmTestDefs0651";
val () = export_theory_no_docs ();
