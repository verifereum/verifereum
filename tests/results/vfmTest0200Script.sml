open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0200Theory;
val () = new_theory "vfmTest0200";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0200") $ get_result_defs "vfmTestDefs0200";
val () = export_theory_no_docs ();
