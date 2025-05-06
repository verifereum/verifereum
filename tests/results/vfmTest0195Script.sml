open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0195Theory;
val () = new_theory "vfmTest0195";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0195") $ get_result_defs "vfmTestDefs0195";
val () = export_theory_no_docs ();
