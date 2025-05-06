open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0878Theory;
val () = new_theory "vfmTest0878";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0878") $ get_result_defs "vfmTestDefs0878";
val () = export_theory_no_docs ();
