open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0099Theory;
val () = new_theory "vfmTest0099";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0099") $ get_result_defs "vfmTestDefs0099";
val () = export_theory_no_docs ();
