open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0311Theory;
val () = new_theory "vfmTest0311";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0311") $ get_result_defs "vfmTestDefs0311";
val () = export_theory_no_docs ();
