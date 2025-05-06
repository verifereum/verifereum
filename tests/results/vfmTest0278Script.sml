open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0278Theory;
val () = new_theory "vfmTest0278";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0278") $ get_result_defs "vfmTestDefs0278";
val () = export_theory_no_docs ();
