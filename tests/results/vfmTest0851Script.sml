open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0851Theory;
val () = new_theory "vfmTest0851";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0851") $ get_result_defs "vfmTestDefs0851";
val () = export_theory_no_docs ();
