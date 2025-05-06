open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0613Theory;
val () = new_theory "vfmTest0613";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0613") $ get_result_defs "vfmTestDefs0613";
val () = export_theory_no_docs ();
