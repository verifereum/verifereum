open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0869Theory;
val () = new_theory "vfmTest0869";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0869") $ get_result_defs "vfmTestDefs0869";
val () = export_theory_no_docs ();
