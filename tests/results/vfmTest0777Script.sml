open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0777Theory;
val () = new_theory "vfmTest0777";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0777") $ get_result_defs "vfmTestDefs0777";
val () = export_theory_no_docs ();
