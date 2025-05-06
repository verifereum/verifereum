open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0491Theory;
val () = new_theory "vfmTest0491";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0491") $ get_result_defs "vfmTestDefs0491";
val () = export_theory_no_docs ();
