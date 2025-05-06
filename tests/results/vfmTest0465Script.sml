open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0465Theory;
val () = new_theory "vfmTest0465";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0465") $ get_result_defs "vfmTestDefs0465";
val () = export_theory_no_docs ();
