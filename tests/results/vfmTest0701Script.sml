open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0701Theory;
val () = new_theory "vfmTest0701";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0701") $ get_result_defs "vfmTestDefs0701";
val () = export_theory_no_docs ();
