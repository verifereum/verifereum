open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0015Theory;
val () = new_theory "vfmTest0015";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0015") $ get_result_defs "vfmTestDefs0015";
val () = export_theory_no_docs ();
