open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0745Theory;
val () = new_theory "vfmTest0745";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0745") $ get_result_defs "vfmTestDefs0745";
val () = export_theory_no_docs ();
