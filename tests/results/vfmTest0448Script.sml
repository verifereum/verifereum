open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0448Theory;
val () = new_theory "vfmTest0448";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0448") $ get_result_defs "vfmTestDefs0448";
val () = export_theory_no_docs ();
