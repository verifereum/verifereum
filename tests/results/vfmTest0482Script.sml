open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0482Theory;
val () = new_theory "vfmTest0482";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0482") $ get_result_defs "vfmTestDefs0482";
val () = export_theory_no_docs ();
