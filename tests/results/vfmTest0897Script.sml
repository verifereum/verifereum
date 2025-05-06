open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0897Theory;
val () = new_theory "vfmTest0897";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0897") $ get_result_defs "vfmTestDefs0897";
val () = export_theory_no_docs ();
