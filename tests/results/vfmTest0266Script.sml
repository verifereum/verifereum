open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0266Theory;
val () = new_theory "vfmTest0266";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0266") $ get_result_defs "vfmTestDefs0266";
val () = export_theory_no_docs ();
