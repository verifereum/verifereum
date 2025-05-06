open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0435Theory;
val () = new_theory "vfmTest0435";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0435") $ get_result_defs "vfmTestDefs0435";
val () = export_theory_no_docs ();
