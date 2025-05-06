open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0568Theory;
val () = new_theory "vfmTest0568";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0568") $ get_result_defs "vfmTestDefs0568";
val () = export_theory_no_docs ();
