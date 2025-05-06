open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0156Theory;
val () = new_theory "vfmTest0156";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0156") $ get_result_defs "vfmTestDefs0156";
val () = export_theory_no_docs ();
