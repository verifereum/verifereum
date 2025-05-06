open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0942Theory;
val () = new_theory "vfmTest0942";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0942") $ get_result_defs "vfmTestDefs0942";
val () = export_theory_no_docs ();
