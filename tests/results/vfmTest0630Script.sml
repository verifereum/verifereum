open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0630Theory;
val () = new_theory "vfmTest0630";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0630") $ get_result_defs "vfmTestDefs0630";
val () = export_theory_no_docs ();
