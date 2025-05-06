open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0360Theory;
val () = new_theory "vfmTest0360";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0360") $ get_result_defs "vfmTestDefs0360";
val () = export_theory_no_docs ();
