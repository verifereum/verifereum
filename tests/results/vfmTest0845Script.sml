open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0845Theory;
val () = new_theory "vfmTest0845";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0845") $ get_result_defs "vfmTestDefs0845";
val () = export_theory_no_docs ();
