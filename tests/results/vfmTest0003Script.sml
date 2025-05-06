open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0003Theory;
val () = new_theory "vfmTest0003";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0003") $ get_result_defs "vfmTestDefs0003";
val () = export_theory_no_docs ();
