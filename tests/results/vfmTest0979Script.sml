open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0979Theory;
val () = new_theory "vfmTest0979";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0979") $ get_result_defs "vfmTestDefs0979";
val () = export_theory_no_docs ();
