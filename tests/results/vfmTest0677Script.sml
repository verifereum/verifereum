open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0677Theory;
val () = new_theory "vfmTest0677";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0677") $ get_result_defs "vfmTestDefs0677";
val () = export_theory_no_docs ();
