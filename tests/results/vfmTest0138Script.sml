open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0138Theory;
val () = new_theory "vfmTest0138";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0138") $ get_result_defs "vfmTestDefs0138";
val () = export_theory_no_docs ();
