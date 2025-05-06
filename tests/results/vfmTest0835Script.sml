open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0835Theory;
val () = new_theory "vfmTest0835";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0835") $ get_result_defs "vfmTestDefs0835";
val () = export_theory_no_docs ();
