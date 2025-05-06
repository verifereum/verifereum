open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0582Theory;
val () = new_theory "vfmTest0582";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0582") $ get_result_defs "vfmTestDefs0582";
val () = export_theory_no_docs ();
