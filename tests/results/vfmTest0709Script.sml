open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0709Theory;
val () = new_theory "vfmTest0709";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0709") $ get_result_defs "vfmTestDefs0709";
val () = export_theory_no_docs ();
