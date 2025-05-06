open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0988Theory;
val () = new_theory "vfmTest0988";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0988") $ get_result_defs "vfmTestDefs0988";
val () = export_theory_no_docs ();
