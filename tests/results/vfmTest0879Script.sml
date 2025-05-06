open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0879Theory;
val () = new_theory "vfmTest0879";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0879") $ get_result_defs "vfmTestDefs0879";
val () = export_theory_no_docs ();
