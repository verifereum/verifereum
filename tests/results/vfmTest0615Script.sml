open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0615Theory;
val () = new_theory "vfmTest0615";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0615") $ get_result_defs "vfmTestDefs0615";
val () = export_theory_no_docs ();
