open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0251Theory;
val () = new_theory "vfmTest0251";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0251") $ get_result_defs "vfmTestDefs0251";
val () = export_theory_no_docs ();
