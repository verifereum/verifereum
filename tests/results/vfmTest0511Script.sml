open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0511Theory;
val () = new_theory "vfmTest0511";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0511") $ get_result_defs "vfmTestDefs0511";
val () = export_theory_no_docs ();
