open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0467Theory;
val () = new_theory "vfmTest0467";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0467") $ get_result_defs "vfmTestDefs0467";
val () = export_theory_no_docs ();
