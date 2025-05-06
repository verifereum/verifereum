open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0587Theory;
val () = new_theory "vfmTest0587";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0587") $ get_result_defs "vfmTestDefs0587";
val () = export_theory_no_docs ();
