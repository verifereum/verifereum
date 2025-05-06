open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0356Theory;
val () = new_theory "vfmTest0356";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0356") $ get_result_defs "vfmTestDefs0356";
val () = export_theory_no_docs ();
