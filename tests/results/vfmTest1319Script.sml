open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1319Theory;
val () = new_theory "vfmTest1319";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1319") $ get_result_defs "vfmTestDefs1319";
val () = export_theory_no_docs ();
