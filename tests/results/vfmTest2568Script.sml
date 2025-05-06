open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2568Theory;
val () = new_theory "vfmTest2568";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2568") $ get_result_defs "vfmTestDefs2568";
val () = export_theory_no_docs ();
