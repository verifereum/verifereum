open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2024Theory;
val () = new_theory "vfmTest2024";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2024") $ get_result_defs "vfmTestDefs2024";
val () = export_theory_no_docs ();
