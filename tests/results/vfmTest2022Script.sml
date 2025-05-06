open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2022Theory;
val () = new_theory "vfmTest2022";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2022") $ get_result_defs "vfmTestDefs2022";
val () = export_theory_no_docs ();
