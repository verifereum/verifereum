open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2639Theory;
val () = new_theory "vfmTest2639";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2639") $ get_result_defs "vfmTestDefs2639";
val () = export_theory_no_docs ();
