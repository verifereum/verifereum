open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2875Theory;
val () = new_theory "vfmTest2875";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2875") $ get_result_defs "vfmTestDefs2875";
val () = export_theory_no_docs ();
