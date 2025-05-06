open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2891Theory;
val () = new_theory "vfmTest2891";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2891") $ get_result_defs "vfmTestDefs2891";
val () = export_theory_no_docs ();
