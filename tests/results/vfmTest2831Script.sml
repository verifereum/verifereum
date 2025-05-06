open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2831Theory;
val () = new_theory "vfmTest2831";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2831") $ get_result_defs "vfmTestDefs2831";
val () = export_theory_no_docs ();
