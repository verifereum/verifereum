open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1831Theory;
val () = new_theory "vfmTest1831";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1831") $ get_result_defs "vfmTestDefs1831";
val () = export_theory_no_docs ();
