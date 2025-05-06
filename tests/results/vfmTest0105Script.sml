open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0105Theory;
val () = new_theory "vfmTest0105";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0105") $ get_result_defs "vfmTestDefs0105";
val () = export_theory_no_docs ();
