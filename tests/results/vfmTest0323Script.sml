open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0323Theory;
val () = new_theory "vfmTest0323";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0323") $ get_result_defs "vfmTestDefs0323";
val () = export_theory_no_docs ();
