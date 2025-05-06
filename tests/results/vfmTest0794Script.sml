open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0794Theory;
val () = new_theory "vfmTest0794";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0794") $ get_result_defs "vfmTestDefs0794";
val () = export_theory_no_docs ();
