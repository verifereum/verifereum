open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1794Theory;
val () = new_theory "vfmTest1794";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1794") $ get_result_defs "vfmTestDefs1794";
val () = export_theory_no_docs ();
