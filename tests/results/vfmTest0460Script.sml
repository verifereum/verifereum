Theory vfmTest0460[no_sig_docs]
Ancestors vfmTestDefs0460
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0460_0.nsv", "result0460_1.nsv"];
val thyn = "vfmTestDefs0460";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
