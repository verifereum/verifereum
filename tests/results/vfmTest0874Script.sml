Theory vfmTest0874[no_sig_docs]
Ancestors vfmTestDefs0874
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0874_0.nsv", "result0874_1.nsv"];
val thyn = "vfmTestDefs0874";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
