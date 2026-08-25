Theory vfmTest0930[no_sig_docs]
Ancestors vfmTestDefs0930
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0930_0.nsv"];
val thyn = "vfmTestDefs0930";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
