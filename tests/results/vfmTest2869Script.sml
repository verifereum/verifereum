Theory vfmTest2869[no_sig_docs]
Ancestors vfmTestDefs2869
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2869_0.nsv", "result2869_1.nsv"];
val thyn = "vfmTestDefs2869";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
