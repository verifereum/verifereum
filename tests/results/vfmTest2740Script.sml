Theory vfmTest2740[no_sig_docs]
Ancestors vfmTestDefs2740
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2740_0.nsv", "result2740_1.nsv", "result2740_2.nsv", "result2740_3.nsv"];
val thyn = "vfmTestDefs2740";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
