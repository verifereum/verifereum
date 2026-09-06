Theory vfmTest2392[no_sig_docs]
Ancestors vfmTestDefs2392
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2392_0.nsv", "result2392_1.nsv", "result2392_2.nsv", "result2392_3.nsv", "result2392_4.nsv", "result2392_5.nsv", "result2392_6.nsv", "result2392_7.nsv"];
val thyn = "vfmTestDefs2392";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
