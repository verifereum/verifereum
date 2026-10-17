Theory vfmTest2447[no_sig_docs]
Ancestors vfmTestDefs2447
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2447_0.nsv", "result2447_1.nsv", "result2447_2.nsv", "result2447_3.nsv", "result2447_4.nsv", "result2447_5.nsv", "result2447_6.nsv", "result2447_7.nsv"];
val thyn = "vfmTestDefs2447";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
