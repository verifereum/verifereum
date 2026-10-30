Theory vfmTest1443[no_sig_docs]
Ancestors vfmTestDefs1443
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1443_0.nsv", "result1443_1.nsv", "result1443_2.nsv", "result1443_3.nsv", "result1443_4.nsv", "result1443_5.nsv", "result1443_6.nsv", "result1443_7.nsv", "result1443_8.nsv", "result1443_9.nsv", "result1443_10.nsv", "result1443_11.nsv", "result1443_12.nsv", "result1443_13.nsv", "result1443_14.nsv", "result1443_15.nsv"];
val thyn = "vfmTestDefs1443";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
