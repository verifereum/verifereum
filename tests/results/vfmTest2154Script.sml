Theory vfmTest2154[no_sig_docs]
Ancestors vfmTestDefs2154
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2154_0.nsv", "result2154_1.nsv", "result2154_2.nsv", "result2154_3.nsv", "result2154_4.nsv", "result2154_5.nsv", "result2154_6.nsv", "result2154_7.nsv", "result2154_8.nsv", "result2154_9.nsv", "result2154_10.nsv", "result2154_11.nsv", "result2154_12.nsv", "result2154_13.nsv", "result2154_14.nsv", "result2154_15.nsv", "result2154_16.nsv", "result2154_17.nsv", "result2154_18.nsv"];
val thyn = "vfmTestDefs2154";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
