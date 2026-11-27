Theory vfmTest2211[no_sig_docs]
Ancestors vfmTestDefs2211
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2211_0.nsv", "result2211_1.nsv", "result2211_2.nsv", "result2211_3.nsv", "result2211_4.nsv", "result2211_5.nsv", "result2211_6.nsv", "result2211_7.nsv", "result2211_8.nsv", "result2211_9.nsv", "result2211_10.nsv", "result2211_11.nsv", "result2211_12.nsv", "result2211_13.nsv", "result2211_14.nsv", "result2211_15.nsv", "result2211_16.nsv", "result2211_17.nsv", "result2211_18.nsv", "result2211_19.nsv", "result2211_20.nsv", "result2211_21.nsv", "result2211_22.nsv", "result2211_23.nsv"];
val thyn = "vfmTestDefs2211";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
