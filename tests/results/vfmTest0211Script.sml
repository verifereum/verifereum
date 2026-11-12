Theory vfmTest0211[no_sig_docs]
Ancestors vfmTestDefs0211
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0211_0.nsv", "result0211_1.nsv", "result0211_2.nsv", "result0211_3.nsv", "result0211_4.nsv", "result0211_5.nsv", "result0211_6.nsv", "result0211_7.nsv", "result0211_8.nsv", "result0211_9.nsv", "result0211_10.nsv", "result0211_11.nsv", "result0211_12.nsv", "result0211_13.nsv", "result0211_14.nsv", "result0211_15.nsv", "result0211_16.nsv", "result0211_17.nsv", "result0211_18.nsv", "result0211_19.nsv", "result0211_20.nsv", "result0211_21.nsv", "result0211_22.nsv", "result0211_23.nsv", "result0211_24.nsv", "result0211_25.nsv", "result0211_26.nsv", "result0211_27.nsv", "result0211_28.nsv", "result0211_29.nsv"];
val thyn = "vfmTestDefs0211";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
